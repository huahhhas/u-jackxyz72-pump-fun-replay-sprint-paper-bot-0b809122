// Sprint scalper for the pump.fun replay: a paper bot on agent-fun/replay/v2.
//
// Idea: pump.fun curves burst hard in their first minutes and then mostly bleed.
// This bot only buys a burst it can measure — several distinct buyers pushing net
// SOL in while the price climbs toward its recent high — and it never rides one
// coin for long: half comes off at +30%, the rest trails, a -15% stop cuts the
// losers, and nothing is held past 2000 slots. One small fixed stake per coin
// (0.12 SOL), no pyramiding, so a false start costs little and the five open
// position slots keep turning over: the guardrail needs at least 20 coins with
// a round trip of 0.01 SOL or more, and holding forever can never reach it.
//
// Deterministic by construction: no clock, no environment, no randomness; every
// decision is a pure function of the batches the harness has delivered, and all
// iteration is over insertion-ordered maps fed by that stream.

import { LAMPORTS_PER_SOL, runBot, type BotState, type BuyInput, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1e9;
const SOL = (n: number): bigint => BigInt(Math.round(n * LAMPORTS));

// --- tunables (SOL unless noted, slots are chain slots) ---
const ENTRY_WINDOW = 600; // slots of tape the entry signal looks back over
const MIN_AGE = 200; // slots since CreateEvent before an entry is allowed
const MIN_BUYS = 4; // buy trades inside the entry window
const MIN_BUYERS = 3; // distinct buying wallets inside the entry window
const MIN_NET_SOL = 0.5; // net SOL (buys minus sells) inside the entry window
const MIN_BUY_SELL = 1.2; // buy SOL must be at least this multiple of sell SOL
const MIN_RISE = 0.1; // price now over price at the window start, minus 1
const MAX_RISE = 0.6; // skip coins that already ran this far in one window
const NEAR_HIGH = 0.94; // price now at least this share of the window high
const MIN_RQ_SOL = 0.5; // real SOL reserves at entry, lower bound
const MAX_RQ_SOL = 100; // real SOL reserves at entry, upper bound
const STAKE_SOL = 0.12; // SOL spent on one entry
const BUY_SLIP_BPS = 1500;
const SELL_SLIP_BPS = 10_000;
const TAKE_PROFIT = 1.3; // sell half when close value reaches this of cost
const TRAIL_ARM = 1.1; // trailing stop arms once peak value reaches this of cost
const TRAIL_GIVEBACK = 0.85; // sell the rest when value falls to this of peak
const MAX_HOLD = 2000; // slots held before a forced exit
const COOLDOWN = 150; // slots to wait after an exit before re-entering a coin
const MAX_ENTRIES = 2; // most entries per coin over the run
const FADE_WINDOW = 300; // slots for the fade exit
const FADE_BUY_SELL = 0.4; // exit when buy SOL falls below this share of sell SOL and underwater
const PROBE_SOL = 0.02; // guardrail probe stake (above the 0.01 SOL round-trip bar)
const PROBE_PACE_SLOTS = 300_000; // pace denominator: 25 coins by this many slots
const PROBE_TARGET_COINS = 25;
const PROBE_MIN_ELAPSED = 60_000; // slots before probes may start

interface TapeTrade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  trades: TapeTrade[];
  entries: number;
  lastExit: number;
}

interface Held {
  entrySlot: number;
  peakValue: bigint; // best close value seen (lamports)
  tookHalf: boolean;
  exiting: boolean; // a sell for this mint is already in flight
}

// --- per-run stores ---
const tapes = new Map<Pubkey, Tape>();
const held = new Map<Pubkey, Held>();
const tradedCoins = new Set<Pubkey>();
const probeBuying = new Set<Pubkey>();
const probeSelling = new Set<Pubkey>();
let firstSlot: number | null = null;

function tapeOf(mint: Pubkey): Tape {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [], entries: 0, lastExit: -1e12 };
    tapes.set(mint, t);
  }
  return t;
}

const priceOf = (vq: bigint, vt: bigint): number =>
  vt === 0n ? 0 : Number(vq) / Number(vt);

/** Close value of `tokens` at the curve's latest reserves, in lamports. */
const closeValue = (tokens: bigint, vq: bigint, vt: bigint): bigint =>
  vt === 0n ? 0n : (tokens * vq) / vt;

/**
 * The entry burst: inside the last ENTRY_WINDOW slots the coin saw at least
 * MIN_BUYS buys from at least MIN_BUYERS wallets, net SOL inflow above
 * MIN_NET_SOL with buys outrunning sells, and the price up between MIN_RISE
 * and MAX_RISE while sitting within NEAR_HIGH of the window high.
 */
function burstSignal(t: Tape, now: number): boolean {
  const from = now - ENTRY_WINDOW;
  let buySol = 0;
  let sellSol = 0;
  let buys = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const buyers = new Set<string>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    if (tr.buy) {
      buySol += tr.sol;
      buys++;
      buyers.add(tr.user);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buys < MIN_BUYS || buyers.size < MIN_BUYERS) return false;
  if (buySol - sellSol < MIN_NET_SOL) return false;
  if (sellSol > 0 && buySol < MIN_BUY_SELL * sellSol) return false;
  if (startPrice <= 0 || last <= 0) return false;
  const rise = last / startPrice - 1;
  if (rise < MIN_RISE || rise > MAX_RISE) return false;
  if (last < high * NEAR_HIGH) return false;
  return true;
}

/** Fade exit: over the last FADE_WINDOW slots sells dominate buys. */
function fadeOut(mint: Pubkey, now: number): boolean {
  const t = tapes.get(mint);
  if (t === undefined) return false;
  const from = now - FADE_WINDOW;
  let buySol = 0;
  let sellSol = 0;
  let n = 0;
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= from) break;
    if (tr.buy) buySol += tr.sol;
    else sellSol += tr.sol;
    n++;
  }
  return n >= 4 && sellSol > 0 && buySol < FADE_BUY_SELL * sellSol;
}

await runBot({
  onBatch(state: BotState, batch) {
    const now = batch.slot;
    const orders: OrderInput[] = [];
    const txFee = state.txFeeLamports();

    // --- fold this batch's fills into the books ---
    for (const f of batch.fills) {
      if (f.status !== 'filled' || f.client_id.startsWith('_')) continue;
      if (f.side === 'buy') {
        tradedCoins.add(f.mint);
        if (probeBuying.has(f.mint)) {
          probeBuying.delete(f.mint);
          probeSelling.add(f.mint);
        }
      }
      if (f.side === 'sell') {
        probeSelling.delete(f.mint);
        const h = held.get(f.mint);
        if (h !== undefined) {
          h.exiting = false;
          const pos = state.positions.get(f.mint);
          if (pos === undefined) {
            held.delete(f.mint);
            const tp = tapes.get(f.mint);
            if (tp !== undefined) tp.lastExit = now;
          }
        }
      }
    }

    // --- fold this batch's events into the tapes ---
    const traded = new Set<Pubkey>();
    for (const e of batch.events) {
      if (e.event === 'CreateEvent') {
        tapeOf(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol: Number(e.sol_amount) / LAMPORTS,
          user: e.user,
          price: priceOf(BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves)),
        });
        traded.add(e.mint);
      } else {
        // CompleteEvent: the curve is done; drop its tape so it is never re-entered.
        tapes.delete(e.mint);
      }
    }
    if (firstSlot === null && batch.events.length > 0) firstSlot = now;
    for (const mint of traded) {
      const t = tapes.get(mint);
      if (t === undefined) continue;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - ENTRY_WINDOW - 50) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }

    const pendingBuy = new Set<Pubkey>();
    const pendingSell = new Set<Pubkey>();
    for (const po of state.pending.values()) {
      if (po.order.side === 'buy') pendingBuy.add(po.order.mint);
      else pendingSell.add(po.order.mint);
    }

    // --- exits first: free position slots before deciding entries ---
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingSell.has(mint) && !pendingBuy.has(mint)) {
          held.delete(mint);
          const t = tapes.get(mint);
          if (t !== undefined) t.lastExit = now;
        }
        continue;
      }
      if (curve === undefined || curve.complete || h.exiting || pendingSell.has(mint)) continue;
      const value = closeValue(pos.token_amount, curve.virtual_quote_reserves, curve.virtual_token_reserves);
      if (value > h.peakValue) h.peakValue = value;
      const cost = BigInt(pos.cost_lamports); // SOL spent on the tokens still held
      if (cost <= 0n) continue;
      let sell: bigint | null = null;
      if (!h.tookHalf && value >= (cost * 13n) / 10n) {
        sell = pos.token_amount / 2n; // take profit: sell half at +30%
        h.tookHalf = true;
        h.peakValue = value / 2n; // rescale the peak to the half left behind
      } else if (h.tookHalf && h.peakValue >= (cost * 11n) / 10n && value <= (h.peakValue * 85n) / 100n) {
        sell = pos.token_amount; // trailing stop on the rest
      } else if (value <= (cost * 85n) / 100n) {
        sell = pos.token_amount; // hard stop at -15%
      } else if (now - h.entrySlot >= MAX_HOLD) {
        sell = pos.token_amount; // time stop
      } else if (!h.tookHalf && value < cost && fadeOut(mint, now)) {
        sell = pos.token_amount; // buyers left while underwater
      }
      if (sell !== null && sell > 0n) {
        orders.push({ side: 'sell', mint, token_amount: sell, max_slippage_bps: SELL_SLIP_BPS });
        h.exiting = true;
      }
    }

    // --- probe sells: a probe round trip closes as soon as its buy lands ---
    for (const mint of probeSelling) {
      const pos = state.positions.get(mint);
      if (pos === undefined || pendingSell.has(mint)) continue;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: SELL_SLIP_BPS });
      probeSelling.delete(mint);
    }

    // --- entries: one buy per coin, only on a measured burst ---
    let free = state.freeCashLamports();
    let slotsOpen = state.hello.caps.max_open_positions - state.committedPositionCount();
    const decided = new Set<Pubkey>();
    for (const e of batch.events) {
      if (e.event !== 'TradeEvent') continue;
      if (orders.length >= state.hello.caps.max_orders_per_batch) break;
      const mint = e.mint;
      if (decided.has(mint) || !traded.has(mint)) continue;
      decided.add(mint);
      const t = tapes.get(mint);
      const curve = state.curves.get(mint);
      if (t === undefined || curve === undefined || curve.complete) continue;
      if (held.has(mint) || pendingBuy.has(mint) || probeBuying.has(mint) || probeSelling.has(mint)) continue;
      if (t.entries >= MAX_ENTRIES || now - t.lastExit < COOLDOWN) continue;
      if (t.created === null || now - t.created < MIN_AGE) continue;
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      if (rqSol < MIN_RQ_SOL || rqSol > MAX_RQ_SOL) continue;
      if (!burstSignal(t, now)) continue;
      if (slotsOpen <= 0) continue;
      const cap = state.maxBuyLamports(mint);
      const stake = SOL(STAKE_SOL);
      const amount = cap < stake ? cap : stake;
      if (amount < SOL(0.02) || free < amount + txFee) continue;
      orders.push({ side: 'buy', mint, quote_lamports: amount, max_slippage_bps: BUY_SLIP_BPS });
      free -= amount + txFee;
      slotsOpen -= 1;
      t.entries += 1;
      held.set(mint, { entrySlot: now, peakValue: 0n, tookHalf: false, exiting: false });
    }

    // --- guardrail probes: keep the coin count on pace when the signal goes quiet ---
    if (
      firstSlot !== null &&
      now - firstSlot >= PROBE_MIN_ELAPSED &&
      tradedCoins.size < PROBE_TARGET_COINS &&
      tradedCoins.size < Math.floor((PROBE_TARGET_COINS * (now - firstSlot)) / PROBE_PACE_SLOTS) + 1 &&
      probeBuying.size === 0 &&
      probeSelling.size === 0 &&
      slotsOpen > 0 &&
      orders.length < state.hello.caps.max_orders_per_batch
    ) {
      let best: Pubkey | null = null;
      let bestRq = -1;
      for (const mint of traded) {
        const curve = state.curves.get(mint);
        if (curve === undefined || curve.complete) continue;
        if (held.has(mint) || pendingBuy.has(mint) || tradedCoins.has(mint)) continue;
        const rq = Number(curve.real_quote_reserves);
        if (rq > bestRq && state.maxBuyLamports(mint) >= SOL(PROBE_SOL)) {
          best = mint;
          bestRq = rq;
        }
      }
      if (best !== null && free >= SOL(PROBE_SOL) + txFee) {
        orders.push({ side: 'buy', mint: best, quote_lamports: SOL(PROBE_SOL), max_slippage_bps: BUY_SLIP_BPS });
        probeBuying.add(best);
      }
    }

    return orders;
  },
});
