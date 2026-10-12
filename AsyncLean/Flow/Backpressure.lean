/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure.Instances

/-!
# Backpressure reaches the fluid optimum

This module gathers the backpressure development, in seven parts:

1. `Backpressure.Model` — the queueing model, the scheduler, stability, conservation;
2. `Backpressure.Stability` — the drift, stability and throughput optimality;
3. `Backpressure.Buffers` — finite per-destination buffers suffice;
4. `Backpressure.Bursty` — leaky-bucket arrivals, whole packets at fractional rates;
5. `Backpressure.Converse` — no scheduler beats the fluid model;
6. `Backpressure.Scheduler` — the greedy scheduler, with fractional or whole-packet sends;
7. `Backpressure.Instances` — the mesh, the torus and the hypercube with `m` connections.

The fluid model (`Fluid.Routable`) says which throughputs a network can carry at best.  These
modules prove that one scheduler, **backpressure** (max-weight scheduling, Tassiulas and
Ephremides), carries every one of them: every load strictly inside the fluid optimum keeps its
backlog bounded and is delivered in full.  Conversely no scheduler whatever keeps its backlog
bounded above any fluid upper bound (`Run.potential_bound`).  So the fluid optimum is exactly
the throughput of backpressure.

## The model

A **queueing run** (`Fluid.Run N`) runs in slots `t = 0, 1, …`.  Every vertex `v` keeps a
backlog `Q t v d ≥ 0` for every destination `d` (`Q t d d = 0`: a packet at its destination has
left).  In slot `t` the scheduler offers commodity `d` the rate `μ t d u v` on the link
`u → v`, within the capacities (`Feasible`); the link carries `x t d u v ≤ μ t d u v`, and no
vertex sends more of a commodity than it holds.  Then `a t v d ≥ 0` new traffic arrives:

  `Q (t+1) v d = Q t v d - (sent by v) + (received by v) + a t v d`   (`v ≠ d`).

Quantities are rational: the run is the queueing network of the fluid model in discrete time,
with packets as divisible as the fluid's.  The backpressure scheduler (`Run.Backpressure`):

* **max-weight** : the rates maximise `∑ d u v, μ d u v * (Q u d - Q v d)` (`weight`) among all
  feasible rates.  Giving every link, in full, to a commodity of largest backlog difference
  across it, when that difference is positive, is such a choice (`bpRates_maxWeight`).
* **work conserving** : a vertex sends of each commodity `min (backlog, offered rate)`.

## Main results

* `Run.backlog_succ`, `Run.delivered_sum` : conservation: the delivered traffic is what arrived
  less what is still queued.
* `Run.drift` : **the drift bound.**  If `dem` is routable at throughput `1` and the arrivals
  stay `ε` below it (`a t v d + ε ≤ dem v d`), the Lyapunov function `∑ Q²` of a backpressure run
  obeys `E (t+1) ≤ E t + B - 2 ε ∑ Q`, for a constant `B` of the network and the traffic.
* `Run.backpressure_stable` : the backlog of a backpressure run stays bounded, and it delivers
  all its arrivals up to a constant.
* `Run.backpressure_optimal` : **backpressure is throughput optimal.**  If `dem` is routable at
  `θ`, every load `ρ * dem` with `0 ≤ ρ < θ` (any arrivals below it, slot by slot) keeps the
  backlog bounded and is delivered in full.  Only some traffic reaching every pair is needed
  (for instance the uniform traffic): no knowledge of `dem`, `θ` or the flow is used by the
  scheduler.
* `Run.backpressure_fitsIn` : **finite buffers suffice.**  Started empty, the run never holds
  more than `B / (2 ε) + ε` in any per-destination queue (`Run.FitsIn`), so buffers of that size
  are never exceeded; the size grows like `1 / ε` as the load approaches the optimum.
  `mesh_buffer` : on the mesh with `m` connections per link, under a load `(1 - δ)` times the
  optimum, buffers of `145 m k⁷ / (16 δ) + m` packets per destination suffice (a loose constant).
* `Run.backpressure_stable_bursty` : **bursty arrivals**: the same for arrivals within a leaky
  bucket (at most `W (dem - ε) + σ` over every window of `W` slots), by the drift over frames
  (`Run.frame_drift`); this covers whole packets arriving at fractional rates.
  `Run.ofArrivalsSeq` : backpressure with sequential sends (`sendSeq`), which moves whole packets
  only (`Run.ofArrivalsSeq_int`); `mesh_backpressure_packets` : on the mesh with `m` connections
  it is stable for whole packets at every leaky-bucket rate below `m` times the optimum.
* `Run.potential_bound` : **the converse**, for every scheduler: a run that keeps its backlog
  bounded under the load `ρ * dem` respects every potential bound of the fluid model
  (`potential_bound`); `Run.cut_bound`, `Run.hop_bound` are the cut and hop forms.
* Instances, with `m` connections per link: on the `k × k` mesh (even `k`) under uniform traffic
  backpressure is stable at every load below `m * 8 (k² - 1) / k³`, no scheduler is stable
  above it (`mesh_backpressure`); likewise on the torus (`torus_backpressure`, `m` times
  `torus_uniform_opt`) and the hypercube (`cube_backpressure`).
* `Run.ofArrivals`, `Run.ofArrivals_backpressure` : for every arrival sequence there is a
  backpressure run (the greedy rates `bpRates`, proportional transmissions `sendAll`);
  `mesh_backpressure_exists` : on the mesh it is stable at every load below the optimum.

All results are over `ℚ`.
-/
