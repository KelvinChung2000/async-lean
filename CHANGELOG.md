# Changelog

## Unreleased

* **Packets in time, whole packets, adaptivity** (`Routing/Throughput.lean`,
  `Examples/Throughput.lean`, `Flow/Necessity.lean`). Timed runs of packet networks
  (`Network.TimedRun`) on a placement respect every fluid bound under any selection
  (`TimedRun.ceiling`, `cut_ceiling`, `hop_ceiling`) and deliver all but what the network holds
  (`ejected_ge`); lanes add their timed throughput (`lanesTimed_injected`); the torus with `m`
  lanes is exactly linear with packets up to `m` times the optimum (`torusLanes_ceiling`,
  `torusLanes_sustains`). Backpressure is stable for leaky-bucket arrivals
  (`Run.backpressure_stable_bursty`) and with whole packets (`Run.ofArrivalsSeq_int`,
  `mesh_backpressure_packets`). Stable runs respect every potential bound on the links they use
  (`Fluid.PotentialFeasibleOn`, `Run.potentialFeasibleOn`); on the torus under tornado,
  shortest-path-only scheduling is unstable above `2/3` while backpressure is stable below
  `16/15` (`torusTornado_adaptivity`). Score-based selections are valid, so correct networks
  stay safe under them (`scoreSel_valid`). `GraphCert.PortGraph.upper_of_check'` takes potential
  feasibility instead of a flow. Backpressure never deadlocks where every destination is
  reachable (`Run.backpressure_progress`); on the mesh it is a finite-buffer network near the
  optimum without deadlock (`mesh_finite_buffer_network`). A single first-in first-out queue per
  vertex is never stable above one packet per vertex and slot, so per-destination queues are
  necessary for linear scaling (`Run.singleHead_ceiling`, `mesh_headOfLine`). Restricted
  backpressure reaches the optimum over its permitted links (`Run.backpressureOn_optimal`,
  `torusTornado_minimal_backpressure`). Under random arrivals (mean given the past `ε` below a
  routable traffic, finite second moment: Poisson, for instance) backpressure is strongly stable
  for every expectation operator (`Flow/Stochastic.lean`, `backpressure_strongly_stable`).

* **Backpressure reaches the fluid optimum** (`Flow/Backpressure.lean`,
  `scripts/backpressure_sim.py`). A discrete-time queueing model of the fluid network
  (`Fluid.Run`); max-weight, work-conserving scheduling (`Run.Backpressure`) keeps the backlog
  bounded and delivers everything at every load below the fluid optimum (`Run.drift`,
  `Run.backpressure_stable`, `Run.backpressure_optimal`); no scheduler keeps a bounded backlog
  above any fluid bound (`Run.potential_ceiling`, `cut_ceiling`, `hop_ceiling`); the greedy
  scheduler is max-weight and yields a run for every arrival sequence (`bpRates_maxWeight`,
  `Run.ofArrivals`). With `m` connections per link under uniform traffic the threshold is exactly
  `m` times the optimum on the mesh, torus and hypercube (`mesh_backpressure`,
  `torus_backpressure`, `cube_backpressure`, `mesh_backpressure_exists`). `mesh_upper_of_cut`,
  `torus_uniform_hop`, `cube_uniform_hop` expose the tight bounds. With integer packets on the
  8 × 8 mesh and torus, backpressure accepts 99 % of the fluid optimum for `m = 1, 2, 4` (mesh
  0.975 per node per connection, against 0.45 to 0.64 for the lane and widened networks), at the
  cost of large per-destination queues and delays of hundreds of slots. Finite buffers suffice
  (`Run.FitsIn`, `Run.backpressure_fitsIn`: at most `driftConst / (2 ε) + ε` per destination;
  `mesh_buffer`: `145 m k⁷ / (16 δ) + m` on the mesh at `(1 − δ)` times the optimum); in
  simulation `24 m` packets per destination reach 98 % of the optimum and `16 m` lose up to 30 %
  (`backpressure_sim.py --buffers [--cap c]`).

* **Routing that scales linearly with the connections** (`Flow/Scaling.lean`,
  `Routing/Lanes.lean`, `Examples/Lanes.lean`, `scripts/lane_scaling.py`). In the fluid model the
  best throughput of `m` connections per link is exactly `m` times that of one
  (`copies_routable_iff`, `opt_copies`, `worstOpt_copies`), reached by `m` lanes each running the
  one-connection scheme; layers of unequal connections add (`layered_routable`,
  `opt_superadditive`). Worst case over admissible traffic with `m` connections: exactly `4m/k`
  (mesh), `8m/k` (torus), `2m` (hypercube). `Network.lanes` makes the lanes a packet network;
  `Network.SafeCert` packages the library's proof recipe and `SafeCert.lanes` lifts it to every
  number of lanes (deadlock, livelock and starvation freedom, delivery under saturation:
  `lanes_correct`, `lanes_underLoad`; on every graph for `GraphData.net`, `budgetNet` and
  `detourNet`, throttled sources included). The lanes are independent
  (`lanes_reachable_iff`, `lanes_path`), so `m` copies deliver `m` times the packets of one
  (`copies_path`). Sharing the connections is proved safe too: `GraphData.sharedNet` (escapes per
  lane, adaptive hops on every lane, `shared_correct`) and widening (`Network.widen`: any number of
  copies of every channel of any certified network, every copy usable, `SafeCert.widen`,
  `widen_correct`, `GraphData.wide_detour_correct`, `shared_slots_correct`). In simulation on the
  8 × 8 torus (`scripts/lane_scaling.py`), lanes keep the throughput per connection within 0.006
  of one connection's on every pattern for `m = 1, 2, 4`; widening to one escape and `2m - 1`
  adaptive channels gains 6 to 63 % per connection over lanes at `m = 4`.

* `scripts/torus_significance.py`: with 8 fresh seeds, `bandit2m7f5k` is ahead of dimension
  order, Valiant and UGAL on eight torus patterns by at least 3.5 standard errors and at the
  injection limit with them on neighbour traffic.

* **A torus scheme ahead of every existing one on every pattern (simulation)**:
  `bandit2m7f5k` in `scripts/torus_experiments.py` (marginal-cost prices, flow-count gate for
  the long way, Valiant only for concentrated destinations), a selection of the proved
  `detourNet`; `scripts/torus_final.py` reproduces the comparison.

* `scripts/torus_experiments.py`: latency-learning sources (`bandit<e>[h<h>][q<q>][g<g>]`) beat
  every existing torus scheme on seven of nine patterns, tie on neighbour traffic, and trail
  UGAL by 1.8 % on bit complement; all variants lie on one tornado / bit-complement frontier.

* **Detours, proved safe** (`Routing/GraphDetour.lean`, `Examples/GraphDetour.lean`). The header
  `(d, w, b)` adds a source-chosen intermediate node to `GraphBudget`; for every finite connected
  graph, budget and choice of intermediates the network is deadlock free, livelock free with an
  explicit hop bound, starvation free and delivers under sustained load (`detour_correct`,
  `detour_underLoad`, `exists_detour_correct`); torus instances for every size.

* `scripts/torus_experiments.py`: torus routing with packets — dimension order with datelines,
  Valiant, UGAL, the proved minimal adaptive tree-escape network, and source-chosen detours
  (long way round a ring or a random intermediate, by smoothed congestion). The detour variants
  come within 1 % of the best existing scheme on every pattern and beat it on most; none is at
  least as good on all.

* `scripts/flow_control_experiments.py`: flow control at equal storage on the 8 × 8 mesh. Shared
  slots and deeper single lanes lose; lanes moved to the middle of the mesh trade gains on
  uniform, shuffle, bit-complement and hotspot traffic for losses on transpose and bit
  reversal; only more storage wins on every pattern.

* **Beyond the mesh: which topologies need detours** (`Flow/Topologies.lean`, `Flow/Tree.lean`,
  `Flow/Symmetric.lean`, `Flow/Valiant.lean`, `Flow/GraphCert.lean`, `Flow/GraphPatterns.lean`,
  `scripts/graph_certificates.py`). Minimal routing is optimal for every traffic matrix iff the
  network is a tree (`minimal_optimal_iff_isTree`); for uniform traffic on every arc-transitive
  network (`symmetric_opt`; torus and hypercube optima in closed form). Valiant's bound on every
  network with symmetric capacities (`valiant`) gives the exact worst case of the mesh (4/k),
  the torus (8/k) and the hypercube (2). Exact optima on the 8 × 8 torus and the 6-cube by
  kernel-checked certificates: detours gain up to 60 % on the torus (tornado, shuffle,
  transpose, neighbour, bit reversal) and 45 % on the hypercube (shuffle).

* **Routing on the mesh has no room left, proved in the fluid model** (`Flow/MeshOdd.lean`,
  `Flow/MeshWorst.lean`, `Flow/Certificate.lean`, `Flow/MeshPatterns.lean`,
  `scripts/fluid_certificates.py`). `Flow.Minimal` and `Flow.potential_bound_on` (the dual bound
  for a flow restricted to some links). Uniform traffic: the optimum for every k (8/k for odd k,
  `mesh_opt_all`), reached by XY without detours (`uniform_minimal_opt`). Worst case over
  admissible traffic: O1TURN routes every admissible matrix at 4/k (`o1turn_admissible`) and no
  routing does better (`worst_opt`, even k); XY's worst case is exactly 2/(k − 1)
  (`xy_worst_opt`); bit complement's optimum is 4/k (`bitcomp_opt`). On the 8 × 8 mesh, exact
  optima by kernel-checked LP certificates: transpose 10/11, shuffle 1, bit reversal 20/21 —
  all reached by minimal flows — and hotspot 40/67 against 840/1471 for minimal flows.

* **The wire ceiling, proved** (`Flow/Fluid.lean`, `Flow/MeshWire.lean`, fluid model over ℚ).
  `Fluid.potential_bound` (weak duality for multicommodity flow) gives the wire bound
  (`wire_bound`: traffic × distance ≤ capacity × wire, every topology and routing) and the cut
  bound (`cut_bound`). On the k × k grid under uniform traffic: `throughput_le_wire`
  (θ ≤ 6 · wire / k³), `mesh_opt` (the mesh's optimum is exactly 8(k² − 1)/k³ for even k; an
  explicit XY flow reaches it for every k), and `wire_ceiling` (no network with the mesh's wire
  beats it by more than 3k / (2(k + 1)) < 3/2).

* `scripts/routing_graph_sim.py`: the cycle-level simulator for arbitrary graphs (same mechanics
  as `routing_sim.py`, spanning-tree or XY escape, bounded returns) and the wire-budget designs
  `CA_112`, `D_128`, `DF_156`; README "Beyond the mesh": at equal radix and wire, no topology
  tried beats the mesh significantly with packets, though the fluid model allows up to +33 %.

* **Bounded returns from the escape layer** (`Routing/GraphBudget.lean`,
  `Examples/GraphBudget.lean`). The absorbing escape of `Routing/Graph.lean` costs throughput,
  and unbounded returns can livelock. A packet header now carries a return budget `B`: from an
  escape channel a packet may take an adaptive hop while its budget lasts, spending one unit.
  For every finite connected graph and every `B` the network is deadlock free, livelock free
  (at most `B * rankBound + (2 * height + 1) * (dist + 1)` hops), starvation free and delivers
  under sustained load (`budget_correct`, `budget_correct_of_sourceSel`, `budget_underLoad`,
  `exists_budget_correct`); `B = 0` is the absorbing network. Torus instances for every size.

* **Delivery under sustained load** (`Routing/Saturation.lean`, `Examples/Saturation.lean`).
  Strong fairness over whole transitions makes a run of a finite deadlock- and livelock-free
  network revisit the empty configuration, so `StarvationFree` says nothing about a saturated
  network. `ChannelFair` asks only that a channel offered a way out infinitely often gets its
  packet out infinitely often; it is implied by strong fairness and allows runs that never
  drain (`Network.Saturated`: a channel-fair run that injects forever and is never empty
  again). Under it, with injections never stopping, every packet outside the throttled
  sources is delivered (`Network.starvationFreeUnderLoad_of_source`), every packet under
  selections that never refuse a free escape hop (`starvationFreeUnderLoad_of_escape`).
  Instances for every size: Duato's, the west-first and the north-last mesh under every tiered
  selection containing the throttled escape tier and under every valid selection, and every
  finite connected graph (`GraphData.underLoad`, `GraphData.exists_underLoad`). Packets held in
  a throttled injection channel can starve under saturation and are not covered.

* **Safe adaptive routing on every topology** (`Routing/Graph.lean`). For every finite connected
  undirected graph (`GraphData`: vertex list, symmetric neighbour lists, a distance estimate and
  a rooted spanning tree, which `GraphData.ofConnected` builds for any connected graph), minimal
  adaptive routing on virtual channel 1 with an absorbing tree-routing escape on virtual channel
  0 is deadlock, livelock and starvation free (`GraphData.correct`; starvation freedom under strong
  fairness, which makes a run revisit the empty network), also under every selection
  satisfying `EscapeSel` or `SourceSel` (`correct_of_escapeSel`, `correct_of_sourceSel`);
  `GraphData.exists_correct` states it for every connected graph. Instances
  (`Examples/GraphRouting.lean`): the torus of every size (`torus_correct`) and the Petersen
  graph (`petersen_correct`).
  * `scripts/routing_bounds.py`: the optimal throughput of mesh routing with and without
    detours (a linear program) and the worst case of XY and O1TURN over all permutations.

* **Any preference is safe** (`Examples/MeshTiered.lean`): Duato's, the west-first and the
  north-last mesh are deadlock, livelock and starvation free under every tiered selection that
  contains the throttled escape tier `Mesh.escTier`, for every size (`duatoTiers_correct`,
  `westFirstTiers_correct`, `northLastTiers_correct`); `tieredMesh` is one instance.
  * `Routing/Reduce.lean`: `Network.wf_dep_of_reduction`, acyclic channel dependencies transfer
    along any map of channels that sends dependencies to chains of dependencies (a tool; nothing
    uses it yet).
  * `scripts/routing_experiments.py`: a global-view selection, sources learning their mode, a
    controller switching modes, two-phase XY, patience and distance rules (only the global-view
    and west-first selections are covered by the theorems; the others keep per-packet or global
    state). None beats every
    existing scheme on every pattern; under bit-complement traffic XY on both virtual channels is
    at the bisection limit of the model.

* **A selection that performs, proved safe** (`Examples/MeshTiered.lean`). `tieredMesh` offers a
  packet its dimension-order hop (XY on virtual channel 0, YX on virtual channel 1), then the
  escape hop, then virtual channel 1, and throttles the sources: a packet leaves its injection
  channel only towards a router with at least `g` of its 8 outgoing channels free (channels leaving
  the mesh count as free). Duato's mesh,
  the west-first and the north-last mesh are deadlock, livelock and starvation free under it for
  every size and every `g ≤ 8` (`duatoTiered_correct`, `westFirstTiered_correct`,
  `northLastTiered_correct`). In simulation it has the best worst case over six traffic
  patterns of the schemes compared on 8 × 8 and 16 × 16 meshes, and the highest peak
  throughput under four of them.
  * `Routing/Source.lean`: Duato's theorem for selections that hold packets back at their
    sources (`Network.SourceSel`, `Network.deadlockFreeWith_of_source`), starvation freedom
    under such a selection (`Network.StarvationFreeWith`,
    `Network.starvationFreeWith_of_source`), and tiered selections (`Network.tieredSel`).
  * `Network.delivered_of_ranking` and `Network.reachable_finite` only need the selection to
    offer permitted hops.
  * `scripts/routing_sim.py`: source throttling (`T<g>:`), the tiered selection, O1TURN, XY on
    both virtual channels, three more traffic patterns and `--bench`;
    `scripts/validate_routing.py` runs random single-step runs of the tiered selection on small
    meshes for every threshold and finds no deadlock.

* **Maximally adaptive on every mesh size** (`Examples/MeshMaximal.lean`). The west-first and
  north-last meshes are maximally adaptive among minimal routing functions on two virtual
  channels for every `k` (`westFirstMesh_maximal_all`, `northLastMesh_maximal_all`), with no
  common improvement for every `k ≥ 2` and Duato's mesh not maximal for every `k ≥ 2`. The
  proof follows the packet that takes an extra hop and closes with one of eight deadlocks
  checked in a 3 × 3 window.
  * `Routing/Embed.lean`: `Network.runGoodB`, `Network.path_of_runGoodB` and
    `Network.not_deadlockFree_of_runGoodB` carry a run and a deadlock of a small network into
    a large one along a map of channels and headers, with frozen packets standing for packets
    whose destination lies outside the window.
  * `Mesh.MeshFamily` collects what the window argument needs of a family of mesh routing
    functions; the 4 × 4 search of `OptimalRouting.lean` is subsumed and removed.
* **The north-last mesh of every size** (`Examples/MeshNorthLast.lean`) is deadlock and
  livelock free, starvation free and correct under escape-respecting selections, along
  shortest paths. Under wormhole switching Duato's condition fails for it.
* **Optimal routing per cost** (`Examples/MeshMetrics.lean`), for every mesh size:
  * hop count: `hops_lower_bound` (no neighbour routing beats the distance) and
    `family_latency_optimal`;
  * buffers: `westFirst1` and `northLast1` on a single virtual channel are correct (also under
    wormhole switching) and maximally adaptive among minimal routing on one virtual channel;
    XY is correct (`xyMesh_correct_all`) but not maximal;
  * routing tables: `table_lower_bound` (4 decisions per inner router for any deadlock-free
    minimal routing), `xy_table` (XY makes exactly 4), `westFirstMesh_table_le` and
    `northLastMesh_table_le` (at most 8, independent of the size).
* `scripts/validate_routing.py` replays the maximality constructions on meshes up to 8 × 8 and
  re-checks acyclicity, hop counts and table sizes; `scripts/routing_sim.py` simulates the
  single-channel schemes too.

* **Maximally adaptive routing** (`Routing/Optimal.lean`). `Network.Extends` and
  `Network.Within` compare routing functions by the hops they permit.
  `Network.MaximallyAdaptive U N` says that adding any set of hops of `U` to `N` introduces a
  deadlock.
  * `Network.not_deadlockFree_of_refuteBetweenB` refutes every routing function between two
    bounds with one run. `Network.not_deadlockFree_of_checkTree` does the same with case
    splits on single hops.
  * The trusted checker `Network.maxCheck` and its soundness theorem
    `Network.maximallyAdaptive_of_maxCheck`. `async_decide` proves `N.MaximallyAdaptive U`.
    `#eval N.explainMaximal …` reports the search.
  * `Network.MaximallyAdaptive.not_deadlockFree`: two maximal networks that differ have no
    common deadlock-free extension.
  * `Network.MaximallyAdaptive.wormhole`: maximality carries over to wormhole switching.
  * Examples (`Examples/OptimalRouting.lean`): Duato's mesh is not maximally adaptive. Two new
    schemes give virtual channel 0 a west-first or a north-last turn model on top of the XY
    escape hop. Both are minimal and strictly more adaptive than Duato's mesh, for every size.
    The west-first mesh of **every size** is deadlock and livelock free, starvation free and
    correct under wormhole switching, and every packet takes exactly as many hops as the
    distance to its destination. It is maximally adaptive among minimal routing functions on
    two virtual channels on the 3 × 3 mesh (the north-last mesh too), also under wormhole
    switching. No deadlock-free routing function contains both. Fully adaptive
    minimal routing on both virtual channels deadlocks.
* **Duato's theorem for congestion-aware selections** (`Network.EscapeSel`,
  `Network.deadlockFreeWith_of_escape`, `Network.livelockFreeWith_of_ranking`): a selection may
  decline free adaptive hops as long as it never refuses a free escape hop. `Network.gatedSel`
  offers the escape hops and the adaptive hops a predicate admits. In the examples,
  `westFirstGated` uses the extra hops of the west-first mesh only towards lightly loaded
  routers; it is correct for every size (`westFirstGated_correct`).
* `scripts/routing_sim.py`: a cycle-level simulation of the mesh routing functions (outside the
  Lean development). More adaptivity on the escape layer can lower saturation throughput under
  adversarial traffic; the gated selection avoids that.
* `Network.deadlockFree_of_wormholeDeadlockFree`: one-flit packets behave like store-and-forward
  packets, so wormhole deadlock freedom implies store-and-forward deadlock freedom.
* `Network.packet_hops_eq` (exact hop counts when every hop decreases a ranking by one) and
  `Network.wf_of_lexRank` (well-foundedness from a lexicographic numbering of the channels).

* **Interconnection networks with dynamic routing** (`Routing/Basic.lean`). `Network` models
  packet-switched networks with one-packet channel buffers, adaptive routing functions and
  run-time selection functions. `Network.Correct` is routing deadlock freedom and routing
  livelock freedom under *every* work-conserving selection function. The new results:
  * Duato's theorem (`Network.deadlockFree_of_escape`) and Dally and Seitz's theorem
    (`Network.deadlockFree_of_cdg`);
  * livelock freedom from a ranking function, for minimal or bounded non-minimal routing
    (`Network.livelockFree_of_ranking`), with per-packet hop bounds
    (`Network.packet_hops_le`);
  * the drain theorem (`Network.Correct.drain`);
  * the reduction of every selection policy to fully adaptive routing;
  * refutations from counterexample runs.
* `async_decide` proves `Network.Correct` by kernel-checked local certificates
  (`Network.checkCert`), with no exploration of network configurations. On failure it reports
  a deadlock or livelock counterexample and the theorem that proves it. `async_routing
  (escape := R₁)` names the escape channels. `#eval N.explain` prints the same report.
* **Duato's condition is necessary** (`Network.staticDeadlockFree_iff_exists_escape`,
  `Network.deadlockFree_iff_exists_escape`): an equivalence when finitely many channels carry
  legal packets.
* **Starvation freedom** (`Routing/Fairness.lean`): `Network.StarvationFree`, every packet is
  delivered along every strongly fair run (`Network.delivered_of_ranking`,
  `Network.starvationFree_of_escape_ranking`); `async_decide` proves it.
* **Wormhole switching** (`Routing/Wormhole.lean`, `Routing/WormholeCheck.lean`): packets
  spanning several channels, Duato's theorem with the extended dependency graph
  (`Network.wormholeDeadlockFree_of_escape`), Dally and Seitz's theorem, livelock freedom by
  ranking and the drain theorem, for packets of every length. Kernel-checked certificates
  through `async_decide` and `async_routing (escape := E)`, refutations and diagnosis
  (`#eval N.explainWormhole`).
* `LTS.LivelockFree.mono`, `LTS.LivelockFree.of_sub`, `LTS.Path.iStep_rtc`,
  `LTS.Path.iStep_transGen`.
* Examples (`Examples/Routing.lean`): rings with and without a dateline, with proofs for
  dateline rings of every size (correct, starvation free, wormhole correct); XY, fully
  adaptive, Duato, bounded-misrouting and deflection meshes, under store-and-forward and
  wormhole switching. A tutorial section on routing.

* **Partial-order reduction.** Stubborn sets preserve deadlocks (`Net.reachable_red_of_dead`);
  `async_decide` checks deadlock freedom on a reduced state space whose stubborn sets the
  kernel verifies marking by marking (`PNet.deadlockFree_of_checkPOR`).
* **Partial-order reduction for liveness and livelock freedom.** The cycle proviso makes a
  reduced state space decide liveness (`Net.catchUp`, `Net.live_of_stubborn`); visibility
  and a rank on internal steps decide livelock freedom (`Net.livelockFree_of_stubborn`).
  `async_decide` proves `Correct`, livelock freedom and liveness this way
  (`PNet.correct_of_checkPORc`): a 40-stage FIFO is `Correct` in 4.4 s, a 12-stage one in
  0.25 s instead of 13 s.
* **Symbolic certificates.** Decision diagrams of an inductive invariant, of witnesses, and of
  distances and ranks, checked by the kernel through joint walks before and after each
  transition without enumerating any marking (`PNet.of_checkBDD`); computed by a small
  untrusted decision-diagram package (`PNet.BDDGen.mkBDDCert`). New tactic `async_bdd`;
  `async_decide` falls back on it for large safe nets.
* **Linear potentials in symbolic certificates.** Liveness from weights on the places that
  every witness decreases, down to hubs, and livelock freedom from weights that every
  internal transition decreases (`PNet.phiL_lt`); both are found by linear programming and
  replace the diagrams of distances and ranks when they exist. Witnesses are chosen over the
  whole space, which makes their diagram up to 15× smaller.
* **Shorter joint walks.** Each level of the diagrams reads one place (`PNet.vars_inj`), so a
  walk on the invariant starts at the cut of the first level a transition touches
  (`PNet.cut_reach`, checked once for all transitions), stops below the last one
  (`PNet.Reach.congr`), and a coverage walk stops at the first data leaf. Together with
  hub traces from shared forward layers, seven philosophers are proved `Correct`
  symbolically in 1.4 s instead of 47 s; a 20-stage FIFO and twelve philosophers, out of
  reach before, in 1.9 s and 3.8 s.
* **Saturation.** The untrusted search computes reachable markings by saturation, and
  backward closures by saturation constrained by them; traces from hubs come from chained
  rounds of images. The search for a 40-stage FIFO takes 1.2 s instead of 21 s, and an
  80-stage FIFO and forty philosophers are proved `Correct` symbolically in 11 and 13 s.
* **Cheaper symbolic checks.** Diagram nodes are packed into one number per field, so the
  kernel reads a node with a few shifts instead of a search (`PNet.nget`); the decrease of
  the potential is checked once per witness transition instead of once per leaf; the search
  finds the rank and the potential with one linear program when it can, and walks traces
  back by galloping search. Symbolic proofs are 5–25% faster.
* **Lexicographic measures.** When no linear potential decreases every witness (or every
  internal transition), each may decrease it or keep it while decreasing a distance (or rank)
  diagram (`PNet.phiL_le`). The diagrams then count only the steps keeping the potential, and
  livelock freedom is decided completely: a cycle of internal steps keeps every potential.
* **Faster kernel lookups.** `Fast.kfind` compares with `Nat.ble` instead of `Nat.blt`,
  which halves the cost of a lookup in the kernel and speeds up every fast checker.
* **The state equation.** Deadlock freedom from a Farkas certificate refuting every dead
  solution of `M = M₀ + C · x` (`Net.deadlockFree_of_stateEq`), found by linear programming,
  with no exploration; used by `async_structural`, and by `async_decide` when the reduced
  state space is too large.
* **Fast kernel checking.** A checker on natural-number states with recursor-based inner
  loops (`Fast.of_check`), and its instance for nets packed into bit fields
  (`PNet.checkFast`): about 7× faster than before. Bounds from place invariants are checked
  all at once, packed into one number per place (`PNet.bounded_of_checkPInv`).
* **Concurrent firing.** Step semantics for Petri nets (any multiset of enabled transitions
  fires at once) and circuits (any set of excited gates switches at once), with proofs that
  they agree with the interleaving semantics: always for nets, and for speed-independent
  circuits (`Circuit.correct_iff_stepCorrect`).
* **Unbounded nets.** Checking through finite over-approximations (`ExplicitLTS.Abstracts`,
  with must-distances for liveness) and the counter abstraction of Petri nets
  (`PNet.of_checkAbs`); `async_decide` uses it when the state space does not close, and
  `async_decide (cap := k)` refines it.
* **No dead end on hard siphon–trap instances.** The certificate search has a size budget;
  beyond it `async_structural` falls back on model checking.
* Faster untrusted search: AVL trees for explored states (sorted insertions no longer
  degrade), and counterexample search in linear space.
* **Commoner's theorem for free-choice nets, both directions** (`Net.live_iff_siphonTrap`);
  the necessity direction refutes liveness.
* **Siphon–trap certificates.** The siphon–trap property is checked from a kernel-verified
  branching certificate on bit masks instead of enumerating sets of places;
  `async_structural` also proves deadlock freedom of ordinary nets this way.
* **Isochronic forks per branch.** `Forks` declares isochronic signals or groups of branches
  sharing one wire.
* **Faster circuit checking.** Bit-packed circuit states, recursor-based gate evaluation,
  circuits evaluated to literals once, and labelled-successor certificates for persistence
  (about 3× faster on wired circuits).
* **Design files tracked by Lake** through an `input_dir` target.

## 0.2.0

New models and theory:

* **STGs.** Signal transition graphs (`StgModel`, `Stg`) with consistency, complete state
  coding and output persistence. Conformance of a gate-level implementation implies the
  correctness of the closed loop (`Stg.implementation_correct`) and its hazard freedom.
  Complete state coding is exactly implementability (`StgModel.csc_iff_exists_conformant`).
* **Composition.** Parallel composition, hiding and divergence-preserving weak bisimulation,
  which is a congruence preserving deadlock and livelock freedom (`LTS/Compose.lean`).
* **Fairness.** Infinite runs and strong fairness: live actions happen infinitely often, and
  fair runs make progress (`LTS/Fairness.lean`).
* **Free-choice nets.** Commoner's liveness theorem (`Net.live_of_siphonTrap`).
* **Wire delays.** `Circuit.withWires`, `Circuit.QDI`, and the proof that QDI implies speed
  independence (`Circuit.speedIndependent_of_qdi`, `Circuit.correct_of_qdi`).

Tools:

* `async_decide` handles STG goals (specification, consistency, CSC, output persistence,
  conformance, closed-loop properties), QDI goals, boundedness and safeness, and generic
  explicit transition systems.
* `async_minimize` replaces a component of a parallel composition by a certified minimal
  quotient.
* `async_structural` proves safeness, boundedness, livelock freedom for every initial
  marking, and liveness of marked graphs and free-choice nets, from certificates found by
  linear programming and graph search.
* Importers: `stg_from_g` (Petrify / Workcraft `.g`), `pnet_from_pnml` (PNML),
  `gates_from_verilog` and `circuit_from_verilog` (structural Verilog).
* Faster kernel checking: literal successor lists, home-state certificates, and bit-packed
  markings for safe nets, about 6× faster on the dining philosophers.

Documentation: a checked tutorial (`AsyncLean/Tutorial.lean`) and a doc-gen4 setup
(`docbuild/`, `.github/workflows/docs.yml`).

## 0.1.0

* Labelled transition systems and the properties deadlock freedom, livelock freedom,
  liveness and persistence, with proof and refutation rules and the progress theorem.
* Petri nets, P-invariants, siphons and traps, linear ranking functions.
* Marked graphs: Commoner's theorem, token conservation, safeness; parametric Muller rings.
* Gate-level circuits with Muller semantics and speed independence.
* A verified certificate checker and the `async_decide` tactic, with counterexample
  diagnosis.
* Axiom audit (`#assert_standard_axioms`).
