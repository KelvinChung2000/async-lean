# Scripts

[← back to the README](../README.md)

Python 3 scripts that sit **next to** the Lean development. None of them is part of a proof:
the simulators measure throughput, the certificate generators compute data that Lean then
checks in the kernel, and the validators cross-check results independently. The simulators
need only the standard library, except `backpressure_sim.py` (`numpy`); the certificate
generators and `routing_bounds.py` need `scipy`.

Run them from the repository root, for example `python3 scripts/lane_scaling.py --help`.

## Simulators (measurements, not theorems)

| Script | What it measures | Results in |
|---|---|---|
| `routing_sim.py` | cycle-level mesh simulation of the routing functions of `Examples/Routing.lean` and `Examples/OptimalRouting.lean`; `--bench` prints the selection tables | [routing-adaptivity.md](../docs/routing-adaptivity.md) |
| `routing_experiments.py` | further selections on the mesh, beyond `tieredMesh` | [routing-adaptivity.md](../docs/routing-adaptivity.md) |
| `routing_graph_sim.py` | the same mechanics on any graph of radix ≤ 4 (mesh, torus, express links, …) | [topologies.md](../docs/topologies.md) |
| `flow_control_experiments.py` | reallocating the same buffer storage on the mesh | [topologies.md](../docs/topologies.md) |
| `torus_experiments.py` | routing schemes and detour rules on the 8 × 8 torus | [topologies.md](../docs/topologies.md) |
| `torus_final.py` | the final torus comparison (4 seeds) | [topologies.md](../docs/topologies.md) |
| `torus_significance.py` | the same with standard errors (8 fresh seeds) | [topologies.md](../docs/topologies.md) |
| `lane_scaling.py` | throughput per connection with `m` connections: lanes, shared lanes, widening | [scaling.md](../docs/scaling.md) |
| `backpressure_sim.py` | backpressure with whole packets: throughput, delay, buffer needs (`--buffers`, `--cap`) | [scaling.md](../docs/scaling.md) |

`routing_graph_sim.py` and `routing_sim.py` are also libraries: `lane_scaling.py`,
`torus_*.py` and `backpressure_sim.py` reuse their network and traffic definitions.

## Certificate generators (data checked by Lean)

| Script | Generates | Checked by |
|---|---|---|
| `fluid_certificates.py` | exact LP solutions (flows and dual lengths) for traffic patterns on the 8 × 8 mesh | `Flow/MeshPatterns/Data.lean`, checked by `Flow/Certificate.lean` |
| `graph_certificates.py` | the same for the 8 × 8 torus and the 6-cube | `Flow/GraphPatterns/Data.lean`, checked by `Flow/GraphCert.lean` |

## Cross-checks

| Script | What it checks |
|---|---|
| `validate_routing.py` | replays the deadlocks of the maximality proofs on meshes up to 8 × 8, and re-checks acyclicity, hop counts and routing-table sizes |
| `routing_bounds.py` | fluid-model throughput bounds on the k × k mesh, computed numerically |
