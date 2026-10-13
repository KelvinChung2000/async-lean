# Guides

[← back to the README](../README.md)

The [README](../README.md) is the user guide: setting up, the proof workflow, and one walkthrough
per kind of design. These guides go deeper into the routing and throughput results.

| Guide | Read it for |
|---|---|
| [How adaptive can routing be?](routing-adaptivity.md) | maximally adaptive deadlock-free mesh routing (proved for every size), costs and trade-offs, which run-time selection performs (simulation), safe history-dependent strategies and the packet-level ceiling |
| [Beyond the mesh](topologies.md) | safe routing on every finite connected graph; how much a topology can carry in the fluid model (exact optima); torus routing schemes with packets (simulation) |
| [Scaling with the connections](scaling.md) | what `m` connections per link buy: the linear ceiling, planes, packets in time, backpressure reaching the fluid optimum, and what is necessary; with a table of what is proved, measured and open |
| [Library map](library-map.md) | every Lean file and what it contains |
| [Glossary](glossary.md) | the library's names and the standard terms and references of each field |

Reading order for newcomers: the README's section 7, then the guides in the order above.
Throughout, **theorems** are named in `code` with the file that proves them, and
**simulation** results come from the scripts in [`scripts/`](../scripts/README.md); the guides
say which is which.
