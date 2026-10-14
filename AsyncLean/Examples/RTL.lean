/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Import.Verilog
import AsyncLean.Routing.RTL
import AsyncLean.Examples.Routing
import AsyncLean.AxiomAudit

/-!
# Example: a network routed by its RTL

`designs/xy_route.v` is the routing logic of a router of the 4×4 mesh `xyMesh 4`: from the
router's node and the packet's destination (four bits each) it computes the output port (two
bits) by dimension-order routing.  `xyRouter` says how the network uses it: a packet held in
channel `c` with destination `d` is routed by the router at the node `head 4 c`, and port `o`
leads to the channel `ch (head 4 c) o 0`.

The kernel evaluates the netlist on all 2 560 pairs of a channel and a destination and finds
the same hops as `xyMesh`'s routing function (`xyMesh_implemented`), and checks that every
packet the network can carry is handled by the netlist (`xyMesh_covered`).  The correctness
of `xyMesh 4` therefore holds for the network routed by the netlist (`xyMesh_rtl_correct`),
under every selection function; `Comb.unique` makes the netlist's outputs independent of gate
delays.
-/

namespace AsyncLean.Examples

open Network Mesh

comb_from_verilog xyRoute "designs/xy_route.v"

/-- The four bits of a node number. -/
def bits4 (n : ℕ) : List Bool := [n.testBit 0, n.testBit 1, n.testBit 2, n.testBit 3]

/-- How `xyMesh 4` uses the routing logic. -/
def xyRouter : RtlRouter where
  comb := xyRoute
  nc := 160
  np := 16
  dom c _ := decide (head 4 c < 16)
  enc c d := bits4 (head 4 c) ++ bits4 d
  dec c d o := [(ch (head 4 c) ((o.getD 0 false).toNat + 2 * (o.getD 1 false).toNat) 0, d)]

/-- The netlist computes exactly the routing function of `xyMesh 4`. -/
theorem xyMesh_implemented : (xyMesh 4).implementedBy xyRouter = true := by decide +kernel

/-- The netlist handles every packet the network can carry. -/
theorem xyMesh_covered : (xyMesh 4).coveredBy xyRouter = true := by decide +kernel

/-- **The mesh routed by the netlist is deadlock and livelock free**, under every selection
function. -/
theorem xyMesh_rtl_correct : ((xyMesh 4).withRtl xyRouter).Correct :=
  correct_of_rtl xyMesh_implemented xyMesh_correct

#assert_standard_axioms xyMesh_implemented xyMesh_covered xyMesh_rtl_correct

end AsyncLean.Examples
