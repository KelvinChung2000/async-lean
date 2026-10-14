/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic
import AsyncLean.Circuit.Comb

/-!
# Routing functions implemented by gate-level netlists

The theorems of `AsyncLean.Routing.Basic` are about a network's routing function as a Lean
definition.  In silicon the routing decision is made by the router's routing logic, a
combinational netlist (`Comb`, imported from Verilog with `comb_from_verilog`).  This file
connects the two.

An `RtlRouter` says how the netlist is used: which `(channel, header)` pairs it handles
(`dom`, all below the bounds `nc` and `np`), which input bits it reads for a pair (`enc`, for
example the bits of the current node and of the destination), and how its output bits decode
into hops (`dec`, for example a port number into the next channel).

* `Network.withRtl N r` is the network whose routing decisions, on the pairs the router
  handles, are the netlist's outputs.
* `Network.implementedBy N r` is a Boolean check, decided by the kernel by evaluating the
  netlist on every handled pair: the netlist is well formed and offers exactly the hops of
  `N.route` on every handled pair of a packet that has not arrived.  Then
  `N.withRtl r = N` (`withRtl_eq`), so **every theorem about `N` holds for the network routed
  by the netlist** (`correct_of_rtl`, `deadlockFree_of_rtl`, …).
* `Network.coveredBy N r` checks that the router handles every packet the network can carry:
  injected packets, and the hops of handled packets, are handled.  Then in every reachable
  configuration, under every selection function, every packet is in the router's domain
  (`legal_of_coveredBy`): the network never relies on routing decisions outside the netlist.

`Comb.unique` justifies reading the netlist as a function: every settled state of the gates
agrees with `Comb.eval`, whatever the gate delays.
-/

namespace AsyncLean

namespace Network

/-- A router's routing logic: a combinational netlist, the pairs it handles, the input bits it
reads for a pair, and how its output bits decode into hops. -/
structure RtlRouter where
  /-- The routing logic. -/
  comb : Comb
  /-- Channels handled are below `nc`. -/
  nc : ℕ
  /-- Headers handled are below `np`. -/
  np : ℕ
  /-- The pairs handled. -/
  dom : ℕ → ℕ → Bool
  /-- The input bits for a pair. -/
  enc : ℕ → ℕ → List Bool
  /-- The hops encoded by the output bits, for a pair. -/
  dec : ℕ → ℕ → List Bool → List (ℕ × ℕ)

namespace RtlRouter

variable (r : RtlRouter)

/-- The pair is handled (and within the bounds). -/
def inDom (c p : ℕ) : Bool := decide (c < r.nc) && decide (p < r.np) && r.dom c p

/-- The hops the netlist offers for a pair. -/
def hops (c p : ℕ) : List (ℕ × ℕ) := r.dec c p (r.comb.eval (r.enc c p))

end RtlRouter

variable (N : Network ℕ ℕ) (r : RtlRouter)

/-- **The network routed by the netlist**: on the handled pairs of packets that have not
arrived, the hops are decoded from the netlist's outputs. -/
def withRtl : Network ℕ ℕ :=
  { N with route := fun c p => if r.inDom c p && !N.arrived c p then r.hops c p else N.route c p }

/-- **The netlist implements the routing function** on the pairs it handles. -/
def implementedBy : Bool :=
  r.comb.wf && (List.range r.nc).all fun c => (List.range r.np).all fun p =>
    !(r.inDom c p && !N.arrived c p) || r.hops c p == N.route c p

/-- **The router handles every packet the network can carry.** -/
def coveredBy : Bool :=
  N.inject.all (fun q => r.inDom q.1 q.2) &&
    (List.range r.nc).all fun c => (List.range r.np).all fun p =>
      !(r.inDom c p && !N.arrived c p) || (N.route c p).all fun q => r.inDom q.1 q.2

variable {N r}

theorem inDom_lt {c p : ℕ} (h : r.inDom c p = true) : c < r.nc ∧ p < r.np := by
  simp only [RtlRouter.inDom, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem withRtl_eq (h : N.implementedBy r = true) : N.withRtl r = N := by
  simp only [implementedBy, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨-, h⟩ := h
  cases N with
  | mk arrived route inject =>
    simp only [withRtl, mk.injEq, true_and, and_true]
    funext c p
    split_ifs with hd
    · obtain ⟨hc, hp⟩ := inDom_lt (Bool.and_eq_true_iff.1 hd).1
      rcases h c hc p hp with h' | h'
      · rw [hd] at h'; cases h'
      · exact h'
    · rfl

/-- The netlist's settled outputs are its evaluation: the routing decisions do not depend on
gate delays. -/
theorem hops_of_settled (hwf : r.comb.wf = true) {c p : ℕ} {v : ℕ → Bool}
    (hin : ∀ i < r.comb.nin, v i = (r.enc c p).getD i false)
    (hg : ∀ g ∈ r.comb.gates, v g.1 = g.2.eval v) :
    r.dec c p (r.comb.outs.map v) = r.hops c p := by
  unfold RtlRouter.hops Comb.eval
  congr 1
  exact List.map_congr_left fun o ho => Comb.unique hwf hin hg o ho

/-- **Correctness transfers to the network routed by the netlist.** -/
theorem correct_of_rtl (h : N.implementedBy r = true) (hc : N.Correct) : (N.withRtl r).Correct :=
  (withRtl_eq h).symm ▸ hc

theorem deadlockFree_of_rtl (h : N.implementedBy r = true) (hc : N.DeadlockFree) :
    (N.withRtl r).DeadlockFree :=
  (withRtl_eq h).symm ▸ hc

theorem livelockFree_of_rtl (h : N.implementedBy r = true) (hc : N.LivelockFree) :
    (N.withRtl r).LivelockFree :=
  (withRtl_eq h).symm ▸ hc

/-- The handled pairs are closed under injection and routing. -/
theorem closed_of_coveredBy (h : N.coveredBy r = true) : N.Closed fun c p => r.inDom c p = true := by
  simp only [coveredBy, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨hinj, hrt⟩ := h
  refine ⟨fun q hq => hinj q hq, fun c p q hcp harr hq => ?_⟩
  obtain ⟨hc, hp⟩ := inDom_lt hcp
  rcases hrt c hc p hp with h' | h'
  · simp [hcp, harr] at h'
  · exact h' q hq

/-- **Every packet is handled by the router**: in every reachable configuration, under every
valid selection function, every packet is in the router's domain. -/
theorem legal_of_coveredBy (h : N.coveredBy r = true) {sel : Selection ℕ ℕ}
    (hsel : N.ValidSel sel) {f : Config ℕ ℕ} (hf : (N.ltsWith sel).Reachable empty f) :
    ∀ c p, f c = some p → r.inDom c p = true :=
  N.legal_of_reachable (closed_of_coveredBy h) hsel hf

end Network

end AsyncLean
