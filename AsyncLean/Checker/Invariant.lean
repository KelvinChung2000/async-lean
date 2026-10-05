/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Explicit

/-!
# Certified reachable-state invariants

Many properties are of the form "every reachable state satisfies `P`", where `P` may look at
the successors of the state and at data attached to other states (for instance the set of
edges a neighbouring state enables).  An `InvCert` stores, for each candidate state, its
successor states (as literal data, so that the kernel does not recompute them during lookups)
and a datum of type `D`.  `checkInv` verifies

* the initial state is present,
* the stored successors are exactly the computed ones, and are all present,
* `P s (succ s) look` at every stored state, where `look` reads the stored data,

and `of_checkInv` concludes `P s (succ s) look` for **every reachable** state `s`.  The
certificate itself (`mkInvCert`) is computed by untrusted code.
-/

namespace AsyncLean

namespace ExplicitLTS

variable {S L D : Type*} (E : ExplicitLTS S L)

/-- An invariant certificate: states with their successors and a datum. -/
abbrev InvCert (S D : Type*) := BTree (S × (List S × D))

/-- Read the data stored in an invariant certificate. -/
def InvCert.look [DecidableEq S] (cmp : S → S → Ordering) (c : InvCert S D) (s : S) : Option D :=
  (c.findData cmp s).map Prod.snd

section

variable [DecidableEq S] (cmp : S → S → Ordering)

/-- Compute an invariant certificate (untrusted). -/
def mkInvCert (data : S → D) (fuel : ℕ) (s₀ : S) : InvCert S D :=
  let t := E.explore cmp fuel s₀
  BTree.ofList ((t.toListAcc []).map fun s => (s, ((E.succ s).map Prod.snd, data s)))

/-- The checks at one node. -/
def checkInvNode (P : S → List (L × S) → (S → Option D) → Bool) (c : InvCert S D) (s : S)
    (ss : List S) : Bool :=
  let es := E.succ s
  decide (es.map Prod.snd = ss) && (ss.all fun s' => (c.findData cmp s').isSome) &&
    P s ((es.map Prod.fst).zip ss) (c.look cmp)

/-- Check an invariant certificate (trusted). -/
def checkInv (P : S → List (L × S) → (S → Option D) → Bool) (s₀ : S) (c : InvCert S D) :
    Bool :=
  (c.findData cmp s₀).isSome && c.all fun x => E.checkInvNode cmp P c x.1 x.2.1

variable {E} {cmp}

theorem InvCert.mem_of_isSome {c : InvCert S D} {s : S} (h : (c.findData cmp s).isSome = true) :
    ∃ b, (s, b) ∈ c.toList := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
  exact ⟨b, BTree.mem_toList_of_findData hb⟩

/-- **Soundness**: the predicate holds at every reachable state. -/
theorem of_checkInv {P : S → List (L × S) → (S → Option D) → Bool} {s₀ : S} {c : InvCert S D}
    (h : E.checkInv cmp P s₀ c = true) :
    ∀ s, E.toLTS.Reachable s₀ s → P s (E.succ s) (c.look cmp) = true := by
  simp only [checkInv, Bool.and_eq_true, BTree.all_eq_true] at h
  obtain ⟨h₀, hc⟩ := h
  have hnode : ∀ s, (∃ b, (s, b) ∈ c.toList) →
      (∀ l s', (l, s') ∈ E.succ s → ∃ b, (s', b) ∈ c.toList) ∧
        P s (E.succ s) (c.look cmp) = true := by
    rintro s ⟨⟨ss, d⟩, hs⟩
    have := hc _ hs
    simp only [checkInvNode, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    obtain ⟨⟨hss, hmem⟩, hp⟩ := this
    subst hss
    rw [zip_map_fst_snd] at hp
    exact ⟨fun l s' hst => InvCert.mem_of_isSome (hmem s' (List.mem_map_of_mem hst)), hp⟩
  intro s hs
  have hinv : ∃ b, (s, b) ∈ c.toList :=
    hs.invariant (InvCert.mem_of_isSome h₀) fun s l s' hm hst => (hnode s hm).1 l s' hst
  exact (hnode s hinv).2

end

end ExplicitLTS

end AsyncLean
