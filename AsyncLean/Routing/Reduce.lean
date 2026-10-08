/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic

/-!
# Reducing one routing function to another

A routing function may look nothing like a known deadlock-free one and still be one of its
disguises: if every channel dependency of its escape layer maps, along a map of the channels, to
a chain of dependencies of a routing function whose dependency graph is acyclic, then its own
dependency graph is acyclic, and Duato's theorem applies to it.

* `Network.wf_dep_of_reduction` : the transfer, for any map of channels.
-/

namespace AsyncLean

namespace Network

variable {C P C' P' : Type*}

/-- **Reduction of channel dependencies.**  If every dependency of the escape layer `R₁` of `N`
maps, along `φ`, to a chain of dependencies of the escape layer `R₁'` of `M`, and the dependency
graph of `M` is well-founded (acyclic), then so is the dependency graph of `N`. -/
theorem wf_dep_of_reduction (N : Network C P) (M : Network C' P') {legal : C → P → Prop}
    {R₁ : C → P → List (C × P)} {legal' : C' → P' → Prop} {R₁' : C' → P' → List (C' × P')}
    (φ : C → C')
    (h : ∀ c c', N.Dep legal R₁ c c' → Relation.TransGen (M.Dep legal' R₁') (φ c) (φ c'))
    (hwf : WellFounded (flip (M.Dep legal' R₁'))) : WellFounded (flip (N.Dep legal R₁)) := by
  have h1 : WellFounded (flip (Relation.TransGen (M.Dep legal' R₁'))) :=
    Subrelation.wf (fun h => Relation.transGen_swap.1 h) hwf.transGen
  exact Subrelation.wf (fun hab => h _ _ hab) (InvImage.wf φ h1)

end Network

end AsyncLean
