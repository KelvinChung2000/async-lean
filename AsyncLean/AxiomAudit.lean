/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Axiom audit

`#assert_standard_axioms foo bar …` fails (with an error, so the build fails) unless each of
the given declarations depends only on Lean's three standard foundational axioms:

* `propext` (propositional extensionality),
* `Quot.sound` (soundness of quotients, which also yields function extensionality),
* `Classical.choice` (the axiom of choice).

In particular it rejects `sorryAx` (any `sorry`, including ones hidden in dependencies),
`Lean.ofReduceBool` / `Lean.trustCompiler` (introduced by `native_decide`), and every
user-declared `axiom`.
-/

namespace AsyncLean

open Lean Elab Command

/-- Lean's standard foundational axioms. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_standard_axioms c₁ c₂ …` checks that every listed constant depends only on
`propext`, `Classical.choice` and `Quot.sound`. -/
elab "#assert_standard_axioms " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| Lean.collectAxioms n
    let bad := axs.filter (· ∉ standardAxioms)
    if bad.isEmpty then
      logInfo m!"{n} depends only on the standard axioms {axs.toList}"
    else
      throwErrorAt id m!"{n} depends on non-standard axioms: {bad.toList}"

end AsyncLean
