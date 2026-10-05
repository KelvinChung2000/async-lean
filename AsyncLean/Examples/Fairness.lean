/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Fairness
import AsyncLean.Examples.Counterexamples
import AsyncLean.Examples.Philosophers
import AsyncLean.AxiomAudit

/-!
# Example: fairness

* The retry protocol of `Examples.Counterexamples` *can* livelock: the sender may be refused
  forever (`retry_livelocks`).  Under a strongly fair scheduler it cannot: every fair run
  delivers external actions infinitely often.
* In the correct dining philosophers, every philosopher *will* eat infinitely often along
  every fair run (not merely *can* eat again).
-/

namespace AsyncLean.Examples

theorem retry_safe : retry.Safe := by async_decide

/-- Under fairness, the retry protocol never livelocks. -/
theorem retry_fair_progress (r : retry.toNet.lts.Run retry.M₀) (hfair : r.StronglyFair) :
    LTS.InfOften (fun n => ¬ retry.Internal (r.lab n)) :=
  r.infOften_external_of_progress (PNet.reachable_finite_of_bounded retry_safe) hfair
    (LTS.progress_of_liveLabel (l := ⟨0, by decide⟩) (by decide) (retry_live _))

theorem philosophers_safe : (philosophers 5 true).Safe := by async_decide

/-- Every philosopher eats infinitely often along every fair run. -/
theorem philosophers_eat_forever (r : (philosophers 5 true).toNet.lts.Run (philosophers 5 true).M₀)
    (hfair : r.StronglyFair) (t : Fin (philosophers 5 true).trans.length) :
    LTS.InfOften (fun n => r.lab n = t) :=
  r.infOften_label_of_live (PNet.reachable_finite_of_bounded philosophers_safe) hfair
    (philosophers_correct.2.2 t)

#assert_standard_axioms retry_fair_progress philosophers_eat_forever

end AsyncLean.Examples
