/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.AxiomAudit

/-!
# Example: compositional verification of two FIFOs

A `k`-stage FIFO accepts items on `in`, moves them internally (`t`) towards the output, and
delivers them on `out`; it has `2^k` reachable markings.  Connecting two FIFOs through the
channel `mid` gives `4^k` states.

Instead of exploring the composite, `async_minimize` replaces each FIFO by its minimal
quotient modulo branching bisimulation (with `t` and the channel `mid` hidden) — a counter
with `k + 1` states — certified by the kernel.  The composition of the two quotients is then
checked by `async_decide`.  The theory (`AsyncLean.LTS.Compose`) guarantees the result holds
for the original composite.
-/

namespace AsyncLean.Examples

/-- A `k`-stage FIFO with input label `inp` and output label `out`; place `2i` means stage `i`
is empty, `2i+1` that it is full. -/
def fifo (k : ℕ) (inp out : String) : PNet where
  places := 2 * k
  trans :=
    [{ name := inp, pre := [0], post := [1] }] ++
    (List.range (k - 1)).map (fun i =>
      { name := "t", pre := [2 * i + 1, 2 * i + 2], post := [2 * i, 2 * i + 3], internal := true }) ++
    [{ name := out, pre := [2 * k - 1], post := [2 * k - 2] }]
  init := (List.range k).flatMap fun _ => [1, 0]

/-- The channel between the two FIFOs. -/
def midSync (a : String) : Bool := a == "mid"

/-- Internal moves and the channel are not observable. -/
def hidden (a : String) : Bool := a == "t" || a == "mid"

/-- Two 6-stage FIFOs in series (4096 composite states) never deadlock and never livelock. -/
theorem twoFifos_ok :
    ((fifo 6 "in" "mid").named.par (fifo 6 "mid" "out").named midSync).toLTS.DeadlockFree
        ((fifo 6 "in" "mid").init, (fifo 6 "mid" "out").init) ∧
      ((fifo 6 "in" "mid").named.par (fifo 6 "mid" "out").named midSync).toLTS.LivelockFree
        (fun a => hidden a = true) ((fifo 6 "in" "mid").init, (fifo 6 "mid" "out").init) := by
  async_minimize        -- the first FIFO becomes a 7-state counter
  async_minimize right  -- and so does the second
  async_decide          -- 49 states remain

#assert_standard_axioms twoFifos_ok

end AsyncLean.Examples
