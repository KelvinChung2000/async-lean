/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.AffineK
import AsyncLean.Checker.FastPetri
import AsyncLean.Auto.StateEq

/-!
# Bit-parallel verification of bounded Petri nets

`PNet.checkBitmap` checks a net through a layout of fields (`AsyncLean.Checker.Affine`) and
a bitmap certificate (`AsyncLean.Checker.Bitmap`).  The literals it receives — the layout,
the table and the initial packed state — are compared once with the values computed from
the net, and the layout passes the structural check `PNet.layoutOk`.

`PNet.of_checkBitmap` then gives deadlock freedom, livelock freedom, liveness and, through
the layout, bounds on every place in a field: a component place is safe, a counter place
holds at most `2^w - 1` tokens (`PNet.bounded_of_checkBitmap`).
-/

namespace AsyncLean

namespace PNet

open Fast Aff Bitmap

variable (N : PNet)

/-- The initial place vector. -/
def initVec (p : ℕ) : ℕ := N.init.getD p 0

/-- `w.getD p 0`, by the recursors. -/
noncomputable def kget (w : List ℕ) (p : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun x _ rec p => Nat.rec (motive := fun _ => ℕ) x (fun p' _ => rec p') p) w p

/-- The weights `w` of the places of an arc list, with multiplicity. -/
noncomputable def kweight (w : List ℕ) (ps : List ℕ) : ℕ := ksum (kget w) ps

/-- **The potential conditions**: every transition of `dm` (numbered from `i`) strictly
decreases the potential of weights `w`, every transition of `km` does not increase it. -/
noncomputable def checkPotAux (w : List ℕ) (dm km : ℕ) (ts : List PTrans) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun t _ rec i => band
      (band (Bool.rec (motive := fun _ => Bool) true
          (Nat.blt (kweight w t.post) (kweight w t.pre)) (ktest dm i))
        (Bool.rec (motive := fun _ => Bool) true
          (Nat.ble (kweight w t.post) (kweight w t.pre)) (ktest km i)))
      (rec (Nat.succ i))) ts

/-- The potential conditions for the net. -/
noncomputable def checkPot (w : List ℕ) (dm km : ℕ) : Bool := checkPotAux w dm km N.trans 0

/-- **The bitmap check** for a net under the layout `L`, with the potentials of weights `wR`
(ranks: the internal transitions of `dR` decrease it, the others do not increase it) and `wD`
(distances: the transitions of `dD` decrease it, those of `kD` do not increase it). -/
noncomputable def checkBitmap (L : List LField) (k imask dR dD kD : ℕ) (wR wD : List ℕ)
    (dl ll lv : Bool) (s₀ : ℕ) (c : Bitmap.Cert) : Bool :=
  band (N.layoutOkK L) (band (Nat.beq imask (cond ll N.imask 0))
    (band (Nat.beq s₀ (kencV N.initVec L))
    (band (N.checkPot wR dR imask) (band (N.checkPot wD dD kD)
      (Bitmap.check (N.katable L) k imask dR dD kD N.trans.length dl lv s₀ c)))))

/-- The potential of a marking. -/
def pot (w : List ℕ) (M : Marking (Fin N.places)) : ℕ := ∑ p : Fin N.places, w.getD p.val 0 * M p

/-- Every place lies in a field bounding it by `K`. -/
def layoutBound (L : List LField) (K : ℕ) : Bool :=
  (List.range N.places).all fun p => L.any fun f =>
    f.ps.contains p && decide ((if f.comp then 1 else 2 ^ f.w - 1) ≤ K)

variable {N}

theorem wsum_congr {comp : Bool} {g g' : ℕ → ℕ} :
    ∀ {ps : List ℕ} (i : ℕ), (∀ p ∈ ps, g p = g' p) →
      LField.wsum comp g i ps = LField.wsum comp g' i ps
  | [], _, _ => rfl
  | p :: ps, i, h => by
    simp only [LField.wsum, h p List.mem_cons_self,
      wsum_congr (ps := ps) (i + 1) fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem encV_congr {g g' : ℕ → ℕ} : ∀ {L : List LField},
    (∀ f ∈ L, ∀ p ∈ f.ps, g p = g' p) → encV L g = encV L g'
  | [], _ => rfl
  | f :: L, h => by
    simp only [encV, LField.val, wsum_congr 0 (h f List.mem_cons_self),
      encV_congr (L := L) fun f' hf' => h f' (List.mem_cons_of_mem _ hf')]

theorem encL_M₀ {L : List LField} (hL : LayoutSpec N L) : N.encL L N.M₀ = encV L N.initVec := by
  refine encV_congr fun f hf p hp => ?_
  rw [vec_lt (hL.places f hf p hp)]; rfl

theorem kget_eq : ∀ (w : List ℕ) (p : ℕ), kget w p = w.getD p 0
  | [], _ => rfl
  | x :: w, 0 => rfl
  | x :: w, p + 1 => by
    change kget w p = _
    rw [kget_eq w p]; rfl

theorem kweight_eq (w ps : List ℕ) : kweight w ps = (ps.map fun p => w.getD p 0).sum := by
  unfold kweight
  rw [ksum_eq]
  congr 1
  exact List.map_congr_left fun p _ => kget_eq w p

theorem checkPotAux_spec {w : List ℕ} {dm km : ℕ} : ∀ {ts : List PTrans} {i₀ : ℕ},
    checkPotAux w dm km ts i₀ = true → ∀ j (hj : j < ts.length),
      (dm.testBit (i₀ + j) = true → kweight w ts[j].post < kweight w ts[j].pre) ∧
      (km.testBit (i₀ + j) = true → kweight w ts[j].post ≤ kweight w ts[j].pre)
  | [], _, _, j, hj => by simp at hj
  | t :: ts, i₀, h, j, hj => by
    change band (band (Bool.rec (motive := fun _ => Bool) true
          (Nat.blt (kweight w t.post) (kweight w t.pre)) (ktest dm i₀))
        (Bool.rec (motive := fun _ => Bool) true
          (Nat.ble (kweight w t.post) (kweight w t.pre)) (ktest km i₀)))
      (checkPotAux w dm km ts (Nat.succ i₀)) = true at h
    obtain ⟨h1, h2⟩ := band_eq.1 h
    obtain ⟨hd, hk⟩ := band_eq.1 h1
    cases j with
    | zero =>
      refine ⟨fun hb => ?_, fun hb => ?_⟩
      · rw [Nat.add_zero, ← ktest_eq] at hb; rw [hb] at hd; exact blt_t hd
      · rw [Nat.add_zero, ← ktest_eq] at hb; rw [hb] at hk; exact ble_t hk
    | succ j =>
      have := checkPotAux_spec h2 j (by simpa using hj)
      rw [show Nat.succ i₀ + j = i₀ + (j + 1) by omega] at this
      exact this

theorem pot_fire (hwf : N.wf = true) (w : List ℕ) {M : Marking (Fin N.places)}
    {t : Fin N.trans.length} (hen : N.toNet.Enabled M t) :
    N.pot w (N.toNet.fire M t) + kweight w (N.tr t).pre = N.pot w M + kweight w (N.tr t).post := by
  rw [kweight_eq, kweight_eq, sum_map_eq_sum_count _ ((wf_spec hwf).2 t).1,
    sum_map_eq_sum_count _ ((wf_spec hwf).2 t).2]
  unfold pot
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := hen p
  change (N.tr t).pre.count p.val ≤ M p at hp
  simp only [Net.fire, smul_eq_mul]
  change w.getD p.val 0 * (M p - (N.tr t).pre.count p.val + (N.tr t).post.count p.val) +
    (N.tr t).pre.count p.val * w.getD p.val 0 = w.getD p.val 0 * M p +
    (N.tr t).post.count p.val * w.getD p.val 0
  obtain ⟨d, hd⟩ : ∃ d, M p = (N.tr t).pre.count p.val + d :=
    ⟨M p - (N.tr t).pre.count p.val, by omega⟩
  rw [hd, Nat.add_sub_cancel_left]
  ring

theorem pot_step (hwf : N.wf = true) {w : List ℕ} {dm km : ℕ} (hc : N.checkPot w dm km = true)
    {M M' : Marking (Fin N.places)} {t : Fin N.trans.length} (hst : N.toNet.lts.step M t M') :
    (dm.testBit t.val = true → N.pot w M' < N.pot w M) ∧
      (km.testBit t.val = true → N.pot w M' ≤ N.pot w M) := by
  obtain ⟨hen, rfl⟩ := hst
  have hf := pot_fire hwf w hen
  have := checkPotAux_spec hc t.val (by simp)
  rw [Nat.zero_add] at this
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have := this.1 hb; change kweight w (N.tr t).post < kweight w (N.tr t).pre at this; omega
  · have := this.2 hb; change kweight w (N.tr t).post ≤ kweight w (N.tr t).pre at this; omega

theorem of_checkBitmap {L : List LField} {k imask dR dD kD s₀ : ℕ} {wR wD : List ℕ}
    {dl ll lv : Bool} {c : Bitmap.Cert}
    (h : N.checkBitmap L k imask dR dD kD wR wD dl ll lv s₀ c = true) :
    (dl = true → N.toNet.lts.DeadlockFree N.M₀) ∧
      (ll = true → N.toNet.lts.LivelockFree N.Internal N.M₀) ∧
      (lv = true → N.toNet.lts.Live N.M₀) ∧
      ∀ M, N.toNet.lts.Reachable N.M₀ M → N.GoodL L M := by
  unfold checkBitmap at h
  obtain ⟨hL, h⟩ := band_eq.1 h
  obtain ⟨hk, h⟩ := band_eq.1 h
  obtain ⟨hs₀, h⟩ := band_eq.1 h
  obtain ⟨hpR, h⟩ := band_eq.1 h
  obtain ⟨hpD, hc⟩ := band_eq.1 h
  have hL := layoutSpec_of_layoutOkK hL
  rw [katable_eq, Nat.eq_of_beq_eq_true hs₀, kencV_eq, ← encL_M₀ hL] at hc
  obtain ⟨hd, hl, hv, hg⟩ := Bitmap.of_check (encodesL hL) Fin.val_injective (N.pot wR) (N.pot wD)
    (fun M t M' hst hi => let h := pot_step hL.wf hpR hst; ⟨h.2 hi, h.1⟩)
    (fun M t M' hst => pot_step hL.wf hpD hst) (goodL_M₀ hL) hc
  refine ⟨hd, fun hll => ?_, fun hlv t => hv hlv t t.isLt, hg⟩
  rw [Nat.eq_of_beq_eq_true hk, hll] at hl
  have : (fun t : Fin N.trans.length => (cond true N.imask 0).testBit t.val = true) =
      fun t => (N.tr t).internal = true := by
    funext t; rw [Bool.cond_true, testBit_imask]
  rw [this] at hl
  exact hl

/-- **A successful bitmap check proves the design correct.** -/
theorem correct_of_checkBitmap {L : List LField} {k imask dR dD kD s₀ : ℕ} {wR wD : List ℕ}
    {c : Bitmap.Cert} (h : N.checkBitmap L k imask dR dD kD wR wD true true true s₀ c = true) : N.Correct :=
  let h := of_checkBitmap h
  ⟨h.1 rfl, h.2.1 rfl, h.2.2.1 rfl⟩

theorem deadlockFree_of_checkBitmap {L : List LField} {k imask dR dD kD s₀ : ℕ} {wR wD : List ℕ}
    {ll lv : Bool} {c : Bitmap.Cert} (h : N.checkBitmap L k imask dR dD kD wR wD true ll lv s₀ c = true) :
    N.toNet.lts.DeadlockFree N.M₀ :=
  (of_checkBitmap h).1 rfl

theorem livelockFree_of_checkBitmap {L : List LField} {k imask dR dD kD s₀ : ℕ} {wR wD : List ℕ}
    {dl lv : Bool} {c : Bitmap.Cert} (h : N.checkBitmap L k imask dR dD kD wR wD dl true lv s₀ c = true) :
    N.toNet.lts.LivelockFree N.Internal N.M₀ :=
  (of_checkBitmap h).2.1 rfl

theorem live_of_checkBitmap {L : List LField} {k imask dR dD kD s₀ : ℕ} {wR wD : List ℕ} {dl ll : Bool}
    {c : Bitmap.Cert} (h : N.checkBitmap L k imask dR dD kD wR wD dl ll true s₀ c = true) :
    N.toNet.lts.Live N.M₀ :=
  (of_checkBitmap h).2.2.1 rfl

/-- **Bounds from a bitmap check**: every place lies in a field bounding it by `K`. -/
theorem bounded_of_checkBitmap {L : List LField} {k imask dR dD kD s₀ K : ℕ} {wR wD : List ℕ}
    {dl ll lv : Bool} {c : Bitmap.Cert} (h : N.checkBitmap L k imask dR dD kD wR wD dl ll lv s₀ c = true)
    (hb : N.layoutBound L K = true) : N.Bounded K := by
  intro M hM p
  have hg := (of_checkBitmap h).2.2.2 M hM
  simp only [layoutBound, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    List.contains_iff_mem, decide_eq_true_eq] at hb
  obtain ⟨f, hf, hp, hK⟩ := hb p.val p.isLt
  exact le_trans (goodL_bound hg hf hp) hK

end PNet

end AsyncLean
