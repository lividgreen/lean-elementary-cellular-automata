module

public import ECA.ReproductionBracket
public import ECA.RationalRayRule90
public import ECA.RationalRayPairs

/-!
# Rays of rules `60` and `102` from the single seed
([RuleSpace] §5, transferring Proposition 5.1)

From the single seed, rule `60` is rule `90` sheared and rule `102` is the mirror image of rule
`60`. [RuleSpace] §5 Proposition 5.1 makes every ray of rule `90` from the single seed at a speed
strictly between rest and one not eventually periodic, by a one past every step and zero runs of
every length past every step. This file states the same two conditions for rule `60` and the
mirror relation for rule `102`, proves all three conditions and the shear, and so proves that the
rays of both rules are not eventually periodic; the forms conditional on the three conditions are
kept beside the unconditional ones.

## Main results

* `F60LateOnes` — along every ray of rule `60` from the single seed at a speed strictly between
  rest and one, from any cell, a one is read past every step.
* `F60LateZeroRuns` — along every ray at a speed below one, from any cell, a run of zeros of
  every length is read past every step.
* `F102MirrorSingle` — rule `102` from the single seed is the mirror image of rule `60`.
* `f60_single_apply_eq_f90` — rule `60` from the single seed is rule `90` sheared: its value at
  cell `i` and step `t` is rule `90`'s at cell `2 i - t`.
* `f102MirrorSingle` — the mirror relation holds.
* `f60LateZeroRuns` — the zero-runs condition holds, by the shear and [RuleSpace] §5
  Proposition 5.1(ii)'s light-cone argument at a large power of two.
* `f60LateOnes` — the ones condition holds: a pair of naturals with no shared binary digit lies on
  the ray, through the late disjoint pairs of rule `90` at the speed `2 p - q` over `q`, its
  mirror at `q - 2 p` over `q`, or the line `a - b = 2 e - 1` at the speed `1 / 2`.
* `not_eventuallyPeriodic_observedRationalRay_f60_single` and
  `not_eventuallyPeriodic_mirrorRay_f102_single` — **a ray of rule `60`, and the mirror ray of
  rule `102`, from the single seed at a speed strictly between rest and one is not eventually
  periodic**, from every cell; `not_eventuallyPeriodic_observedRationalRay_f60_single_nonvacuous`
  meets the speed hypotheses at speed `1 / 2`.
* `not_eventuallyPeriodic_observedRationalRay_f60_single_of` and
  `not_eventuallyPeriodic_mirrorRay_f102_single_of` — the conditional forms: given the ones
  condition and the zero-runs condition (and, for rule `102`, the mirror relation), the same
  conclusions.
* `not_F60LateZeroRuns_of_zero_speed` — **guard**: the zero-runs condition fails when speed zero
  is admitted.
* `eventuallyPeriodic_observedRationalRay_f60_single_one` and
  `eventuallyPeriodic_observedRationalRay_f60_single_zero` — **guards**: at speed one and at
  speed zero from cell `0` the ray of rule `60` reads `1` at every step, so the speed
  hypotheses of the conditional statements are needed.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- Along every ray of rule 60 from the single seed at a speed strictly between rest and one,
from any cell, a one is read past every step. -/
def F60LateOnes : Prop :=
  ∀ p q : ℕ, 0 < p → p < q → ∀ e : ℤ, ∀ T : ℕ, ∃ t, T ≤ t ∧
    observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t = 1

/-- Along every ray of rule 60 from the single seed at a speed strictly between rest and one,
from any cell, a run of zeros of every length is read past every step. -/
def F60LateZeroRuns : Prop :=
  ∀ p q : ℕ, 0 < p → p < q → ∀ e : ℤ, ∀ n T : ℕ, ∃ t₀, T ≤ t₀ ∧ ∀ r < n,
    observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e
      (t₀ + r) = 0

/-- Rule 102 from the single seed is the mirror of rule 60. -/
def F102MirrorSingle : Prop :=
  ∀ (t : ℕ) (i : ℤ),
    ((finRule f102 hq102)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i =
      ((finRule f60 hq60)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-i)

/-- **A ray of rule `60` from the single seed, at a speed strictly between rest and one, is not
eventually periodic**, given a one past every step and zero runs of every length past every step
along every such ray (the transfer of [RuleSpace] §5 Proposition 5.1). -/
theorem not_eventuallyPeriodic_observedRationalRay_f60_single_of
    (h1 : F60LateOnes) (h0 : F60LateZeroRuns) (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_of_late_one_of_late_zero_runs _ (h1 p q hp hpq e) (h0 p q hp hpq e)

/-- **The mirror ray of rule `102` from the single seed, at a speed strictly between rest and one,
is not eventually periodic**, given the conditions of the ray of rule `60` and that rule `102` is
the mirror image of rule `60` from the single seed. -/
theorem not_eventuallyPeriodic_mirrorRay_f102_single_of
    (h1 : F60LateOnes) (h0 : F60LateZeroRuns) (hm : F102MirrorSingle)
    (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (fun t => ((finRule f102 hq102)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (e - ((p * t / q : ℕ) : ℤ))) := by
  have h := not_eventuallyPeriodic_observedRationalRay_f60_single_of h1 h0 p q hp hpq (-e)
  have hfun : (fun t => ((finRule f102 hq102)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (e - ((p * t / q : ℕ) : ℤ))) =
      observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q (-e) := by
    funext t
    rw [hm]
    unfold observedRationalRay
    congr 1
    ring
  rw [hfun]
  exact h

/-- Rule `60` from the single seed: no cell to the left of the origin is ever occupied, and the
origin is occupied at every step. -/
private theorem f60_single_left (t : ℕ) :
    (∀ i : ℤ, i < 0 →
      ((finRule f60 hq60)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i = 0) ∧
    ((finRule f60 hq60)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 1 := by
  induction t with
  | zero =>
    refine ⟨fun i hi => ?_, by simp⟩
    simp [hi.ne]
  | succ t ih =>
    obtain ⟨hl, h0⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [finRule_apply]
      have h2 := hl (i - 1) (by omega)
      rw [sub_eq_add_neg] at h2
      simp [f60, hl i hi, h2, sub_eq_add_neg]
    · rw [finRule_apply]
      have h2 := hl (-1) (by omega)
      simp [f60, h0, h2]

/-- Rule `60` from the single seed: no cell to the right of the front at `t` is occupied at step
`t`, and the front is occupied. -/
private theorem f60_single_front (t : ℕ) :
    (∀ i : ℤ, (t : ℤ) < i →
      ((finRule f60 hq60)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i = 0) ∧
    ((finRule f60 hq60)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (t : ℤ) = 1 := by
  induction t with
  | zero =>
    refine ⟨fun i hi => ?_, by simp⟩
    have : (0 : ℤ) ≠ i := by push_cast at hi; omega
    simp [this]
  | succ t ih =>
    obtain ⟨hr, hf⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [finRule_apply]
      push_cast at hi
      have h2 := hr (i - 1) (by omega)
      rw [sub_eq_add_neg] at h2
      simp [f60, hr i (by omega), h2, sub_eq_add_neg]
    · rw [finRule_apply]
      push_cast
      have h2 := hr ((t : ℤ) + 1) (by omega)
      simp [f60, hf, h2]

/-- **Guard: at speed one the ray of rule `60` from the single seed reads `1` at every step**,
so it is eventually periodic; the speed hypothesis `p < q` is needed. -/
theorem eventuallyPeriodic_observedRationalRay_f60_single_one :
    (∀ t, observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      1 1 0 t = 1) ∧
    DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 1 0) := by
  have hall : ∀ t, observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      1 1 0 t = 1 := by
    intro t
    unfold observedRationalRay
    simpa using (f60_single_front t).2
  exact ⟨hall, 1, 0, one_pos, fun u _ => by rw [hall, hall]⟩

/-- **Guard: at speed zero the ray of rule `60` from the single seed at cell `0` reads `1` at
every step**, so it is eventually periodic; the speed hypothesis `0 < p` is needed. -/
theorem eventuallyPeriodic_observedRationalRay_f60_single_zero :
    (∀ t, observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      0 1 0 t = 1) ∧
    DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1 0) := by
  have hall : ∀ t, observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      0 1 0 t = 1 := by
    intro t
    unfold observedRationalRay
    simpa using (f60_single_left t).2
  exact ⟨hall, 1, 0, one_pos, fun u _ => by rw [hall, hall]⟩

/-- **Guard: the zero-runs condition on rays of rule `60` fails when speed zero is admitted.**
Cell `0` reads `1` at every step, so the hypothesis `0 < p` is needed. -/
theorem not_F60LateZeroRuns_of_zero_speed :
    ¬ (∀ p q : ℕ, p < q → ∀ e : ℤ, ∀ n T : ℕ, ∃ t₀, T ≤ t₀ ∧ ∀ r < n,
      observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e
        (t₀ + r) = 0) := by
  intro h
  obtain ⟨t₀, -, hr⟩ := h 0 1 one_pos 0 1 0
  have := hr 0 one_pos
  rw [add_zero, eventuallyPeriodic_observedRationalRay_f60_single_zero.1] at this
  exact one_ne_zero this

/-- **Rule `60` from the single seed is rule `90` sheared** ([RuleSpace] §5): the value of
rule `60` at cell `i` and step `t` is the value of rule `90` at cell `2 i - t`. -/
theorem f60_single_apply_eq_f90 (t : ℕ) (i : ℤ) :
    ((finRule f60 hq60)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i =
      ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (2 * i - t) := by
  induction t generalizing i with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Finsupp.single_apply]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; push_cast at h2; omega)
  | succ t ih =>
      rw [Function.iterate_succ_apply', finRule_apply, f60, ih (i - 1), ih i,
        Function.iterate_succ_apply', finRule_apply, f90,
        show (2 * i - ((t + 1 : ℕ) : ℤ)) - 1 = 2 * (i - 1) - t by push_cast; ring,
        show (2 * i - ((t + 1 : ℕ) : ℤ)) + 1 = 2 * i - t by push_cast; ring]

/-- **Rule `102` from the single seed is the mirror image of rule `60`**: the two rules read the
same value at cells `i` and `-i`. -/
theorem f102MirrorSingle : F102MirrorSingle := by
  intro t i
  induction t generalizing i with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Finsupp.single_apply]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  | succ t ih =>
      rw [Function.iterate_succ_apply', finRule_apply, f102, ih i, ih (i + 1),
        Function.iterate_succ_apply', finRule_apply, f60,
        show -i - 1 = -(i + 1) by ring, add_comm]

/-- **Late zero runs along every ray of rule `60` at a speed strictly between rest and one**
(the transfer of [RuleSpace] §5 Proposition 5.1(ii) through the shear
`f60_single_apply_eq_f90`): at a large power of two `2 ^ B` the sheared cell lies outside both
light cones of the two translated copies into which rule `90` splits. -/
theorem f60LateZeroRuns : F60LateZeroRuns := by
  intro p q hp hpq e n T
  set B : ℕ := T + n + q * e.natAbs + q * n + q with hB
  have hlt : B < 2 ^ B := Nat.lt_two_pow_self
  refine ⟨2 ^ B, by omega, ?_⟩
  intro r hr
  unfold observedRationalRay
  rw [f60_single_apply_eq_f90, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  have hk : q * (p * (2 ^ B + r) / q) ≤ p * (2 ^ B + r) := Nat.mul_div_le _ _
  have hk' : p * (2 ^ B + r) < q * (p * (2 ^ B + r) / q + 1) := by
    exact Nat.lt_mul_div_succ (p * (2 ^ B + r)) (show 0 < q by omega)
  set k : ℕ := p * (2 ^ B + r) / q with hkdef
  have hkz : (q : ℤ) * k ≤ p * (2 ^ B + r) := by exact_mod_cast hk
  have hkz' : (p : ℤ) * (2 ^ B + r) < q * (k + 1) := by exact_mod_cast hk'
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have he2 : e ≤ (e.natAbs : ℤ) := by rw [habs]; exact le_abs_self e
  have hpq' : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hNz : (B : ℤ) < 2 ^ B := by exact_mod_cast hlt
  have hBz : (B : ℤ) = T + n + q * e.natAbs + q * n + q := by rw [hB]; push_cast; ring
  have hrz : (r : ℤ) < n := by exact_mod_cast hr
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hT0 : (0 : ℤ) ≤ T := by positivity
  have hqe : (q : ℤ) * -(e.natAbs : ℤ) ≤ q * e := mul_le_mul_of_nonneg_left he1 hq0
  have hqe' : (q : ℤ) * e ≤ q * (e.natAbs : ℤ) := mul_le_mul_of_nonneg_left he2 hq0
  have hqr : (q : ℤ) * r ≤ q * n := mul_le_mul_of_nonneg_left hrz.le hq0
  have hq1 : (1 : ℤ) ≤ q := by omega
  have hM : (0 : ℤ) ≤ 2 ^ B + r := by positivity
  have hpt : (2 ^ B + r : ℤ) ≤ p * (2 ^ B + r) := by nlinarith
  have hpt' : (p : ℤ) * (2 ^ B + r) + (2 ^ B + r) ≤ q * (2 ^ B + r) :=
    by nlinarith
  -- lower: r < e + k
  have hA : (r : ℤ) < e + k := by
    have : (q : ℤ) * r < q * (e + k) := by nlinarith
    exact lt_of_mul_lt_mul_left this hq0
  -- upper: e + k < 2 ^ B
  have hC : (e : ℤ) + k < 2 ^ B := by
    have : (q : ℤ) * (e + k) < q * 2 ^ B := by nlinarith
    exact lt_of_mul_lt_mul_left this hq0
  have z1 := f90_single_apply_eq_zero_of_lt r (2 * (e + k) - (2 ^ B + r) - 2 ^ B)
    (by rw [lt_abs]; right; linarith)
  have z2 := f90_single_apply_eq_zero_of_lt r (2 * (e + k) - (2 ^ B + r) + 2 ^ B)
    (by rw [lt_abs]; left; linarith)
  rw [f90_iterate_two_pow_add]
  rw [z1, z2, add_zero]

/-- A cell of the ray of rule `60` that is the left member of a pair `(a, b)` with no shared binary
digit, read at step `a + b`, holds a one. -/
private theorem ray_f60_eq_one_of_disjoint (p q : ℕ) (e : ℤ) (a b : ℕ) (hab : a &&& b = 0)
    (h : (a : ℤ) = e + ((p * (a + b) / q : ℕ) : ℤ)) :
    observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e (a + b)
      = 1 := by
  unfold observedRationalRay
  rw [← h, f60_single_apply_eq_f90]
  have := oneOfDisjoint a b hab
  rw [show 2 * (a : ℤ) - ((a + b : ℕ) : ℤ) = (a : ℤ) - b by push_cast; ring]
  exact this

/-- A cell `a` between two floor bounds is the ray's cell at step `a + b`. -/
private theorem cell_eq_of_bounds (p q : ℕ) (hq : 0 < q) (e : ℤ) (a b : ℕ)
    (h1 : (q : ℤ) * (a - e) ≤ p * (a + b)) (h2 : (p : ℤ) * (a + b) < q * (a - e + 1)) :
    (a : ℤ) = e + ((p * (a + b) / q : ℕ) : ℤ) := by
  set m : ℕ := p * (a + b) / q with hm
  have g1 : q * m ≤ p * (a + b) := Nat.mul_div_le _ _
  have g2 : p * (a + b) < q * (m + 1) := Nat.lt_mul_div_succ _ hq
  have g1' : (q : ℤ) * m ≤ p * (a + b) := by exact_mod_cast g1
  have g2' : (p : ℤ) * (a + b) < q * (m + 1) := by exact_mod_cast g2
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have i1 : (q : ℤ) * (a - e) < q * (m + 1) := lt_of_le_of_lt h1 g2'
  have i2 : (q : ℤ) * m < q * (a - e + 1) := lt_of_le_of_lt g1' h2
  have j1 := lt_of_mul_lt_mul_left i1 hq'.le
  have j2 := lt_of_mul_lt_mul_left i2 hq'.le
  omega

/-- Two naturals, one a power of two and the other below it, share no binary digit. -/
private theorem and_eq_zero_of_lt_two_pow (K b : ℕ) (hb : b < 2 ^ K) : 2 ^ K &&& b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : K = i
  · subst hi
    rw [Nat.testBit_lt_two_pow hb]
    simp
  · simp [hi]

/-- **A one late on every ray of rule `60` from the single seed, at a speed strictly between rest
and one, from any cell** (the transfer of [RuleSpace] §5 Proposition 5.1(i) through the shear
`f60_single_apply_eq_f90`): a pair of naturals with no shared binary digit lies on the ray of
rule `90` at the speed `2 p - q` over `q` when `q < 2 p`, on the mirrored ray at `q - 2 p` over `q`
when `2 p < q`, and on the line `a - b = 2 e - 1` when `2 p = q`, and rule `60` reads a one at the
left member of such a pair, at the step of their sum. -/
theorem f60LateOnes : F60LateOnes := by
  intro p q hp hpq e T
  have hq : 0 < q := by omega
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  rcases lt_trichotomy q (2 * p) with h | h | h
  · -- `q < 2 p`
    obtain ⟨a, b, hab, hT, hon⟩ := lateDisjointOnRay (2 * p - q) q (by omega) (by omega) (2 * e) T
    rw [onRay_iff _ _ hq] at hon
    obtain ⟨l, u⟩ := hon
    have hc : (((2 * p - q : ℕ) : ℤ)) = 2 * p - q := by omega
    rw [hc] at l u
    refine ⟨a + b, hT, ray_f60_eq_one_of_disjoint p q e a b hab ?_⟩
    apply cell_eq_of_bounds p q hq e a b <;> nlinarith
  · -- `q = 2 p`
    subst h
    have hd : (2 * e - 1 : ℤ) ≠ 0 := by omega
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · -- `a - b = 2 e - 1 < 0`: swap the roles
      set d : ℕ := (1 - 2 * e).toNat with hdd
      have hd1 : (d : ℤ) = 1 - 2 * e := by omega
      set K : ℕ := T + d with hK
      have hlt : K < 2 ^ K := Nat.lt_two_pow_self
      have hb : 2 ^ K - d < 2 ^ K := by omega
      refine ⟨2 ^ K - d + 2 ^ K, by omega, ?_⟩
      have hand : (2 ^ K - d) &&& 2 ^ K = 0 := by
        rw [Nat.land_comm]; exact and_eq_zero_of_lt_two_pow K _ hb
      apply ray_f60_eq_one_of_disjoint p (2 * p) e _ _ hand
      have hcast : ((2 ^ K - d : ℕ) : ℤ) = 2 ^ K - d := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hs : p * (2 ^ K - d + 2 ^ K) / (2 * p) = (2 ^ K - d + 2 ^ K) / 2 := by
        rw [show p * (2 ^ K - d + 2 ^ K) = (2 ^ K - d + 2 ^ K) * p by ring]
        exact Nat.mul_div_mul_right _ _ hp
      rw [hs]
      have : (2 ^ K - d + 2 ^ K) / 2 = 2 ^ K - (d + 1) / 2 := by omega
      rw [this]
      have hodd : (d + 1) / 2 * 2 = d + 1 := by omega
      have h2 : (((2 ^ K - (d + 1) / 2 : ℕ)) : ℤ) = 2 ^ K - ((d + 1) / 2 : ℕ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast, h2]
      have : (((d + 1) / 2 : ℕ) : ℤ) * 2 = d + 1 := by exact_mod_cast hodd
      omega
    · -- `a - b = 2 e - 1 > 0`
      set d : ℕ := (2 * e - 1).toNat with hdd
      have hd1 : (d : ℤ) = 2 * e - 1 := by omega
      set K : ℕ := T + d with hK
      have hlt : K < 2 ^ K := Nat.lt_two_pow_self
      have hb : 2 ^ K - d < 2 ^ K := by omega
      refine ⟨2 ^ K + (2 ^ K - d), by omega, ?_⟩
      have hand : 2 ^ K &&& (2 ^ K - d) = 0 := and_eq_zero_of_lt_two_pow K _ hb
      apply ray_f60_eq_one_of_disjoint p (2 * p) e _ _ hand
      have hs : p * (2 ^ K + (2 ^ K - d)) / (2 * p) = (2 ^ K + (2 ^ K - d)) / 2 := by
        rw [show p * (2 ^ K + (2 ^ K - d)) = (2 ^ K + (2 ^ K - d)) * p by ring]
        exact Nat.mul_div_mul_right _ _ hp
      rw [hs]
      have h2 : (((2 ^ K + (2 ^ K - d)) / 2 : ℕ) : ℤ) * 2 + 1 = (2 ^ K + (2 ^ K - d) : ℕ) := by
        have : (2 ^ K + (2 ^ K - d)) % 2 = 1 := by omega
        have h3 := Nat.div_add_mod (2 ^ K + (2 ^ K - d)) 2
        have h4 : ((2 ^ K + (2 ^ K - d) : ℕ) : ℤ) = ((2 ^ K + (2 ^ K - d)) / 2 : ℕ) * 2 + 1 := by
          omega
        omega
      have hcast : ((2 ^ K - d : ℕ) : ℤ) = 2 ^ K - d := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [hcast] at h2 ⊢
      omega
  · -- `2 p < q`
    obtain ⟨a, b, hab, hT, hon⟩ := lateDisjointOnRay (q - 2 * p) q (by omega) (by omega)
      (1 - 2 * e) T
    rw [onRay_iff _ _ hq] at hon
    obtain ⟨l, u⟩ := hon
    have hc : (((q - 2 * p : ℕ) : ℤ)) = q - 2 * p := by omega
    rw [hc] at l u
    refine ⟨b + a, by omega, ray_f60_eq_one_of_disjoint p q e b a
      (by rw [Nat.land_comm]; exact hab) ?_⟩
    apply cell_eq_of_bounds p q hq e b a <;> nlinarith

/-- **A ray of rule `60` from the single seed, at a speed strictly between rest and one, from any
cell, is not eventually periodic** ([RuleSpace] §5 Proposition 5.1 transferred through the shear
`f60_single_apply_eq_f90`). -/
theorem not_eventuallyPeriodic_observedRationalRay_f60_single
    (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_observedRationalRay_f60_single_of f60LateOnes f60LateZeroRuns p q hp hpq e

/-- **The mirror ray of rule `102` from the single seed, at a speed strictly between rest and one,
from any cell, is not eventually periodic**: rule `102` is the mirror image of rule `60` from the
single seed. -/
theorem not_eventuallyPeriodic_mirrorRay_f102_single
    (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (fun t => ((finRule f102 hq102)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (e - ((p * t / q : ℕ) : ℤ))) :=
  not_eventuallyPeriodic_mirrorRay_f102_single_of f60LateOnes f60LateZeroRuns f102MirrorSingle
    p q hp hpq e

/-- **Joint satisfiability** of the speed hypotheses of the statement on rule `60`: the ray at
speed `1 / 2` from cell zero is not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f60_single_nonvacuous :
    0 < 1 ∧ 1 < 2 ∧
      ¬ DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 0) :=
  ⟨by decide, by decide,
    not_eventuallyPeriodic_observedRationalRay_f60_single 1 2 (by decide) (by decide) 0⟩

end ECA

/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f60_single_of' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f60_single_of

/-- info: 'ECA.not_eventuallyPeriodic_mirrorRay_f102_single_of' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_mirrorRay_f102_single_of

/-- info: 'ECA.eventuallyPeriodic_observedRationalRay_f60_single_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedRationalRay_f60_single_one

/-- info: 'ECA.eventuallyPeriodic_observedRationalRay_f60_single_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedRationalRay_f60_single_zero

/-- info: 'ECA.not_F60LateZeroRuns_of_zero_speed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_F60LateZeroRuns_of_zero_speed

/-- info: 'ECA.f60_single_apply_eq_f90' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f60_single_apply_eq_f90

/-- info: 'ECA.f102MirrorSingle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f102MirrorSingle

/-- info: 'ECA.f60LateZeroRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f60LateZeroRuns

/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f60_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f60_single

/-- info: 'ECA.not_eventuallyPeriodic_mirrorRay_f102_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_mirrorRay_f102_single

/-- info: 'ECA.f60LateOnes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f60LateOnes

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f60_single_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f60_single_nonvacuous
