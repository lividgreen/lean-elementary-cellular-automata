module

public import ECA.RationalRayRule90
public import ECA.ObservedColumn
public import ECA.Doubling
public import ECA.RationalRaySeeds
public import ECA.RationalRayPairs
public import ECA.ReproductionBracket

/-!
# Rays of rule `22` from the single seed
([RuleSpace] §5, transferring Proposition 5.1 and Proposition 5.18)

[RuleSpace] §5 Proposition 5.1 makes every ray of rule `90` from the single seed at a speed
strictly between rest and one not eventually periodic, by a one past every step and zero runs of
every length past every step, and Proposition 5.18 carries the statement to rules `60` and `102`.
This file states the same two conditions for rule `22` and the symmetry of its orbit about the
seed, proves all three, and so proves that the rays of rule `22` are not eventually periodic; the
forms conditional on the three are kept beside the unconditional ones. The transfer goes through
the closed form of Chan-López and Martín-Ruiz (2026, §3): from the single seed, rule `22` is rule
`90` at even steps and rule `90` plus its previous row at odd steps.

## Main results

* `F22LateOnes` — along every ray of rule `22` from the single seed at a speed strictly between
  rest and one, from any cell, a one is read past every step.
* `F22LateZeroRuns` — along every such ray, from any cell, a run of zeros of every length is read
  past every step.
* `F22SymmSingle` — rule `22` from the single seed is symmetric about the seed.
* `f22_single_apply_eq_f90` — rule `22` from the single seed is rule `90` plus, at odd steps,
  rule `90`'s previous row.
* `f22LateOnes` — the ones condition holds: a one of rule `90` read on the ray at a late step is
  at a cell and step of one parity, so the previous row adds nothing there.
* `f22LateZeroRuns` — the zero-runs condition holds, by [RuleSpace] §5 Proposition 5.1(ii)'s
  light-cone argument at a large power of two, for the step and for the step before it.
* `f22SymmSingle` — the symmetry holds, the rule being symmetric in its outer inputs.
* `not_eventuallyPeriodic_observedRationalRay_f22_single` and
  `not_eventuallyPeriodic_mirrorRay_f22_single` — **a ray of rule `22` from the single seed at a
  speed strictly between rest and one is not eventually periodic**, from every cell, toward either
  side; `not_eventuallyPeriodic_observedRationalRay_f22_single_nonvacuous` meets the speed
  hypotheses at speed `1 / 2`.
* `not_eventuallyPeriodic_observedRationalRay_f22_single_of` and
  `not_eventuallyPeriodic_mirrorRay_f22_single_of` — the conditional forms: **given the ones
  condition and the zero-runs condition (and, for the mirror ray, the symmetry), a ray of rule
  `22` from the single seed at a speed strictly between rest and one is not eventually periodic**,
  from every cell, toward either side.
* `eventuallyPeriodic_observedRationalRay_f22_single_one` and
  `eventuallyPeriodic_observedRationalRay_f22_single_zero` — **guards**: at speed one from cell
  `0` the ray of rule `22` reads `1` at every step, and at speed zero from cell `0` it reads `0`
  from step two on, so the speed hypotheses are needed.
* `not_F22LateOnes_of_zero_speed` — **guard**: the ones condition fails when speed zero is
  admitted.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- Along every ray of rule 22 from the single seed at a speed strictly between rest and one,
from any cell, a one is read past every step. -/
def F22LateOnes : Prop :=
  ∀ p q : ℕ, 0 < p → p < q → ∀ e : ℤ, ∀ T : ℕ, ∃ t, T ≤ t ∧
    observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t = 1

/-- Along every ray of rule 22 from the single seed at a speed strictly between rest and one,
from any cell, a run of zeros of every length is read past every step. -/
def F22LateZeroRuns : Prop :=
  ∀ p q : ℕ, 0 < p → p < q → ∀ e : ℤ, ∀ n T : ℕ, ∃ t₀, T ≤ t₀ ∧ ∀ r < n,
    observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e
      (t₀ + r) = 0

/-- Rule 22 from the single seed is symmetric about the seed. -/
def F22SymmSingle : Prop :=
  ∀ (t : ℕ) (i : ℤ),
    ((finRule f22 hq22)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-i) =
      ((finRule f22 hq22)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i

/-- **A ray of rule `22` from the single seed, at a speed strictly between rest and one, is not
eventually periodic**, given a one past every step and zero runs of every length past every step
along every such ray (the form of [RuleSpace] §5 Proposition 5.1 at rule `22`). -/
theorem not_eventuallyPeriodic_observedRationalRay_f22_single_of
    (h1 : F22LateOnes) (h0 : F22LateZeroRuns) (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_of_late_one_of_late_zero_runs _ (h1 p q hp hpq e) (h0 p q hp hpq e)

/-- **The ray of rule `22` from the single seed toward decreasing cells, at a speed strictly
between rest and one, is not eventually periodic**, given the conditions of the ray toward
increasing cells and that rule `22` from the single seed is symmetric about the seed. -/
theorem not_eventuallyPeriodic_mirrorRay_f22_single_of
    (h1 : F22LateOnes) (h0 : F22LateZeroRuns) (hs : F22SymmSingle)
    (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (fun t => ((finRule f22 hq22)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (e - ((p * t / q : ℕ) : ℤ))) := by
  have h := not_eventuallyPeriodic_observedRationalRay_f22_single_of h1 h0 p q hp hpq (-e)
  have hfun : (fun t => ((finRule f22 hq22)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (e - ((p * t / q : ℕ) : ℤ))) =
      observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q (-e) := by
    funext t
    rw [← hs]
    unfold observedRationalRay
    congr 1
    ring
  rw [hfun]
  exact h

/-- Rule `22` from the single seed: no cell to the right of the front at `t` is occupied at step
`t`, and the front is occupied. -/
private theorem f22_single_front (t : ℕ) :
    (∀ i : ℤ, (t : ℤ) < i →
      ((finRule f22 hq22)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i = 0) ∧
    ((finRule f22 hq22)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (t : ℤ) = 1 := by
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
      rw [h2, hr i (by omega), hr (i + 1) (by omega)]
      decide
    · rw [finRule_apply]
      push_cast
      have h2 := hr ((t : ℤ) + 1) (by omega)
      have h3 := hr ((t : ℤ) + 1 + 1) (by omega)
      rw [add_sub_cancel_right, hf, h2, h3]
      decide

/-- **Guard: at speed one the ray of rule `22` from the single seed reads `1` at every step**,
so it is eventually periodic; the speed hypothesis `p < q` is needed. -/
theorem eventuallyPeriodic_observedRationalRay_f22_single_one :
    (∀ t, observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      1 1 0 t = 1) ∧
    DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 1 0) := by
  have hall : ∀ t, observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      1 1 0 t = 1 := by
    intro t
    unfold observedRationalRay
    simpa using (f22_single_front t).2
  exact ⟨hall, 1, 0, one_pos, fun u _ => by rw [hall, hall]⟩


/-- A single seed is supported in one coset of `4ℤ`. -/
private theorem supportInCoset_finsupp_single :
    Rule22Sparse.SupportInCoset 4 ⇑(Finsupp.single (0 : ℤ) (1 : ZMod 2)) := by
  intro i j hi hj
  have hi' : i = 0 := by
    by_contra h; exact hi (by simp [Ne.symm h])
  have hj' : j = 0 := by
    by_contra h; exact hj (by simp [Ne.symm h])
  subst hi' hj'; simp

/-- **Rule `22` from the single seed is rule `90` plus, at odd steps, rule `90`'s previous row**
(the closed form of Chan-López and Martín-Ruiz 2026, §3, read on the line): at even steps the two
rules agree, and the odd row of rule `22` is the three-cell sum of the even row. -/
theorem f22_single_apply_eq_f90 (t : ℕ) (i : ℤ) :
    ((finRule f22 hq22)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i =
      ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i +
        if Odd t then ((finRule f90 hq90)^[t - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i
        else 0 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
  · rw [finRule_f22_iterate_two_mul_eq_f90 _ supportInCoset_finsupp_single j]
    have : ¬ Odd (2 * j) := by simp
    simp only [this, ↓reduceIte, add_zero]
  · have h22 : ∀ n, ⇑((finRule f22 hq22)^[n] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) =
        (LocalRuleColumns.step Rule22Sparse.rule22)^[n] (Pi.single 0 1) := by
      intro n
      rw [coe_finRule_iterate, f22_eq_rule22, Finsupp.single_eq_pi_single]
    have hodd := Rule22Sparse.iterate_step_rule22_odd_single j i
    have e1 := congrFun (h22 (2 * j + 1)) i
    have e2 := congrFun (h22 (2 * j)) (i - 1)
    have e3 := congrFun (h22 (2 * j)) i
    have e4 := congrFun (h22 (2 * j)) (i + 1)
    rw [e1, hodd, ← e2, ← e3, ← e4,
      finRule_f22_iterate_two_mul_eq_f90 _ supportInCoset_finsupp_single j]
    have ho : Odd (2 * j + 1) := by simp
    simp only [ho, ↓reduceIte]
    rw [Nat.add_sub_cancel, Function.iterate_succ_apply', finRule_apply]
    simp only [f90]
    ring


/-- Rule `22` from the single seed is symmetric about the seed: the rule is symmetric in its outer
inputs and the seed is. -/
theorem f22SymmSingle : F22SymmSingle := by
  have hsym : ∀ a b c : ZMod 2, f22 a b c = f22 c b a := by
    unfold f22 wolframRule; decide
  intro t
  induction t with
  | zero =>
      intro i
      simp only [Function.iterate_zero, id_eq, Finsupp.single_apply]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  | succ t ih =>
      intro i
      rw [Function.iterate_succ_apply', finRule_apply, finRule_apply, hsym,
        show -i - 1 = -(i + 1) by ring, show -i + 1 = -(i - 1) by ring, ih (i + 1), ih i,
        ih (i - 1)]

/-- **A one late on every ray of rule `22` from the single seed, at a speed strictly between rest
and one, from any cell**: a late one of rule `90` on the ray sits at a cell and step of one parity,
so rule `90`'s previous row, which vanishes at the opposite parity, adds nothing there. -/
theorem f22LateOnes : F22LateOnes := by
  intro p q hp hpq e T
  obtain ⟨t, hT, ht⟩ := exists_late_one_observedRationalRay_f90_single p q hp hpq e T
  refine ⟨t, hT, ?_⟩
  unfold observedRationalRay at ht ⊢
  set y : ℤ := e + ((p * t / q : ℕ) : ℤ) with hy
  rw [f22_single_apply_eq_f90]
  have hpar : 2 ∣ ((t : ℤ) + y) := by
    by_contra h
    rw [f90_single_apply_eq_zero_of_odd t y h] at ht
    exact zero_ne_one ht
  by_cases hodd : Odd t
  · have hn : ¬ 2 ∣ (((t - 1 : ℕ) : ℤ) + y) := by
      obtain ⟨m, hm⟩ := hodd
      omega
    simp only [hodd, ↓reduceIte]
    rw [f90_single_apply_eq_zero_of_odd (t - 1) y hn, ht, add_zero]
  · simp only [hodd, ↓reduceIte]
    rw [ht, add_zero]

/-- **Late zero runs along every ray of rule `22` at a speed strictly between rest and one**
(the transfer of [RuleSpace] §5 Proposition 5.1(ii) through `f22_single_apply_eq_f90`): at a large
power of two `2 ^ B` the ray's cell lies outside both light cones of the two translated copies
into which rule `90` splits, at the step and at the step before it. -/
theorem f22LateZeroRuns : F22LateZeroRuns := by
  intro p q hp hpq e n T
  set B : ℕ := T + n + q * e.natAbs + 2 * q * n + 1 with hB
  have hlt : B < 2 ^ B := Nat.lt_two_pow_self
  refine ⟨2 ^ B, by omega, ?_⟩
  intro r hr
  unfold observedRationalRay
  rw [f22_single_apply_eq_f90]
  set y : ℤ := e + ((p * (2 ^ B + r) / q : ℕ) : ℤ) with hy
  have hk : q * (p * (2 ^ B + r) / q) ≤ p * (2 ^ B + r) := Nat.mul_div_le _ _
  set k : ℕ := p * (2 ^ B + r) / q with hkdef
  have hkz : (q : ℤ) * k ≤ p * (2 ^ B + r) := by exact_mod_cast hk
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have he2 : e ≤ (e.natAbs : ℤ) := by rw [habs]; exact le_abs_self e
  have hpq' : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
  have hNz : (B : ℤ) < 2 ^ B := by exact_mod_cast hlt
  have hBz : (B : ℤ) = T + n + q * e.natAbs + 2 * q * n + 1 := by rw [hB]; push_cast; ring
  have hrz : (r : ℤ) < n := by exact_mod_cast hr
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hT0 : (0 : ℤ) ≤ T := by positivity
  have hqe : (q : ℤ) * -(e.natAbs : ℤ) ≤ q * e := mul_le_mul_of_nonneg_left he1 hq0
  have hqe' : (q : ℤ) * e ≤ q * (e.natAbs : ℤ) := mul_le_mul_of_nonneg_left he2 hq0
  have hpr : (p : ℤ) * r ≤ q * n := by
    have : (p : ℤ) * r ≤ q * r := mul_le_mul_of_nonneg_right (by omega) hr0
    have : (q : ℤ) * r ≤ q * n := mul_le_mul_of_nonneg_left hrz.le hq0
    omega
  have hq1 : (1 : ℤ) ≤ q := by omega
  have hea : (e.natAbs : ℤ) ≤ q * e.natAbs := by
    have : (0 : ℤ) ≤ e.natAbs := by positivity
    nlinarith
  have hA : (r : ℤ) < e + k + 2 ^ B := by omega
  have hC : (q : ℤ) * r < q * (2 ^ B - (e + k)) := by
    have h1 : (q : ℤ) * (2 ^ B - (e + k)) = q * 2 ^ B - q * e - q * k := by ring
    have h2 : ((p : ℤ) + 1) * 2 ^ B ≤ q * 2 ^ B :=
      mul_le_mul_of_nonneg_right hpq' (by positivity)
    have h3 : (q : ℤ) * r ≤ q * n := mul_le_mul_of_nonneg_left hrz.le hq0
    nlinarith
  have hD : (r : ℤ) < 2 ^ B - (e + k) := lt_of_mul_lt_mul_left hC hq0
  have z : ∀ r' : ℕ, r' ≤ r →
      ((finRule f90 hq90)^[2 ^ B + r'] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) y = 0 := by
    intro r' hr'
    have hr'z : (r' : ℤ) ≤ r := by exact_mod_cast hr'
    have z1 := f90_single_apply_eq_zero_of_lt r' (e + k - 2 ^ B)
      (by rw [lt_abs]; right; linarith)
    have z2 := f90_single_apply_eq_zero_of_lt r' (e + k + 2 ^ B)
      (by rw [lt_abs]; left; linarith)
    rw [f90_iterate_two_pow_add, hy]
    rw [z1, z2, add_zero]
  rw [z r le_rfl]
  by_cases hodd : Odd (2 ^ B + r)
  · have h2 : 2 ∣ 2 ^ B := dvd_pow_self 2 (by omega)
    have hr1 : 1 ≤ r := by
      rw [Nat.odd_iff] at hodd
      omega
    simp only [hodd, ↓reduceIte]
    rw [show 2 ^ B + r - 1 = 2 ^ B + (r - 1) by omega, z (r - 1) (by omega), add_zero]
  · simp only [hodd, ↓reduceIte, add_zero]

/-- **A ray of rule `22` from the single seed, at a speed strictly between rest and one, from any
cell, is not eventually periodic** ([RuleSpace] §5 Proposition 5.1 transferred through
`f22_single_apply_eq_f90`). -/
theorem not_eventuallyPeriodic_observedRationalRay_f22_single
    (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_observedRationalRay_f22_single_of f22LateOnes f22LateZeroRuns p q hp hpq e

/-- **The ray of rule `22` from the single seed toward decreasing cells, at a speed strictly
between rest and one, from any cell, is not eventually periodic.** -/
theorem not_eventuallyPeriodic_mirrorRay_f22_single
    (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (fun t => ((finRule f22 hq22)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (e - ((p * t / q : ℕ) : ℤ))) :=
  not_eventuallyPeriodic_mirrorRay_f22_single_of f22LateOnes f22LateZeroRuns f22SymmSingle
    p q hp hpq e

/-- **Joint satisfiability** of the speed hypotheses of the statement on rule `22`: the ray at
speed `1 / 2` from cell zero is not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f22_single_nonvacuous :
    0 < 1 ∧ 1 < 2 ∧
      ¬ DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 0) :=
  ⟨by decide, by decide,
    not_eventuallyPeriodic_observedRationalRay_f22_single 1 2 (by decide) (by decide) 0⟩

/-- **Guard: at speed zero the ray of rule `22` from the single seed at cell `0` reads `1` at
steps `0` and `1` and `0` from step two on**, so it is eventually periodic; the speed hypothesis
`0 < p` is needed. -/
theorem eventuallyPeriodic_observedRationalRay_f22_single_zero :
    (∀ t, 2 ≤ t →
      observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1 0 t = 0) ∧
    DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1 0) := by
  have h90 : ∀ u : ℕ, 1 ≤ u →
      ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 0 := by
    intro u hu
    by_cases h : 2 ∣ u
    · obtain ⟨a, rfl⟩ := h
      have := zeroOfShared a a (by rw [Nat.and_self]; omega)
      rw [sub_self] at this
      rw [two_mul]
      exact this
    · exact f90_single_apply_eq_zero_of_odd u 0 (by omega)
  have hall : ∀ t, 2 ≤ t →
      observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1 0 t = 0 := by
    intro t ht
    unfold observedRationalRay
    simp only [zero_mul, Nat.zero_div, Nat.cast_zero, add_zero]
    rw [f22_single_apply_eq_f90, h90 t (by omega)]
    by_cases hodd : Odd t
    · simp only [hodd, ↓reduceIte]
      rw [h90 (t - 1) (by omega), add_zero]
    · simp only [hodd, ↓reduceIte, add_zero]
  exact ⟨hall, 1, 2, one_pos, fun u hu => by rw [hall (u + 1) (by omega), hall u hu]⟩

/-- **Guard: the ones condition on rays of rule `22` fails when speed zero is admitted.** Cell `0`
reads `0` from step two on, so the hypothesis `0 < p` is needed. -/
theorem not_F22LateOnes_of_zero_speed :
    ¬ (∀ p q : ℕ, p < q → ∀ e : ℤ, ∀ T : ℕ, ∃ t, T ≤ t ∧
      observedRationalRay (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t =
        1) := by
  intro h
  obtain ⟨t, ht, hc⟩ := h 0 1 one_pos 0 2
  rw [eventuallyPeriodic_observedRationalRay_f22_single_zero.1 t ht] at hc
  exact zero_ne_one hc

end ECA

/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f22_single_of' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f22_single_of

/-- info: 'ECA.not_eventuallyPeriodic_mirrorRay_f22_single_of' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_mirrorRay_f22_single_of

/-- info: 'ECA.eventuallyPeriodic_observedRationalRay_f22_single_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedRationalRay_f22_single_one

/-- info:
'ECA.f22_single_apply_eq_f90' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f22_single_apply_eq_f90

/-- info: 'ECA.f22SymmSingle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f22SymmSingle

/-- info: 'ECA.f22LateOnes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f22LateOnes

/-- info: 'ECA.f22LateZeroRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f22LateZeroRuns

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f22_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f22_single

/-- info:
'ECA.not_eventuallyPeriodic_mirrorRay_f22_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_mirrorRay_f22_single

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f22_single_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f22_single_nonvacuous

/-- info:
'ECA.eventuallyPeriodic_observedRationalRay_f22_single_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedRationalRay_f22_single_zero

/-- info:
'ECA.not_F22LateOnes_of_zero_speed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_F22LateOnes_of_zero_speed
