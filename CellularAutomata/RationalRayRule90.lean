/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.ObservedRays
public import Mathlib.Data.Nat.Bitwise
public import ErgodicTheory.PascalColumns

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Rays of rule 90 from the single seed: non-periodicity from three conditions
([RuleSpace] §4 Proposition 4.4)

`[RuleSpace] §4 Proposition 4.4` settles the rays of a table whose diameter never grows and
states nothing of a ray at a table whose diameter does grow. This file states one such result,
for rule `90` from the single seed: a rational ray `p / q` from cell `e` is not eventually
periodic as soon as three conditions on that ray hold. Registered as [RuleSpace] §5
Proposition 5.1, row RS-11. The first condition, a one at every disjoint pair, is proved here
(`oneOfDisjoint`),
and so is the third at every speed below one (`lateZeroRuns`); the second is proved in
`RationalRayPairs` at every speed strictly between 0 and 1, where the three conditions hold at
once and the ray is not eventually periodic
(`not_eventuallyPeriodic_observedRationalRay_f90_single`).

"Leaf" is file-local vocabulary: the three conditions are the hypotheses of the parent theorem,
stated as named propositions.

* **A one at every disjoint pair** (`OneOfDisjoint`): when `a` and `b` share no binary digit,
  rule `90` from the single seed reads `1` at cell `a - b` at step `a + b`.
* **Late disjoint pairs on the ray** (`LateDisjointOnRay`): past every step, some pair with no
  shared binary digit lies on the ray (`OnRay`).
* **Late zero runs** (`LateZeroRuns`): past every step, the ray reads `0` for any prescribed
  number of consecutive steps.

## Main results

* `not_eventuallyPeriodic_of_late_one_of_late_zero_runs` — a `ZMod 2` sequence with a one past
  every step and zero runs of every length past every step is not eventually periodic;
  `not_eventuallyPeriodic_of_late_one_of_late_zero_runs_nonvacuous` meets both hypotheses.
* `exists_late_one_observedRationalRay_f90_single_of` — a one at every disjoint pair and late
  disjoint pairs on the ray give a one on the ray past every step.
* `not_eventuallyPeriodic_observedRationalRay_f90_single_of` — **the parent**: the three
  conditions together give a ray that is not eventually periodic.
* `oneOfDisjoint` — the first condition holds: rule `90` from the single seed is Pascal's triangle
  modulo two and the coefficient is odd exactly at disjoint pairs (Lucas's theorem at the prime
  two, `PascalColumns.step_rule90_single_eq_one_iff`); `oneOfDisjoint_guard` shows the
  disjointness is needed.
* `lateZeroRuns` — the third condition holds at every speed `p / q` with `p < q`, from every cell:
  at a large power of two the orbit splits into two copies and the ray lies outside both light
  cones; `lateZeroRuns_guard` shows `p < q` is needed (at speed one the ray reads a one at every
  step).
-/

@[expose] public section

namespace RationalRayNinety

open ExtremeTapWidth EndpointClasses
open ObservedColumn (observedRationalRay hq90)

/-! ## The three conditions -/

/-- **On the ray**: the cell `a - b` is the one the ray of speed `p / q` from `e` reads at step
`a + b`. -/
def OnRay (p q : ℕ) (e : ℤ) (a b : ℕ) : Prop :=
  (a : ℤ) - b = e + ((p * (a + b) / q : ℕ) : ℤ)

/-- **A one at every disjoint pair**: when `a` and `b` share no binary digit, rule 90 from the
single seed reads `1` at cell `a - b` at step `a + b`. -/
def OneOfDisjoint : Prop :=
  ∀ a b : ℕ, a &&& b = 0 →
    ((tableRule f90 hq90)^[a + b] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) ((a : ℤ) - b) = 1

/-- **Late disjoint pairs on the ray**: past every step some pair with no shared binary digit
lies on the ray. -/
def LateDisjointOnRay (p q : ℕ) (e : ℤ) : Prop :=
  ∀ T : ℕ, ∃ a b : ℕ, a &&& b = 0 ∧ T ≤ a + b ∧ OnRay p q e a b

/-- **Late zero runs**: past every step the ray reads `0` for any prescribed number of
consecutive steps. -/
def LateZeroRuns (p q : ℕ) (e : ℤ) : Prop :=
  ∀ n T : ℕ, ∃ t₀ : ℕ, T ≤ t₀ ∧ ∀ r < n,
    observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e (t₀ + r)
      = 0

/-! ## Piece 1: the generic step -/

/-- **A one past every step and zero runs of every length past every step is not eventually
periodic**: a period `P` holding from `N` makes a zero run of length `P` past `N` propagate to
all later steps, against a one past it. -/
theorem not_eventuallyPeriodic_of_late_one_of_late_zero_runs (f : ℕ → ZMod 2)
    (h1 : ∀ T, ∃ t, T ≤ t ∧ f t = 1)
    (h0 : ∀ n T, ∃ t₀, T ≤ t₀ ∧ ∀ r < n, f (t₀ + r) = 0) :
    ¬ GrowingComposite.EventuallyPeriodic f := by
  rintro ⟨P, N, hP, hper⟩
  obtain ⟨t₀, ht₀, hrun⟩ := h0 P N
  have hall : ∀ k, f (t₀ + k) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < P
      · exact hrun k hk
      · have hk' : k - P < k := by omega
        have := hper (t₀ + (k - P)) (by omega)
        have e : t₀ + (k - P) + P = t₀ + k := by omega
        rw [e] at this
        rw [this]
        exact ih _ hk'
  obtain ⟨t, ht, hft⟩ := h1 t₀
  have := hall (t - t₀)
  rw [show t₀ + (t - t₀) = t by omega, hft] at this
  exact one_ne_zero this

/-- **Joint satisfiability**: the sequence reading `1` exactly one before a power of two meets
both hypotheses. -/
theorem not_eventuallyPeriodic_of_late_one_of_late_zero_runs_nonvacuous :
    ∃ f : ℕ → ZMod 2, (∀ T, ∃ t, T ≤ t ∧ f t = 1) ∧
      (∀ n T, ∃ t₀, T ≤ t₀ ∧ ∀ r < n, f (t₀ + r) = 0) := by
  classical
  refine ⟨fun t => if ∃ j, t + 1 = 2 ^ j then 1 else 0, ?_, ?_⟩
  · intro T
    refine ⟨2 ^ T - 1, ?_, ?_⟩
    · have := Nat.lt_two_pow_self (n := T)
      omega
    · have : ∃ j, 2 ^ T - 1 + 1 = 2 ^ j :=
        ⟨T, by have := Nat.one_le_two_pow (n := T); omega⟩
      simp [this]
  · intro n T
    refine ⟨2 ^ (n + T), ?_, ?_⟩
    · have := Nat.lt_two_pow_self (n := n + T)
      omega
    · intro r hr
      have hlt := Nat.lt_two_pow_self (n := n + T)
      have hnot : ¬ ∃ j, 2 ^ (n + T) + r + 1 = 2 ^ j := by
        rintro ⟨j, hj⟩
        by_cases hjle : j ≤ n + T
        · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hjle
          omega
        · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show n + T + 1 ≤ j by omega)
          rw [pow_succ] at this
          omega
      simp [hnot]

/-! ## Piece 2: the parent -/

/-- **A one past every step on the ray**: a one at every disjoint pair and late disjoint pairs
on the ray give a one on the ray past every step. -/
theorem exists_late_one_observedRationalRay_f90_single_of (p q : ℕ) (e : ℤ)
    (h₁ : OneOfDisjoint) (h₂ : LateDisjointOnRay p q e) :
    ∀ T : ℕ, ∃ t, T ≤ t ∧
      observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1 := by
  intro T
  obtain ⟨a, b, hab, hT, hon⟩ := h₂ T
  refine ⟨a + b, hT, ?_⟩
  have h := h₁ a b hab
  unfold OnRay at hon
  unfold observedRationalRay
  rw [← hon]
  exact h

/-- **The parent**: a one at every disjoint pair, late disjoint pairs on the ray and late zero
runs together make the ray of rule 90 from the single seed not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f90_single_of (p q : ℕ) (e : ℤ)
    (h₁ : OneOfDisjoint) (h₂ : LateDisjointOnRay p q e) (h₃ : LateZeroRuns p q e) :
    ¬ GrowingComposite.EventuallyPeriodic
      (observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_of_late_one_of_late_zero_runs _
    (exists_late_one_observedRationalRay_f90_single_of p q e h₁ h₂) h₃

/-! ## Piece 3: a one at every disjoint pair -/

/-- outside the light cone the single seed's orbit is zero -/
theorem f90_single_apply_eq_zero_of_lt (t : ℕ) (i : ℤ) (h : (t : ℤ) < |i|) :
    ((tableRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i = 0 := by
  induction t generalizing i with
  | zero =>
      have hi : i ≠ 0 := by
        intro h0; subst h0; simp at h
      simp [Ne.symm hi]
  | succ t ih =>
      rw [Function.iterate_succ_apply', tableRule_apply]
      have h1 := ih (i - 1) (by push_cast at h; rw [lt_abs] at h ⊢; omega)
      have h2 := ih i (by push_cast at h; rw [lt_abs] at h ⊢; omega)
      have h3 := ih (i + 1) (by push_cast at h; rw [lt_abs] at h ⊢; omega)
      rw [h1, h2, h3]
      exact hq90

/-- `2 ^ M` further steps split the orbit into two translated copies -/
theorem f90_iterate_two_pow_add (M t : ℕ) (s : ℤ →₀ ZMod 2) (i : ℤ) :
    ((tableRule f90 hq90)^[2 ^ M + t] s) i =
      ((tableRule f90 hq90)^[t] s) (i - 2 ^ M) + ((tableRule f90 hq90)^[t] s) (i + 2 ^ M) := by
  rw [Function.iterate_add_apply, DrivenColumns.iterate_two_pow_f90]

/-- **A one at every disjoint pair**: when `a` and `b` share no binary digit, rule 90 from the
single seed reads `1` at cell `a - b` at step `a + b`. -/
theorem oneOfDisjoint : OneOfDisjoint := by
  intro a b hab
  have h := (PascalColumns.step_rule90_single_eq_one_iff a b).mpr hab
  have e := congrFun (ObservedColumn.coe_tableRule_iterate f90 hq90 (a + b)
    (Finsupp.single (0 : ℤ) (1 : ZMod 2))) ((a : ℤ) - b)
  rw [Finsupp.single_eq_pi_single] at e
  exact e.trans h

/-- **Disjointness is load-bearing**: at `a = b = 1`, which share a binary digit, rule 90 from
the single seed reads `0` at cell `0` at step `2`. -/
theorem oneOfDisjoint_guard :
    ((tableRule f90 hq90)^[1 + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) ((1 : ℤ) - 1) = 0 ∧
      (1 : ℕ) &&& 1 ≠ 0 := by
  refine ⟨?_, by decide⟩
  change (tableRule f90 hq90 (tableRule f90 hq90 (Finsupp.single (0 : ℤ) (1 : ZMod 2))))
    ((1 : ℤ) - 1) = 0
  rw [tableRule_apply, tableRule_apply, tableRule_apply, tableRule_apply]
  simp only [sub_self, zero_sub, Int.reduceNeg, Int.reduceSub, ne_eq, neg_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne, one_ne_zero, neg_add_cancel,
    Finsupp.single_eq_same, zero_add, Int.reduceAdd]
  decide

/-! ## Piece 4: late zero runs -/

/-- **Late zero runs at every speed below one**: at every speed `p / q` with `p < q`, from every
cell `e`, the ray of rule 90 from the single seed reads `0` for any prescribed number of
consecutive steps past every step. At a power of two `2 ^ j` that is large enough, the orbit
splits into two translated copies, and the ray's cell lies outside both light cones. -/
theorem lateZeroRuns (p q : ℕ) (hpq : p < q) (e : ℤ) : LateZeroRuns p q e := by
  intro n T
  set B : ℕ := T + n + q * e.natAbs + 2 * q * n with hB
  have hlt : B < 2 ^ B := Nat.lt_two_pow_self
  refine ⟨2 ^ B, by omega, ?_⟩
  intro r hr
  unfold observedRationalRay
  rw [f90_iterate_two_pow_add]
  have hk : q * (p * (2 ^ B + r) / q) ≤ p * (2 ^ B + r) := Nat.mul_div_le _ _
  set k : ℕ := p * (2 ^ B + r) / q with hkdef
  have hkz : (q : ℤ) * k ≤ p * (2 ^ B + r) := by exact_mod_cast hk
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have he2 : e ≤ (e.natAbs : ℤ) := by rw [habs]; exact le_abs_self e
  have hpq' : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
  have hNz : (B : ℤ) < 2 ^ B := by exact_mod_cast hlt
  have hBz : (B : ℤ) = T + n + q * e.natAbs + 2 * q * n := by rw [hB]; push_cast; ring
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
  have z1 := f90_single_apply_eq_zero_of_lt r (e + k - 2 ^ B) (by rw [lt_abs]; right; linarith)
  have z2 := f90_single_apply_eq_zero_of_lt r (e + k + 2 ^ B) (by rw [lt_abs]; left; exact hA)
  rw [z1, z2, add_zero]

/-- **The hypothesis `p < q` is load-bearing**: at speed one from cell `0` the ray reads the cell
`t` at step `t`, which holds `1` at every step, so not even a run of one zero exists. -/
theorem lateZeroRuns_guard : ¬ LateZeroRuns 1 1 0 := by
  intro h
  obtain ⟨t₀, -, ht⟩ := h 1 0
  have h0 := ht 0 (by norm_num)
  have h1 := oneOfDisjoint t₀ 0 (by simp)
  unfold observedRationalRay at h0
  simp only [add_zero, one_mul, Nat.div_one, zero_add] at h0
  simp only [add_zero, Nat.cast_zero, sub_zero] at h1
  rw [h0] at h1
  exact zero_ne_one h1

end RationalRayNinety

/-- info: 'RationalRayNinety.not_eventuallyPeriodic_of_late_one_of_late_zero_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.not_eventuallyPeriodic_of_late_one_of_late_zero_runs

/-- info: 'RationalRayNinety.not_eventuallyPeriodic_of_late_one_of_late_zero_runs_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.not_eventuallyPeriodic_of_late_one_of_late_zero_runs_nonvacuous

/-- info: 'RationalRayNinety.exists_late_one_observedRationalRay_f90_single_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_late_one_observedRationalRay_f90_single_of

/-- info: 'RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single_of

/-- info: 'RationalRayNinety.f90_single_apply_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.f90_single_apply_eq_zero_of_lt

/-- info: 'RationalRayNinety.f90_iterate_two_pow_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.f90_iterate_two_pow_add

/-- info: 'RationalRayNinety.oneOfDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.oneOfDisjoint

/-- info: 'RationalRayNinety.oneOfDisjoint_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.oneOfDisjoint_guard

/-- info: 'RationalRayNinety.lateZeroRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateZeroRuns

/-- info: 'RationalRayNinety.lateZeroRuns_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateZeroRuns_guard
