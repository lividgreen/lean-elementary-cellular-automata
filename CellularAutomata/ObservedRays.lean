/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ErgodicTheory.DrivenColumns
public import CellularAutomata.ObservedColumn
public import ErgodicTheory.LocalRuleColumns

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Driven columns on a table's own recursion
([RuleSpace] §4 Proposition 4.2, [RuleSpace] §4 Remark 4.1)

The driven interior, the rays at the rule's own speed, and the `f90` column at cell `1` that is
not eventually periodic, all built on the engine `eventuallyPeriodic_of_driven` of
`ErgodicTheory/DrivenColumns.lean` over the observed columns of
`CellularAutomata/ObservedColumn.lean`;
the module
docstring there lists the results.
-/


@[expose] public section

namespace DrivenColumns

open ExtremeTapWidth EndpointClasses
open ObservedColumn (observedColumn hq90)


/-! ## Piece 2: the driven interior -/

/-- **The width-`(m + 1)` observed window**: cells `a, a + 1, …, a + m`, read all at once. -/
def observedWindow (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (a : ℤ) (n : ℕ) :
    ℕ → (Fin n → ZMod 2) := fun t j => (U^[t] s₀) (a + ((j : ℕ) : ℤ))

/-- **The window form** ([RuleSpace] §4 Proposition 4.2(ii), row RS-5): the whole width-`(m + 1)`
window is eventually periodic iff its two boundary columns are. An instance of
`LocalRuleColumns.eventuallyPeriodic_window_iff` (lean-classical-upstream), which states the
window form for any local rule over a finite carrier on all configurations of the line; the
table rule's iterates are that rule's iterates on the underlying functions
(`ObservedColumn.coe_tableRule_iterate`). -/
theorem eventuallyPeriodic_observedWindow_iff
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2)
    (a : ℤ) (m : ℕ) :
    GrowingComposite.EventuallyPeriodic (observedWindow (tableRule f hq) s₀ a (m + 1)) ↔
      GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ a) ∧
      GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ (a + (m : ℤ))) := by
  have hw : observedWindow (tableRule f hq) s₀ a (m + 1)
      = LocalRuleColumns.window f ⇑s₀ a (m + 1) := by
    funext t j
    simp only [observedWindow, LocalRuleColumns.window,
      ← ObservedColumn.coe_tableRule_iterate f hq t s₀]
  rw [hw, ObservedColumn.observedColumn_tableRule_eq_column,
    ObservedColumn.observedColumn_tableRule_eq_column]
  exact LocalRuleColumns.eventuallyPeriodic_window_iff f ⇑s₀ a m

/-- **The driven interior, between two settled columns** ([RuleSpace] §4 Proposition 4.2(ii), row
RS-5): at `a ≤ i ≤ b`, if the columns at `a` and `b` are each eventually periodic, so is the
column at `i`. A corollary of the window form: `i` sits
inside the width-`(b - a + 1)` window based at `a`, whose two boundary columns are exactly the
hypotheses, and `i`'s own column is one coordinate projection of that window. -/
theorem eventuallyPeriodic_observedColumn_between
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {a b i : ℤ}
    (ha : GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ a))
    (hb : GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ b))
    (hai : a ≤ i) (hib : i ≤ b) :
    GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i) := by
  rw [ObservedColumn.observedColumn_tableRule_eq_column] at ha hb ⊢
  exact LocalRuleColumns.eventuallyPeriodic_column_between f ⇑s₀ ha hb hai hib

/-- The joint-satisfiability witness for `eventuallyPeriodic_observedColumn_between`'s four
hypotheses: the shift `f170` from the single seed, at `a = -1`, `i = 0`, `b = 1`, with both end
columns eventually periodic by
`ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints`. -/
theorem eventuallyPeriodic_observedColumn_between_nonvacuous :
    GrowingComposite.EventuallyPeriodic
        (observedColumn (tableRule f170 hq170) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-1)) ∧
      GrowingComposite.EventuallyPeriodic
        (observedColumn (tableRule f170 hq170) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) ∧
      (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1 := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩ <;>
    exact ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints
      f170 hq170 EndpointClasses.zeroByEndpoints_f170 _ _

/-! ## Piece 3: the rays at the rule's own speed -/

/-- **The observed ray**: the value read at cell `e + v · t` at stage `t`, moving at integer speed
`v` cells per step. -/
def observedRay (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (v e : ℤ) :
    ℕ → ZMod 2 := fun t => (U^[t] s₀) (e + v * (t : ℤ))

/-- **Speed zero is the observed column** ([RuleSpace] §4 Proposition 4.2(iii), row RS-6). -/
theorem observedRay_zero (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (e : ℤ) :
    observedRay U s₀ 0 e = observedColumn U s₀ e := by
  funext t
  simp [observedRay, observedColumn]

/-- **A bound above the support**: since `s` is finitely supported, some `M` bounds every nonzero
cell from above. -/
private theorem exists_bound_above_support (s : ℤ →₀ ZMod 2) :
    ∃ M : ℤ, ∀ k : ℤ, M < k → s k = 0 := by
  by_cases h : s.support.Nonempty
  · refine ⟨s.support.max' h, fun k hk => ?_⟩
    by_contra hc
    have := Finset.le_max' s.support k (Finsupp.mem_support_iff.mpr hc)
    omega
  · refine ⟨0, fun k _ => ?_⟩
    have hz : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    rw [hz]; simp

/-- **A bound below the support**, the mirror. -/
private theorem exists_bound_below_support (s : ℤ →₀ ZMod 2) :
    ∃ M : ℤ, ∀ k : ℤ, k < M → s k = 0 := by
  by_cases h : s.support.Nonempty
  · refine ⟨s.support.min' h, fun k hk => ?_⟩
    by_contra hc
    have := Finset.min'_le s.support k (Finsupp.mem_support_iff.mpr hc)
    omega
  · refine ⟨0, fun k _ => ?_⟩
    have hz : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    rw [hz]; simp

/-- **The support bound propagates forward, above**: if `s₀` vanishes past `M`, so does every
iterate, past `M` shifted by the elapsed time. -/
private theorem tableRule_iterate_eq_zero_of_gt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M : ℤ} (hM : ∀ k : ℤ, M < k → s₀ k = 0) :
    ∀ (t : ℕ) (j : ℤ), M + (t : ℤ) < j → ((tableRule f hq)^[t] s₀) j = 0 := by
  intro t j hj
  have h := congrFun (ObservedColumn.coe_tableRule_iterate f hq t s₀) j
  exact h.trans (LocalRuleColumns.iterate_step_eq_zero_of_gt f hq ⇑s₀ hM t j hj)

/-- **The support bound propagates forward, below**, the mirror. -/
private theorem tableRule_iterate_eq_zero_of_lt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M : ℤ} (hM : ∀ k : ℤ, k < M → s₀ k = 0) :
    ∀ (t : ℕ) (j : ℤ), j < M - (t : ℤ) → ((tableRule f hq)^[t] s₀) j = 0 := by
  intro t j hj
  have h := congrFun (ObservedColumn.coe_tableRule_iterate f hq t s₀) j
  exact h.trans (LocalRuleColumns.iterate_step_eq_zero_of_lt f hq ⇑s₀ hM t j hj)

/-- **A ray starting beyond the support's upper bound is constantly `0`**. -/
private theorem observedRay_one_eq_zero_of_gt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M e : ℤ} (hM : ∀ k : ℤ, M < k → s₀ k = 0)
    (he : M < e) (t : ℕ) : observedRay (tableRule f hq) s₀ 1 e t = 0 :=
  tableRule_iterate_eq_zero_of_gt f hq s₀ hM t (e + 1 * (t : ℤ)) (by omega)

/-- **A ray starting beyond the support's lower bound is constantly `0`**, the mirror. -/
private theorem observedRay_neg_one_eq_zero_of_lt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M e : ℤ} (hM : ∀ k : ℤ, k < M → s₀ k = 0)
    (he : e < M) (t : ℕ) : observedRay (tableRule f hq) s₀ (-1) e t = 0 :=
  tableRule_iterate_eq_zero_of_lt f hq s₀ hM t (e + (-1) * (t : ℤ)) (by omega)

private theorem eventuallyPeriodic_observedRay_one_of_gt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M e : ℤ} (hM : ∀ k : ℤ, M < k → s₀ k = 0)
    (he : M < e) : GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ 1 e) :=
  ⟨1, 0, one_pos, fun t _ => by
    rw [observedRay_one_eq_zero_of_gt f hq s₀ hM he, observedRay_one_eq_zero_of_gt f hq s₀ hM he]⟩

private theorem eventuallyPeriodic_observedRay_neg_one_of_lt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M e : ℤ} (hM : ∀ k : ℤ, k < M → s₀ k = 0)
    (he : e < M) :
    GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ (-1) e) :=
  ⟨1, 0, one_pos, fun t _ => by
    rw [observedRay_neg_one_eq_zero_of_lt f hq s₀ hM he,
      observedRay_neg_one_eq_zero_of_lt f hq s₀ hM he]⟩

/-- **The ray at speed `1`, by strong induction on the distance to the support's upper bound**:
`ray_e (t + 1) = f (ray_e t) (ray_{e+1} t) (ray_{e+2} t)` drives `ray_e` by the pair `(ray_{e+1},
ray_{e+2})`, each closer to (or past) the bound, so `eventuallyPeriodic_of_driven` closes the
induction once the pair is eventually periodic by the induction hypothesis and pairing. -/
private theorem eventuallyPeriodic_observedRay_one_of_le (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M : ℤ} (hM : ∀ k : ℤ, M < k → s₀ k = 0) :
    ∀ n : ℕ, ∀ e : ℤ, (M + 1 - e).toNat ≤ n →
      GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ 1 e) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e he
    by_cases hcase : M < e
    · exact eventuallyPeriodic_observedRay_one_of_gt f hq s₀ hM hcase
    · push Not at hcase
      have hu := eventuallyPeriodic_pair (ih (M + 1 - (e + 1)).toNat (by omega) (e + 1) le_rfl)
        (ih (M + 1 - (e + 2)).toNat (by omega) (e + 2) le_rfl)
      have hstep : ∃ N, ∀ t, N ≤ t →
          observedRay (tableRule f hq) s₀ 1 e (t + 1)
            = (fun (x : ZMod 2) (p : ZMod 2 × ZMod 2) => f x p.1 p.2)
                (observedRay (tableRule f hq) s₀ 1 e t)
                ((fun t => (observedRay (tableRule f hq) s₀ 1 (e + 1) t,
                            observedRay (tableRule f hq) s₀ 1 (e + 2) t)) t) := by
        refine ⟨0, fun t _ => ?_⟩
        change ((tableRule f hq)^[t + 1] s₀) (e + 1 * ((t + 1 : ℕ) : ℤ))
          = f (((tableRule f hq)^[t] s₀) (e + 1 * (t : ℤ)))
              (((tableRule f hq)^[t] s₀) ((e + 1) + 1 * (t : ℤ)))
              (((tableRule f hq)^[t] s₀) ((e + 2) + 1 * (t : ℤ)))
        have e1 : e + 1 * ((t + 1 : ℕ) : ℤ) - 1 = e + 1 * (t : ℤ) := by push_cast; ring
        have e2 : e + 1 * ((t + 1 : ℕ) : ℤ) = (e + 1) + 1 * (t : ℤ) := by push_cast; ring
        have e3 : e + 1 * ((t + 1 : ℕ) : ℤ) + 1 = (e + 2) + 1 * (t : ℤ) := by push_cast; ring
        rw [Function.iterate_succ_apply', tableRule_apply, e1, e3, e2]
      exact eventuallyPeriodic_of_driven (fun (x : ZMod 2) (p : ZMod 2 × ZMod 2) => f x p.1 p.2)
        hu hstep

/-- **The ray at speed `-1`**, the mirror: `ray_e (t + 1) = f (ray_{e-2} t) (ray_{e-1} t) (ray_e
t)` drives `ray_e` by the pair `(ray_{e-2}, ray_{e-1})`, by strong induction on the distance to the
support's lower bound. -/
private theorem eventuallyPeriodic_observedRay_neg_one_of_le (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M : ℤ} (hM : ∀ k : ℤ, k < M → s₀ k = 0) :
    ∀ n : ℕ, ∀ e : ℤ, (e - M + 1).toNat ≤ n →
      GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ (-1) e) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e he
    by_cases hcase : e < M
    · exact eventuallyPeriodic_observedRay_neg_one_of_lt f hq s₀ hM hcase
    · push Not at hcase
      have hu := eventuallyPeriodic_pair (ih (e - 2 - M + 1).toNat (by omega) (e - 2) le_rfl)
        (ih (e - 1 - M + 1).toNat (by omega) (e - 1) le_rfl)
      have hstep : ∃ N, ∀ t, N ≤ t →
          observedRay (tableRule f hq) s₀ (-1) e (t + 1)
            = (fun (x : ZMod 2) (p : ZMod 2 × ZMod 2) => f p.1 p.2 x)
                (observedRay (tableRule f hq) s₀ (-1) e t)
                ((fun t => (observedRay (tableRule f hq) s₀ (-1) (e - 2) t,
                            observedRay (tableRule f hq) s₀ (-1) (e - 1) t)) t) := by
        refine ⟨0, fun t _ => ?_⟩
        change ((tableRule f hq)^[t + 1] s₀) (e + (-1) * ((t + 1 : ℕ) : ℤ))
          = f (((tableRule f hq)^[t] s₀) ((e - 2) + (-1) * (t : ℤ)))
              (((tableRule f hq)^[t] s₀) ((e - 1) + (-1) * (t : ℤ)))
              (((tableRule f hq)^[t] s₀) (e + (-1) * (t : ℤ)))
        have e1 : e + (-1) * ((t + 1 : ℕ) : ℤ) - 1 = (e - 2) + (-1) * (t : ℤ) := by push_cast; ring
        have e2 : e + (-1) * ((t + 1 : ℕ) : ℤ) = (e - 1) + (-1) * (t : ℤ) := by push_cast; ring
        have e3 : e + (-1) * ((t + 1 : ℕ) : ℤ) + 1 = e + (-1) * (t : ℤ) := by push_cast; ring
        rw [Function.iterate_succ_apply', tableRule_apply, e1, e3, e2]
      exact eventuallyPeriodic_of_driven (fun (x : ZMod 2) (p : ZMod 2 × ZMod 2) => f p.1 p.2 x)
        hu hstep

/-- **The ray at speed `1` is eventually periodic** ([RuleSpace] §4 Proposition 4.2(iii), row RS-6),
at every table meeting quiescence alone and every finitely-supported seed. -/
theorem eventuallyPeriodic_observedRay_one
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) (e : ℤ) :
    GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ 1 e) := by
  obtain ⟨M, hM⟩ := exists_bound_above_support s₀
  exact eventuallyPeriodic_observedRay_one_of_le f hq s₀ hM (M + 1 - e).toNat e le_rfl

/-- **The ray at speed `-1` is eventually periodic** ([RuleSpace] §4 Proposition 4.2(iii), row
RS-6), the mirror. -/
theorem eventuallyPeriodic_observedRay_neg_one
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) (e : ℤ) :
    GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ (-1) e) := by
  obtain ⟨M, hM⟩ := exists_bound_below_support s₀
  exact eventuallyPeriodic_observedRay_neg_one_of_le f hq s₀ hM (e - M + 1).toNat e le_rfl

/-! ## Piece 4: a column that is not eventually periodic -/

/-- **`2 ^ j` steps of rule `90`, in one identity** ([RuleSpace] §4 Proposition 4.2(iv), row RS-6):
pure `ZMod 2` cancellation of the doubled middle term, no binomial coefficient and no Lucas'
theorem. -/
theorem iterate_two_pow_f90 :
    ∀ (j : ℕ) (s : ℤ →₀ ZMod 2) (i : ℤ),
      ((tableRule f90 hq90) ^[2 ^ j] s) i = s (i - 2 ^ j) + s (i + 2 ^ j) := by
  intro j s i
  have h := congrFun (ObservedColumn.coe_tableRule_iterate f90 hq90 (2 ^ j) s) i
  exact h.trans (LocalRuleColumns.iterate_two_pow_step90 j ⇑s i)

/-- **Live at `2 ^ (j + 1) - 1`** ([RuleSpace] §4 Proposition 4.2(iv), row RS-6): the column at
cell `1` reads `1` at every stage `2 ^ j' - 1` with `j' ≥ 1`, one cell over from the center column
of [RuleSpace] §4 Remark 4.1. Route: `2 ^ (j + 1) - 1 = 2 ^ j + (2 ^ j - 1)`, and the step identity
at `r = 2 ^ j - 1` gives the edge-live value (`observedColumn_f90_single_edge`, since
`1 - 2 ^ j = -(2 ^ j - 1)`) plus a cell beyond the `r`-step support (`0`,
`tableRule_iterate_eq_zero_of_gt`). -/
theorem observedColumn_f90_single_one_live (j : ℕ) :
    ((tableRule f90 hq90) ^[2 ^ (j + 1) - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 1 := by
  have h := congrFun (ObservedColumn.coe_tableRule_iterate f90 hq90 (2 ^ (j + 1) - 1)
    (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1
  rw [Finsupp.single_eq_pi_single] at h
  exact h.trans (LocalRuleColumns.column_step90_single_one_live j)

/-- **Dead strictly between two live stages** ([RuleSpace] §4 Proposition 4.2(iv), row RS-6): at
`2 ^ j + r` with `r < 2 ^ j - 1`, the column at cell `1` reads `0` — the other half of the witness.
Route: the step identity's two summands both
land beyond the `r`-step support, above (`1 + 2 ^ j`) and below (`1 - 2 ^ j`, exactly where
`r < 2 ^ j - 1` bites). -/
theorem observedColumn_f90_single_one_dead_between (j r : ℕ) (hr : r < 2 ^ j - 1) :
    ((tableRule f90 hq90) ^[2 ^ j + r] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 0 := by
  have h := congrFun (ObservedColumn.coe_tableRule_iterate f90 hq90 (2 ^ j + r)
    (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1
  rw [Finsupp.single_eq_pi_single] at h
  exact h.trans (LocalRuleColumns.column_step90_single_one_dead_between j r hr)

open Classical in
/-- **The column at cell `1`, assembled into one equality**: `observedColumn_f90_single_one_live`
and `observedColumn_f90_single_one_dead_between` cover disjoint, contiguous dyadic blocks
`[2 ^ j, 2 ^ (j + 1) - 1]` (`j ≥ 1`) tiling every step from `1` on, with step `0` separate (the
seed itself misses cell `1`); `Nat.log 2` names the unique block a step `≥ 1` falls in. -/
theorem observedColumn_f90_single_one :
    observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1
      = fun t => if ∃ j, 0 < j ∧ t + 1 = 2 ^ j then 1 else 0 := by
  funext t
  simp only [observedColumn]
  split_ifs with hcase
  · obtain ⟨j, hjpos, hjeq⟩ := hcase
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
    have hlive := observedColumn_f90_single_one_live j'
    rwa [show t = 2 ^ (j' + 1) - 1 from by omega]
  · rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      simp
    · set j := Nat.log 2 t with hj_def
      have h1 : 2 ^ j ≤ t := Nat.pow_log_le_self 2 (by omega)
      have h2 : t < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
      have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · exfalso
          have h2c := h2
          rw [hj0] at h2c
          norm_num at h2c
          apply hcase
          refine ⟨1, one_pos, ?_⟩
          change t + 1 = 2
          omega
        · exact hj0
      have hne : t ≠ 2 ^ (j + 1) - 1 := by
        intro heqt
        apply hcase
        exact ⟨j + 1, by omega, by omega⟩
      have hjge1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      have hr : t - 2 ^ j < 2 ^ j - 1 := by omega
      have hidx : 2 ^ j + (t - 2 ^ j) = t := by omega
      have hdead := observedColumn_f90_single_one_dead_between j (t - 2 ^ j) hr
      rwa [hidx] at hdead

/-- **The column at `f90`'s center-adjacent cell is not eventually periodic** ([RuleSpace] §4
Proposition 4.2(iv), row RS-6), from the single seed: half of [RuleSpace] §4 Remark 4.1's own
witness (`observedColumn_f90_single`, at cell `0`) does not extend to cell `1`. Route: given a
period `P` from `N`, pick `j` past `N + P + 1`; stage `2 ^ j - 1` is live and stage `2 ^ j - 1 + P`
is dead, contradicting the period. -/
theorem not_eventuallyPeriodic_observedColumn_f90_single_one :
    ¬ GrowingComposite.EventuallyPeriodic
      (observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) := by
  rw [ObservedColumn.observedColumn_tableRule_eq_column, Finsupp.single_eq_pi_single]
  exact LocalRuleColumns.not_eventuallyPeriodic_column_step90_single_one

/-! ## Piece 5: the guards -/

/-- **`eventuallyPeriodic_observedColumn_between`'s second end is load-bearing** ([RuleSpace] §4
Proposition 4.2(ii), row RS-5). At `f90`, the single seed, `a = 0`, `i = 1 = b`: the column at
`0` is eventually periodic
(`ObservedColumn.observedColumn_f90_single`), but the column at `1` is not
(`not_eventuallyPeriodic_observedColumn_f90_single_one`) — one settled end does not settle the
cells beside it. -/
theorem eventuallyPeriodic_observedColumn_between_guard :
    ∃ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2)
      (a i b : ℤ), a ≤ i ∧ i ≤ b ∧
      GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ a) ∧
      ¬ GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i) := by
  refine ⟨f90, hq90, Finsupp.single 0 1, 0, 1, 1, by norm_num, le_rfl, ?_, ?_⟩
  · rw [ObservedColumn.observedColumn_f90_single]
    exact ⟨1, 1, one_pos, fun u _ => by
      have h2 : u ≠ 0 := by omega
      simp [h2]⟩
  · exact not_eventuallyPeriodic_observedColumn_f90_single_one

/-- **The speed is load-bearing in `eventuallyPeriodic_observedRay_one`/`_neg_one`** ([RuleSpace] §4
Proposition 4.2(iii), row RS-6). At speed `0` a ray is exactly a column (`observedRay_zero`), and
this column
(`not_eventuallyPeriodic_observedColumn_f90_single_one`'s own witness) is not eventually
periodic. -/
theorem not_eventuallyPeriodic_observedRay_zero_f90 :
    ¬ GrowingComposite.EventuallyPeriodic
      (observedRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1) := by
  rw [observedRay_zero]
  exact not_eventuallyPeriodic_observedColumn_f90_single_one

end DrivenColumns

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'DrivenColumns.eventuallyPeriodic_observedWindow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedWindow_iff

/-- info: 'DrivenColumns.eventuallyPeriodic_observedColumn_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedColumn_between

/-- info: 'DrivenColumns.eventuallyPeriodic_observedColumn_between_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedColumn_between_nonvacuous

/-- info: 'DrivenColumns.observedRay_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.observedRay_zero

/-- info: 'DrivenColumns.eventuallyPeriodic_observedRay_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedRay_one

/-- info: 'DrivenColumns.eventuallyPeriodic_observedRay_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedRay_neg_one

/-- info: 'DrivenColumns.iterate_two_pow_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.iterate_two_pow_f90

/-- info: 'DrivenColumns.observedColumn_f90_single_one_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.observedColumn_f90_single_one_live

/-- info: 'DrivenColumns.observedColumn_f90_single_one_dead_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.observedColumn_f90_single_one_dead_between

/-- info: 'DrivenColumns.observedColumn_f90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.observedColumn_f90_single_one

/-- info: 'DrivenColumns.not_eventuallyPeriodic_observedColumn_f90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.not_eventuallyPeriodic_observedColumn_f90_single_one

/-- info: 'DrivenColumns.eventuallyPeriodic_observedColumn_between_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedColumn_between_guard

/-- info: 'DrivenColumns.not_eventuallyPeriodic_observedRay_zero_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.not_eventuallyPeriodic_observedRay_zero_f90
