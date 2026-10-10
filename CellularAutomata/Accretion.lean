/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Batteries.Tactic.OpenPrivate
public import CellularAutomata.EndpointClasses
public import Mathlib.Data.Int.Interval
import all CellularAutomata.EndpointClasses
-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing width at a quiescent radius-one table: zero or unbounded, decided by one state
([RuleSpace] §3 Proposition 3.1's boundary paragraph)

`EndpointClasses.lean` decides the growing width along the light cone at the `52` tables whose two
endpoints move by exact constants summing to at least one (unbounded) and at the `48` tables whose
diameter never grows (identically zero), and leaves the `28` tables between the classes — one tap,
the other endpoint moving by a state-dependent amount — undecided. This file proves two general
statements that reduce those `28` tables to one question about one state each, and states the
twelve tables of that band whose question is a bounded-diameter statement or a single orbit.

* **Unbounded from one state, at every table.** If a single state `s₀` lies in the growing part of a
  quiescent radius-one table — its orbit has unbounded diameter — then the light cone's growing
  width at stage `t` is at least `n + 2 t + 1 - diam s₀`
  (`linear_le_growingWidth_lightCone_of_mem_growingPart`). The proof needs no exact move on the
  far endpoint: a tap on one side moves that endpoint by exactly one, which keeps the translates
  of `s₀` pairwise non-merging and non-reaching, since a coincidence of two orbits of translates
  would make an orbit of `s₀` a periodic translate of itself and so of bounded diameter.
* **The dichotomy.** At every quiescent table the growing width along the light cone is either
  identically zero or unbounded in `t` (`growingWidth_lightCone_zero_or_unbounded`), according to
  whether the growing part is empty.
* **Bounded diameter forces zero.** `DiamBoundedBy U c` says every orbit's diameter exceeds its
  start's by at most `c`; it empties the growing part and makes the growing width identically zero
  (`growingWidth_lightCone_eq_zero_of_diamBoundedBy`).
* **Reflection.** `reflect` reverses the line, `mirrorTable f` reads the table right to left, and
  `tableRule_mirrorTable_reflect` conjugates the one rule into the other; bounded diameter and
  membership in the growing part carry across (`diamBoundedBy_mirrorTable`,
  `reflect_mem_growingPart_mirrorTable`).
* **The twelve tables.** `f106`, `f166`, `f38`, `f46`, `f66`, `f174` (Wolfram numbers `106`, `166`,
  `38`, `46`, `66`, `174`) and their mirrors (numbers `120`, `180`, `52`, `116`, `24`, `244`) lie in
  neither class. `growingWidth_lightCone_middle_twelve` decides the growing width at all twelve
  with no hypothesis. The diameter at `f166` grows by at most `1` (`diamBoundedBy_f166`), by a
  parity invariant of the last block of set cells, and is attained
  (`diam_iterate_one_single_f166`). The diameter at `f38`, `f46`, `f66`, `f174` grows by at most
  `2` (`diamBoundedBy_f38`, `diamBoundedBy_f46`, `diamBoundedBy_f66`, `diamBoundedBy_f174`), from
  one closure statement (`diamBoundedBy_two_of_endClosure`): a set of pairs of adjacent cells that
  holds of the zero pair, is carried by the two-cell step and forces the next cell to die bounds
  the growth by `2`, with no tap assumed on the left. The last statement of the band, that the
  two-cell state `seedOneOne` has unbounded orbit diameter at `f106`, IS proved here
  (`seedOneOne_mem_growingPart_f106`): `f106`'s rule is injective, the state is no image, and a
  state with a left tap that is no image of an injective rule has an orbit of unbounded diameter
  (`mem_growingPart_of_injective_of_notMem_range`).

## Main results

* `reflect` / `mirrorTable` / `tableRule_mirrorTable_reflect` / `diam_reflect` — the reflection and
  its conjugacy.
* `linear_le_growingWidth_lightCone_of_mem_growingPart` /
  `growingWidth_lightCone_unbounded_of_mem_growingPart` — **the one-state lower bound** and its
  unbounded corollary, at every quiescent table.
* `growingWidth_lightCone_zero_or_unbounded` — **the dichotomy**.
* `DiamBoundedBy` / `growingWidth_lightCone_eq_zero_of_diamBoundedBy` / `diamBoundedBy_mirrorTable`
  / `reflect_mem_growingPart_mirrorTable` — the bounded side and the transport across reflection.
* `f106`, `f166`, `f38`, `f46`, `f66`, `f174`, with their value lists, and
  `not_mem_endpoint_classes_middle_twelve` — the twelve tables are in neither class.
* `mem_growingPart_of_injective_of_notMem_range` / `tableRule_f106_injective` /
  `seedOneOne_notMem_range_f106` / `seedOneOne_mem_growingPart_f106` — the unbounded orbit of the
  two-cell state at `f106`, from a general statement on injective rules with a left tap.
* `diamBoundedBy_two_of_endClosure` / `diamBoundedBy_f38` / `diamBoundedBy_f46` /
  `diamBoundedBy_f66` / `diamBoundedBy_f174` — the closure statement and its four instances, with
  `diamBoundedBy_two_of_endClosure_nonvacuous` and `diam_iterate_one_single_f38`.
* `diamBoundedBy_f166` / `diam_iterate_one_single_f166` — the diameter bound at `f166`, by a parity
  invariant of the last block, and its attainment.
* `growingWidth_lightCone_middle_twelve` and its twelve per-table corollaries, none taking a
  hypothesis.
* `diam_iterate_le_two_mul_of_traffic` / `growingWidth_lightCone_eq_zero_of_traffic` /
  `growingWidth_lightCone_eq_zero_mirror_of_traffic` — **the traffic class**: a table whose every
  set output cell has a clear cell and a set cell to its right, or a set cell to its left and itself
  set, at most doubles the diameter of every orbit. With `f226`, `f194`, `f98` and
  `growingWidth_lightCone_traffic_six` it decides six tables; `traffic_hypothesis_load_bearing`
  shows the class hypothesis fails at `f106` with an unbounded orbit, and
  `diam_seedOneOne_and_step_f226` that the factor is nearly attained.
* Instances: `linear_le_growingWidth_lightCone_f90_single` (the lower bound at `f90` from the
  single cell) and `growingWidth_lightCone_eq_zero_f170`, `diamBoundedBy_mirrorTable_f170` (the
  bounded side at a landed zero table).

## Scope

`growingWidth_lightCone_middle_twelve` takes no hypothesis: the twelve tables are decided. A further
six tables between the classes, `f226`, `f194`, `f98` and their mirrors, are decided by one doubled
diameter bound on a class of tables (`diam_iterate_le_two_mul_of_traffic`, the traffic class); the
tables left are not addressed at all. The lower bound's hypothesis is a
single state in the growing part, and the dichotomy is the statement that this hypothesis is the
only thing between `0` and unbounded.
-/

open private translate_zero translate_apply translate_support translate_ne_zero_iff
  translate_support_min' translate_support_max' translate_support_bound diam_eq' diam_zero'
  tableRule_zero' memWidth_eq_zero_of_empty tableRule_ne_zero_of_rightTap below_min'_eq_zero
  above_max'_eq_zero diam_le_of_support_subset
  from CellularAutomata.EndpointClasses

@[expose] public section

namespace OneTapWidth

open GrowingWidth MemoryWidth GrowingCore GrowingWorld ExtremeTapWidth LightConeWidth
open EndpointClasses (AccretesByEndpoints ZeroByEndpoints f90
  tableRule_min'_of_leftTap tableRule_max'_of_rightTap tableRule_ne_zero_of_leftTap
  diam_tableRule_le_of_noTap diam_tableRule_le_of_leftTap_rightDies
  growingPart_eq_empty_of_diam_le advances_lightCone_tableRule)

-- Shorthand for `EndpointClasses.translate`, which Mathlib's root-level `translate` makes
-- ambiguous once `EndpointClasses` is opened.
local notation "τ" => EndpointClasses.translate

/-! ## Reflection -/

/-- **Reflection of the line**: `Finsupp.mapDomain (fun i => -i)`, sending the cell `i` to `-i`. -/
noncomputable def reflect (s : ℤ →₀ ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.mapDomain (fun i => -i) s

/-- **The mirror of a local table**: the table read right to left, `a b c ↦ f c b a`. -/
def mirrorTable (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 :=
  fun a b c => f c b a

private theorem reflect_apply (s : ℤ →₀ ZMod 2) (x : ℤ) : reflect s x = s (-x) := by
  have h := Finsupp.mapDomain_apply_of_injective
    (neg_injective : Function.Injective (Neg.neg : ℤ → ℤ)) s (-x)
  rw [neg_neg] at h
  exact h

/-- Reflection is an involution. -/
theorem reflect_reflect (s : ℤ →₀ ZMod 2) : reflect (reflect s) = s := by
  ext x
  rw [reflect_apply, reflect_apply, neg_neg]

private theorem mem_support_reflect (s : ℤ →₀ ZMod 2) (x : ℤ) :
    x ∈ (reflect s).support ↔ -x ∈ s.support := by
  simp [Finsupp.mem_support_iff, reflect_apply]

/-- **Reflection conjugates a table's rule into its mirror's**: the mirror table's rule at a
reflected state is the reflection of the table's rule at the state. -/
theorem tableRule_mirrorTable_reflect (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (s : ℤ →₀ ZMod 2) :
    tableRule (mirrorTable f) hq (reflect s) = reflect (tableRule f hq s) := by
  ext x
  have h1 : tableRule (mirrorTable f) hq (reflect s) x =
      f (reflect s (x + 1)) (reflect s x) (reflect s (x - 1)) :=
    tableRule_apply (mirrorTable f) hq _ x
  refine h1.trans ?_
  have h2 : tableRule f hq s (-x) = f (s (-x - 1)) (s (-x)) (s (-x + 1)) :=
    tableRule_apply f hq s (-x)
  rw [reflect_apply, reflect_apply, reflect_apply, reflect_apply, h2]
  have e1 : -(x + 1) = -x - 1 := by ring
  have e2 : -(x - 1) = -x + 1 := by ring
  rw [e1, e2]

/-- **Reflection preserves the diameter**. -/
theorem diam_reflect (s : ℤ →₀ ZMod 2) : diam (reflect s) = diam s := by
  by_cases hs : s.support.Nonempty
  · have hr : (reflect s).support.Nonempty := by
      obtain ⟨x, hx⟩ := hs
      exact ⟨-x, (mem_support_reflect s (-x)).mpr (by simpa using hx)⟩
    have hmin : (reflect s).support.min' hr = - s.support.max' hs := by
      apply le_antisymm
      · apply Finset.min'_le
        rw [mem_support_reflect, neg_neg]
        exact Finset.max'_mem _ _
      · apply Finset.le_min'
        intro y hy
        rw [mem_support_reflect] at hy
        have := Finset.le_max' s.support (-y) hy
        omega
    have hmax : (reflect s).support.max' hr = - s.support.min' hs := by
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        rw [mem_support_reflect] at hy
        have := Finset.min'_le s.support (-y) hy
        omega
      · apply Finset.le_max'
        rw [mem_support_reflect, neg_neg]
        exact Finset.min'_mem _ _
    rw [diam_eq' hr, diam_eq' hs, hmin, hmax]
    have : -s.support.min' hs - -s.support.max' hs = s.support.max' hs - s.support.min' hs := by
      ring
    rw [this]
  · have hz : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst hz
    simp [reflect, diam_zero']

private theorem iterate_mirror_reflect (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (s : ℤ →₀ ZMod 2) :
    ∀ k : ℕ, (tableRule (mirrorTable f) hq)^[k] (reflect s) = reflect ((tableRule f hq)^[k] s)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      iterate_mirror_reflect f hq s k, tableRule_mirrorTable_reflect]

/-! ## Translation, and the rigid-endpoint argument -/

private theorem translate_apply_sub (i x : ℤ) (s : ℤ →₀ ZMod 2) : τ i s x = s (x - i) := by
  have h := translate_apply i (x - i) s
  rwa [sub_add_cancel] at h

private theorem translate_translate (a b : ℤ) (s : ℤ →₀ ZMod 2) :
    τ a (τ b s) = τ (a + b) s := by
  ext x
  rw [translate_apply_sub, translate_apply_sub, translate_apply_sub, sub_sub]

private theorem tableRule_translate (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (k : ℤ) (s : ℤ →₀ ZMod 2) : tableRule f hq (τ k s) = τ k (tableRule f hq s) := by
  ext x
  simp only [tableRule_apply, translate_apply_sub]
  rw [show x - 1 - k = x - k - 1 by ring, show x + 1 - k = x - k + 1 by ring]

private theorem diam_translate (d : ℤ) (s : ℤ →₀ ZMod 2) : diam (τ d s) = diam s := by
  by_cases hs : s.support.Nonempty
  · have hr : (τ d s).support.Nonempty := by
      rw [translate_support]; exact hs.image _
    rw [diam_eq' hr, diam_eq' hs, translate_support_max' d hs hr, translate_support_min' d hs hr]
    have e : s.support.max' hs + d - (s.support.min' hs + d)
        = s.support.max' hs - s.support.min' hs := by ring
    rw [e]
  · have hz : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst hz
    rw [(translate_ne_zero_iff d).mpr rfl]

private theorem iterate_translate' {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hc : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s)) (d : ℤ) (s : ℤ →₀ ZMod 2) :
    ∀ k : ℕ, U^[k] (τ d s) = τ d (U^[k] s)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_translate' hc d s k, hc,
      Function.iterate_succ_apply']

private theorem iterate_pos {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {pos : (ℤ →₀ ZMod 2) → ℤ} {e : ℤ}
    (hU : ∀ s, s ≠ 0 → U s ≠ 0 ∧ pos (U s) = pos s + e) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) :
    ∀ k : ℕ, U^[k] s ≠ 0 ∧ pos (U^[k] s) = pos s + k * e
  | 0 => ⟨hs, by simp⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := iterate_pos hU hs k
    obtain ⟨h3, h4⟩ := hU _ h1
    rw [Function.iterate_succ_apply']
    exact ⟨h3, by rw [h4, h2]; push_cast; ring⟩

private theorem ne_zero_of_mem_growingPart {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} (hU0 : U 0 = 0)
    {s : ℤ →₀ ZMod 2} (hs : s ∈ GrowingPart U diam) : s ≠ 0 := by
  rintro rfl
  obtain ⟨k, hk⟩ := hs 0
  rw [Function.iterate_fixed hU0, diam_zero'] at hk
  exact lt_irrefl _ hk

private theorem translate_mem_growingPart' {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hc : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s)) {s₀ : ℤ →₀ ZMod 2}
    (hs₀ : s₀ ∈ GrowingPart U diam) (i : ℤ) : τ i s₀ ∈ GrowingPart U diam := by
  intro N
  obtain ⟨k, hk⟩ := hs₀ N
  exact ⟨k, by rw [iterate_translate' hc, diam_translate]; exact hk⟩

/-- A state of unbounded orbit diameter is never a translate of an iterate of itself. -/
private theorem no_periodic_translate {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hc : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s)) {y : ℤ →₀ ZMod 2}
    (hy : y ∈ GrowingPart U diam) {d : ℕ} (hd : 0 < d) {c : ℤ} (h : U^[d] y = τ c y) : False := by
  have hclaim : ∀ n : ℕ, U^[d * n] y = τ (n * c) y := by
    intro n
    induction n with
    | zero => simp [translate_zero]
    | succ n ih =>
      rw [show d * (n + 1) = d + d * n by ring, Function.iterate_add_apply, ih,
        iterate_translate' hc, h, translate_translate]
      congr 1
      push_cast
      ring
  obtain ⟨m, hm⟩ := hy (∑ r ∈ Finset.range d, diam (U^[r] y))
  have hmdecomp : m = m % d + d * (m / d) := (Nat.mod_add_div m d).symm
  have hrd : m % d < d := Nat.mod_lt _ hd
  have hU : U^[m] y = τ ((m / d : ℕ) * c) (U^[m % d] y) := by
    conv_lhs => rw [hmdecomp, Function.iterate_add_apply, hclaim, iterate_translate' hc]
  rw [hU, diam_translate] at hm
  have hle : diam (U^[m % d] y) ≤ ∑ r ∈ Finset.range d, diam (U^[r] y) :=
    Finset.single_le_sum (f := fun r => diam (U^[r] y)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hrd)
  omega

/-- **Rigid endpoint**: at an update commuting with translation that moves a position function by
a fixed amount on nonzero states, two iterates of translates of a state in the growing part
coincide only when their exponents and offsets do. -/
private theorem iterate_translate_eq {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    {pos : (ℤ →₀ ZMod 2) → ℤ} {e : ℤ}
    (hc : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s)) (hU0 : U 0 = 0)
    (hposT : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), s ≠ 0 → pos (τ d s) = pos s + d)
    (hU : ∀ s, s ≠ 0 → U s ≠ 0 ∧ pos (U s) = pos s + e) {s₀ : ℤ →₀ ZMod 2}
    (hs₀ : s₀ ∈ GrowingPart U diam) {i i' : ℤ} {j k : ℕ} (hkj : k ≤ j)
    (heq : U^[j] (τ i s₀) = U^[k] (τ i' s₀)) : j = k ∧ i = i' := by
  have hne0 := ne_zero_of_mem_growingPart hU0 hs₀
  have hTi : τ i s₀ ≠ 0 := fun h => hne0 ((translate_ne_zero_iff i).mp h)
  have hTi' : τ i' s₀ ≠ 0 := fun h => hne0 ((translate_ne_zero_iff i').mp h)
  have hp := congrArg pos heq
  rw [(iterate_pos hU hTi j).2, (iterate_pos hU hTi' k).2, hposT _ _ hne0, hposT _ _ hne0] at hp
  by_cases hjk : j = k
  · subst hjk
    exact ⟨rfl, by linarith⟩
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, j = d + k := ⟨j - k, by omega⟩
    have hd : 0 < d := by omega
    have hyG : U^[k] s₀ ∈ GrowingPart U diam := (mem_growingPart_iff_iterate U diam s₀ k).mp hs₀
    have h1 : τ i (U^[d] (U^[k] s₀)) = τ i' (U^[k] s₀) := by
      rw [← iterate_translate' hc i, ← iterate_translate' hc i s₀ k,
        ← Function.iterate_add_apply, heq]
      exact iterate_translate' hc i' s₀ k
    have h2 := congrArg (τ (-i)) h1
    rw [translate_translate, neg_add_cancel, translate_zero, translate_translate] at h2
    have h3 : -i + i' = (d : ℤ) * e := by
      push_cast at hp
      linarith
    rw [h3] at h2
    exact no_periodic_translate hc hyG hd h2

/-- **The lower bound at a rigid endpoint**, for any update commuting with translation: the
engine's window of translates, with `iterate_translate_eq` supplying both the injectivity on the
merge quotient and the antichain. -/
private theorem linear_le_of_rigid {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    {pos : (ℤ →₀ ZMod 2) → ℤ} {e : ℤ}
    (hc : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s)) (hU0 : U 0 = 0)
    (hposT : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), s ≠ 0 → pos (τ d s) = pos s + d)
    (hU : ∀ s, s ≠ 0 → U s ≠ 0 ∧ pos (U s) = pos s + e) {s₀ : ℤ →₀ ZMod 2}
    (hs₀ : s₀ ∈ GrowingPart U diam) (n t : ℕ) :
    ((n + 2 * t + 1 - diam s₀ : ℕ) : ℕ∞) ≤ growingWidth U diam (lightCone n) t := by
  have hne0 : s₀.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (ne_zero_of_mem_growingPart hU0 hs₀)
  set m₀ := s₀.support.min' hne0 with hm₀_def
  set M₀ := s₀.support.max' hne0 with hM₀_def
  set c : ℕ := n + 2 * t + 1 - diam s₀ with hc_def
  set i₀ : ℤ := -(t : ℤ) - m₀ with hi₀_def
  set F : Fin c → (ℤ →₀ ZMod 2) := fun k => τ (i₀ + (k : ℤ)) s₀ with hF_def
  have hFbound : ∀ k : Fin c, ∀ x ∈ (F k).support,
      m₀ + (i₀ + (k : ℤ)) ≤ x ∧ x ≤ M₀ + (i₀ + (k : ℤ)) :=
    fun k _ hx => translate_support_bound (i₀ + (k : ℤ)) hne0 hx
  have hdiam_eq : diam s₀ = (M₀ - m₀).toNat + 1 := diam_eq' hne0
  have hFcone : ∀ k : Fin c, F k ∈ lightCone n t := by
    intro k x hx
    have hb := hFbound k x hx
    have hkc : (k : ℕ) < c := k.isLt
    have hkpos : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
    constructor <;> omega
  have hFgrow : ∀ k : Fin c, F k ∈ GrowingPart U diam :=
    fun k => translate_mem_growingPart' hc hs₀ _
  have hmergeInj : Function.Injective (fun k : Fin c => mergeMk U (F k)) := by
    intro k1 k2 heq
    have hM : Merges U (F k1) (F k2) := Quotient.exact heq
    obtain ⟨k', hk'⟩ := hM
    have hres := iterate_translate_eq hc hU0 hposT hU hs₀ (i := i₀ + (k1 : ℤ))
      (i' := i₀ + (k2 : ℤ)) (j := k') (k := k') le_rfl hk'
    have h2 := hres.2
    exact Fin.ext (by omega)
  set A : Set (MergeQuot U) := Set.range (fun k : Fin c => mergeMk U (F k)) with hA_def
  have hAcard : A.encard = (c : ℕ∞) := by
    rw [hA_def, hmergeInj.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  have hAsub : A ⊆ mergeStage U (fun t' => lightCone n t' ∩ GrowingPart U diam) t := by
    rintro _ ⟨k, rfl⟩
    exact ⟨F k, ⟨hFcone k, hFgrow k⟩, rfl⟩
  have hAanti : IsAntichain (Reaches U) A := by
    rintro _ ⟨k1, rfl⟩ _ ⟨k2, rfl⟩ hne ⟨j, hj⟩
    rw [mergeLaw_iterate_mergeMk] at hj
    have hM : Merges U (U^[j] (F k1)) (F k2) := Quotient.exact hj
    obtain ⟨k', hk'⟩ := hM
    have heq2 : U^[k' + j] (F k1) = U^[k'] (F k2) := by
      rw [Function.iterate_add_apply]; exact hk'
    have hres := iterate_translate_eq hc hU0 hposT hU hs₀ (i := i₀ + (k1 : ℤ))
      (i' := i₀ + (k2 : ℤ)) (j := k' + j) (k := k') (Nat.le_add_right _ _) heq2
    have h2 := hres.2
    exact hne (congrArg (fun k => mergeMk U (F k)) (Fin.ext (show (k1 : ℕ) = (k2 : ℕ) by omega)))
  have hle : (c : ℕ∞) ≤ growingWidth U diam (lightCone n) t := by
    unfold growingWidth
    rw [← hAcard]
    exact le_sSup ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
  rwa [hc_def]

/-! ## The one-state lower bound at a quiescent table -/

private noncomputable def posMin (s : ℤ →₀ ZMod 2) : ℤ :=
  if h : s.support.Nonempty then s.support.min' h else 0

private noncomputable def posMax (s : ℤ →₀ ZMod 2) : ℤ :=
  if h : s.support.Nonempty then s.support.max' h else 0

private theorem posMin_translate (d : ℤ) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) :
    posMin (τ d s) = posMin s + d := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hne' : (τ d s).support.Nonempty := by rw [translate_support]; exact hne.image _
  simp only [posMin, hne, hne', ↓reduceDIte]
  exact translate_support_min' d hne hne'

private theorem posMax_translate (d : ℤ) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) :
    posMax (τ d s) = posMax s + d := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hne' : (τ d s).support.Nonempty := by rw [translate_support]; exact hne.image _
  simp only [posMax, hne, hne', ↓reduceDIte]
  exact translate_support_max' d hne hne'

private theorem zmod2_eq_zero_of_ne_one : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide

/-- **The lower bound from one state, at every quiescent table**: a single state `s₀` whose orbit
under `tableRule f hq` has unbounded diameter forces the growing width along the light cone from
the `n`-cell window to be at least `n + 2 t + 1 - diam s₀` at stage `t`
([RuleSpace] §3 Proposition 3.1's boundary paragraph). No exact move of the far endpoint is assumed:
a tap on one side moves that endpoint by exactly one, which keeps the translates of `s₀`
pairwise non-merging and non-reaching, and a table with neither tap has empty growing part. -/
theorem linear_le_growingWidth_lightCone_of_mem_growingPart
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0} {s₀ : ℤ →₀ ZMod 2}
    (hs₀ : s₀ ∈ GrowingPart (tableRule f hq) diam) (n t : ℕ) :
    ((n + 2 * t + 1 - diam s₀ : ℕ) : ℕ∞) ≤ growingWidth (tableRule f hq) diam (lightCone n) t := by
  by_cases h1 : f 0 0 1 = 1
  · refine linear_le_of_rigid (pos := posMin) (e := -1) (tableRule_translate f hq)
      (tableRule_zero' f hq) (fun d s hs => posMin_translate d hs) ?_ hs₀ n t
    intro s hs
    refine ⟨tableRule_ne_zero_of_leftTap (f := f) (hq := hq) h1 hs, ?_⟩
    have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hne' : (tableRule f hq s).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr (tableRule_ne_zero_of_leftTap (f := f) (hq := hq) h1 hs)
    simp only [posMin, hne, hne', ↓reduceDIte]
    rw [tableRule_min'_of_leftTap (f := f) (hq := hq) h1 hne hne']
    ring
  · by_cases h2 : f 1 0 0 = 1
    · refine linear_le_of_rigid (pos := posMax) (e := 1) (tableRule_translate f hq)
        (tableRule_zero' f hq) (fun d s hs => posMax_translate d hs) ?_ hs₀ n t
      intro s hs
      refine ⟨tableRule_ne_zero_of_rightTap (f := f) (hq := hq) h2 hs, ?_⟩
      have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
      have hne' : (tableRule f hq s).support.Nonempty :=
        Finsupp.support_nonempty_iff.mpr (tableRule_ne_zero_of_rightTap (f := f) (hq := hq) h2 hs)
      simp only [posMax, hne, hne', ↓reduceDIte]
      rw [tableRule_max'_of_rightTap (f := f) (hq := hq) h2 hne hne']
    · exfalso
      have hempty := growingPart_eq_empty_of_diam_le
        (diam_tableRule_le_of_noTap (f := f) (hq := hq) (zmod2_eq_zero_of_ne_one _ h1)
          (zmod2_eq_zero_of_ne_one _ h2))
      rw [hempty] at hs₀
      exact hs₀

/-- **The unbounded corollary**: a single state in the growing part makes the growing width along
the light cone exceed every bound. -/
theorem growingWidth_lightCone_unbounded_of_mem_growingPart
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0} {s₀ : ℤ →₀ ZMod 2}
    (hs₀ : s₀ ∈ GrowingPart (tableRule f hq) diam) (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth (tableRule f hq) diam (lightCone n) t := by
  intro N
  refine ⟨N + diam s₀, ?_⟩
  have hbound := linear_le_growingWidth_lightCone_of_mem_growingPart hs₀ n (N + diam s₀)
  have hlt : N < n + 2 * (N + diam s₀) + 1 - diam s₀ := by omega
  exact lt_of_lt_of_le (by exact_mod_cast hlt) hbound

private theorem growingWidth_eq_zero_of_growingPart_eq_empty
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} (h : GrowingPart U diam = ∅) (n t : ℕ) :
    growingWidth U diam (lightCone n) t = 0 := by
  unfold growingWidth
  exact memWidth_eq_zero_of_empty (by rw [h, Set.inter_empty])

/-- **The dichotomy**: at every quiescent radius-one table the growing width along the light cone
is identically zero or unbounded in the stage, according to whether the growing part is empty. -/
theorem growingWidth_lightCone_zero_or_unbounded
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (n : ℕ) :
    (∀ t, growingWidth (tableRule f hq) diam (lightCone n) t = 0) ∨
      (∀ N : ℕ, ∃ t, (N : ℕ∞) < growingWidth (tableRule f hq) diam (lightCone n) t) := by
  rcases Set.eq_empty_or_nonempty (GrowingPart (tableRule f hq) diam) with h | ⟨s₀, hs₀⟩
  · exact Or.inl (growingWidth_eq_zero_of_growingPart_eq_empty h n)
  · exact Or.inr (growingWidth_lightCone_unbounded_of_mem_growingPart hs₀ n)

/-! ## The bounded side, and transport across reflection -/

/-- **Bounded diameter growth**: every orbit's diameter exceeds its start's by at most `c`. -/
def DiamBoundedBy (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (c : ℕ) : Prop :=
  ∀ (s : ℤ →₀ ZMod 2) (k : ℕ), diam (U^[k] s) ≤ diam s + c

/-- **Bounded diameter growth forces a zero growing width**: no state has an orbit of unbounded
diameter, so the growing part is empty. -/
theorem growingWidth_lightCone_eq_zero_of_diamBoundedBy
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {c : ℕ} (h : DiamBoundedBy U c) (n t : ℕ) :
    growingWidth U diam (lightCone n) t = 0 := by
  apply growingWidth_eq_zero_of_growingPart_eq_empty
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨k, hk⟩ := hs (diam s + c)
  have := h s k
  omega

/-- **Bounded diameter growth passes to the mirror table**. -/
theorem diamBoundedBy_mirrorTable {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    {c : ℕ} (h : DiamBoundedBy (tableRule f hq) c) :
    DiamBoundedBy (tableRule (mirrorTable f) hq) c := by
  intro s k
  have hs : s = reflect (reflect s) := (reflect_reflect s).symm
  rw [hs, iterate_mirror_reflect, diam_reflect, diam_reflect, diam_reflect]
  have := h (reflect s) k
  rwa [diam_reflect] at this

/-- **Membership in the growing part passes to the mirror table**, at the reflected state. -/
theorem reflect_mem_growingPart_mirrorTable {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    {hq : f 0 0 0 = 0} {s : ℤ →₀ ZMod 2} (h : s ∈ GrowingPart (tableRule f hq) diam) :
    reflect s ∈ GrowingPart (tableRule (mirrorTable f) hq) diam := by
  intro N
  obtain ⟨k, hk⟩ := h N
  exact ⟨k, by rw [iterate_mirror_reflect, diam_reflect]; exact hk⟩

/-! ## Bounded diameter growth from a closed set at the right end -/

private theorem iterate_left_zero {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    {m : ℤ} {s : ℤ →₀ ZMod 2} (hs : ∀ i < m, s i = 0) :
    ∀ k : ℕ, ∀ i < m - k, (tableRule f hq)^[k] s i = 0
  | 0 => by simpa using hs
  | k + 1 => by
    intro i hi
    push_cast at hi
    rw [Function.iterate_succ_apply', tableRule_apply,
      iterate_left_zero hs k (i - 1) (by omega), iterate_left_zero hs k i (by omega),
      iterate_left_zero hs k (i + 1) (by omega)]
    exact hq

private theorem f_zero_zero_of_end {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0)
    (hR : f 1 0 0 = 0) (q : ZMod 2) : f q 0 0 = 0 := by
  have : q = 0 ∨ q = 1 := by revert q; decide
  rcases this with rfl | rfl
  · exact hq
  · exact hR

private theorem iterate_right_closure {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hR : f 1 0 0 = 0) (A : ZMod 2 → ZMod 2 → Prop) (h0 : A 0 0)
    (hstep : ∀ u v p q, A p q → A (f u v p) (f v p q)) (hdie : ∀ p q, A p q → f p q 0 = 0)
    {M : ℤ} {s : ℤ →₀ ZMod 2} (hs : ∀ i > M, s i = 0) :
    ∀ k : ℕ, (∀ i > M - k + 2, (tableRule f hq)^[k] s i = 0) ∧
      A ((tableRule f hq)^[k] s (M - k + 1)) ((tableRule f hq)^[k] s (M - k + 2))
  | 0 => by
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa using hs i (by simpa using (by omega : i > M))
    · simp only [Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero]
      rw [hs (M + 1) (by omega), hs (M + 2) (by omega)]
      exact h0
  | k + 1 => by
    obtain ⟨hz, hA⟩ := iterate_right_closure hR A h0 hstep hdie hs k
    have hB : M - ((k + 1 : ℕ) : ℤ) = M - k - 1 := by push_cast; ring
    rw [hB, Function.iterate_succ_apply']
    generalize M - (k : ℤ) = B at hz hA ⊢
    generalize (tableRule f hq)^[k] s = x at hz hA ⊢
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [tableRule_apply]
      have hd : ∀ y : ℤ, y > B + 2 → x y = 0 := hz
      rcases (by omega : i = B + 2 ∨ i = B + 3 ∨ i ≥ B + 4) with h | h | h
      · subst h
        rw [show B + 2 - 1 = B + 1 by ring, hd (B + 2 + 1) (by omega)]
        exact hdie _ _ hA
      · subst h
        rw [show B + 3 - 1 = B + 2 by ring, hd (B + 3) (by omega), hd (B + 3 + 1) (by omega)]
        exact f_zero_zero_of_end hq hR _
      · rw [hd (i - 1) (by omega), hd i (by omega), hd (i + 1) (by omega)]
        exact hq
    · rw [tableRule_apply, tableRule_apply]
      simp only [show B - 1 + 1 = B by ring, show B - 1 + 2 = B + 1 by ring,
        show B + 1 - 1 = B by ring, show B + 1 + 1 = B + 2 by ring]
      exact hstep _ _ _ _ hA

/-- **A closed set at the right end bounds the diameter growth by two**: if the zero pair is in
`A`, `A` is carried by the table's two-cell step `(p, q) ↦ (f u v p, f v p q)` for every left
context `(u, v)`, `A` forces the next cell to die (`f p q 0 = 0`), and a lone cell to the left of
zeros dies (`f 1 0 0 = 0`), then every orbit's diameter exceeds its start's by at most two. No tap
on the left is assumed: a radius-one rule moves the leftmost cell left by at most one a step
([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem diamBoundedBy_two_of_endClosure
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0} (hR : f 1 0 0 = 0)
    (A : ZMod 2 → ZMod 2 → Prop) (h0 : A 0 0)
    (hstep : ∀ u v p q, A p q → A (f u v p) (f v p q))
    (hdie : ∀ p q, A p q → f p q 0 = 0) :
    DiamBoundedBy (tableRule f hq) 2 := by
  intro s k
  by_cases hs : s = 0
  · subst hs
    rw [Function.iterate_fixed (tableRule_zero' f hq)]
    omega
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hL := iterate_left_zero (f := f) (hq := hq) (m := s.support.min' hne)
      (fun i hi => below_min'_eq_zero hne hi) k
    have hRt := (iterate_right_closure (hq := hq) hR A h0 hstep hdie (M := s.support.max' hne)
      (fun i hi => above_max'_eq_zero hne hi) k).1
    have hmm := Finset.min'_le_max' s.support hne
    refine (diam_le_of_support_subset (m := s.support.min' hne - k)
      (M := s.support.max' hne - k + 2) ?_ (by omega)).trans ?_
    · intro x hx
      rw [Finsupp.mem_support_iff] at hx
      constructor
      · by_contra hlt
        exact hx (hL x (by omega))
      · by_contra hlt
        exact hx (hRt x (by omega))
    · rw [diam_eq' hne]
      omega

/-! ## A state outside the range has an orbit of unbounded diameter -/

private theorem eq_of_support_eq {u v : ℤ →₀ ZMod 2} (h : u.support = v.support) : u = v := by
  ext y
  have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  by_cases hy : y ∈ u.support
  · have hy' : y ∈ v.support := h ▸ hy
    rw [Finsupp.mem_support_iff] at hy hy'
    rw [key _ hy, key _ hy']
  · have hy' : y ∉ v.support := h ▸ hy
    rw [Finsupp.notMem_support_iff] at hy hy'
    rw [hy, hy']

private theorem posMin_tableRule_leftTap {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    {hq : f 0 0 0 = 0} (h1 : f 0 0 1 = 1) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) :
    tableRule f hq s ≠ 0 ∧ posMin (tableRule f hq s) = posMin s + -1 := by
  refine ⟨tableRule_ne_zero_of_leftTap (f := f) (hq := hq) h1 hs, ?_⟩
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hne' : (tableRule f hq s).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (tableRule_ne_zero_of_leftTap (f := f) (hq := hq) h1 hs)
  simp only [posMin, hne, hne', ↓reduceDIte]
  rw [tableRule_min'_of_leftTap (f := f) (hq := hq) h1 hne hne']
  ring

/-- **A state outside the range of an injective rule with a left tap has an orbit of unbounded
diameter**: if the update `tableRule f hq` is injective, a cell value `1` to the right of two
clear cells is read as `1`, and a nonzero state `s` is no image of the update, then `s` lies in
the growing part. A bounded orbit would have, translated back by its stage, a fixed leftmost cell
and a bounded diameter, hence finitely many values; two stages would then coincide, and
injectivity would write `s` as an image. The zero state is an image of itself, so the hypothesis
`s ∉ Set.range (tableRule f hq)` already forces `s ≠ 0`
([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem mem_growingPart_of_injective_of_notMem_range
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0} (htap : f 0 0 1 = 1)
    (hinj : Function.Injective (tableRule f hq)) {s : ℤ →₀ ZMod 2}
    (hrange : s ∉ Set.range (tableRule f hq)) : s ∈ GrowingPart (tableRule f hq) diam := by
  have hc := tableRule_translate f hq
  have hs : s ≠ 0 := by
    rintro rfl
    exact hrange ⟨0, tableRule_zero' f hq⟩
  by_contra hnot
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k, diam ((tableRule f hq)^[k] s) ≤ N := by
    by_contra hcon
    push Not at hcon
    exact hnot hcon
  have hpos := iterate_pos (U := tableRule f hq) (pos := posMin) (e := -1)
    (fun s hs => posMin_tableRule_leftTap htap hs) hs
  have hmem : ∀ k : ℕ, (τ (k : ℤ) ((tableRule f hq)^[k] s)).support ∈
      (((Finset.Icc (posMin s) (posMin s + N)).powerset : Finset (Finset ℤ)) : Set (Finset ℤ)) := by
    intro k
    obtain ⟨hk0, hk1⟩ := hpos k
    have hxne : τ (k : ℤ) ((tableRule f hq)^[k] s) ≠ 0 := fun h =>
      hk0 ((translate_ne_zero_iff _).mp h)
    have hne : (τ (k : ℤ) ((tableRule f hq)^[k] s)).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr hxne
    have hpm : posMin (τ (k : ℤ) ((tableRule f hq)^[k] s)) = posMin s := by
      rw [posMin_translate _ hk0, hk1]; ring
    have hpm' : posMin (τ (k : ℤ) ((tableRule f hq)^[k] s)) =
        (τ (k : ℤ) ((tableRule f hq)^[k] s)).support.min' hne := by
      simp [posMin, hne]
    have hd := diam_eq' hne
    rw [diam_translate] at hd
    have hdk := hN k
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro y hy
    have h1 := Finset.min'_le _ y hy
    have h2 := Finset.le_max' _ y hy
    rw [Finset.mem_Icc]
    omega
  obtain ⟨a, b, hab, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => (τ (k : ℤ) ((tableRule f hq)^[k] s)).support) hmem (Finset.finite_toSet _)
  have heq' : τ (a : ℤ) ((tableRule f hq)^[a] s) = τ (b : ℤ) ((tableRule f hq)^[b] s) :=
    eq_of_support_eq heq
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have h1 : τ ((a + d + 1 : ℕ) : ℤ) ((tableRule f hq)^[a + d + 1] s) =
      (tableRule f hq)^[a] (τ ((a + d + 1 : ℕ) : ℤ) ((tableRule f hq)^[d + 1] s)) := by
    rw [iterate_translate' hc, show a + d + 1 = a + (d + 1) by omega, Function.iterate_add_apply]
  have h2 : τ (a : ℤ) ((tableRule f hq)^[a] s) = (tableRule f hq)^[a] (τ (a : ℤ) s) :=
    (iterate_translate' hc _ _ _).symm
  rw [h1, h2] at heq'
  have h3 := (hinj.iterate a) heq'
  have h4 := congrArg (τ (-(a : ℤ))) h3
  rw [translate_translate, translate_translate, neg_add_cancel, translate_zero] at h4
  have hcast : -(a : ℤ) + ((a + d + 1 : ℕ) : ℤ) = ((d + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, Function.iterate_succ_apply', ← hc] at h4
  exact hrange ⟨_, h4.symm⟩

/-! ## The twelve tables between the classes -/

/-- **Table `106`**, `f a b c = c + a * b`:
the Wolfram number `106` sets the bits `4 a + 2 b + c`
listed in `f106_values`. -/
def f106 (a b c : ZMod 2) : ZMod 2 := c + a * b

/-- Quiescence of `f106`. -/
theorem hq106 : f106 0 0 0 = 0 := by decide

/-- The eight values of `f106` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `106`. -/
theorem f106_values :
    f106 0 0 0 = 0 ∧ f106 0 0 1 = 1 ∧ f106 0 1 0 = 0 ∧
      f106 0 1 1 = 1 ∧ f106 1 0 0 = 0 ∧ f106 1 0 1 = 1 ∧
      f106 1 1 0 = 1 ∧ f106 1 1 1 = 0 := by decide

/-- **Table `166`**, `f a b c = c + b + a·b`:
the Wolfram number `166` sets the bits `4 a + 2 b + c`
listed in `f166_values`. -/
def f166 (a b c : ZMod 2) : ZMod 2 := c + b + a * b

/-- Quiescence of `f166`. -/
theorem hq166 : f166 0 0 0 = 0 := by decide

/-- The eight values of `f166` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `166`. -/
theorem f166_values :
    f166 0 0 0 = 0 ∧ f166 0 0 1 = 1 ∧ f166 0 1 0 = 1 ∧
      f166 0 1 1 = 0 ∧ f166 1 0 0 = 0 ∧ f166 1 0 1 = 1 ∧
      f166 1 1 0 = 0 ∧ f166 1 1 1 = 1 := by decide

/-- **Table `38`**, `f a b c = c + b + a·b + a·b·c`:
the Wolfram number `38` sets the bits `4 a + 2 b + c`
listed in `f38_values`. -/
def f38 (a b c : ZMod 2) : ZMod 2 := c + b + a * b + a * b * c

/-- Quiescence of `f38`. -/
theorem hq38 : f38 0 0 0 = 0 := by decide

/-- The eight values of `f38` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `38`. -/
theorem f38_values :
    f38 0 0 0 = 0 ∧ f38 0 0 1 = 1 ∧ f38 0 1 0 = 1 ∧
      f38 0 1 1 = 0 ∧ f38 1 0 0 = 0 ∧ f38 1 0 1 = 1 ∧
      f38 1 1 0 = 0 ∧ f38 1 1 1 = 0 := by decide

/-- **Table `46`**, `f a b c = c + b + b·c + a·b`:
the Wolfram number `46` sets the bits `4 a + 2 b + c`
listed in `f46_values`. -/
def f46 (a b c : ZMod 2) : ZMod 2 := c + b + b * c + a * b

/-- Quiescence of `f46`. -/
theorem hq46 : f46 0 0 0 = 0 := by decide

/-- The eight values of `f46` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `46`. -/
theorem f46_values :
    f46 0 0 0 = 0 ∧ f46 0 0 1 = 1 ∧ f46 0 1 0 = 1 ∧
      f46 0 1 1 = 1 ∧ f46 1 0 0 = 0 ∧ f46 1 0 1 = 1 ∧
      f46 1 1 0 = 0 ∧ f46 1 1 1 = 0 := by decide

/-- **Table `66`**, `f a b c = c + b·c + a·c + a·b`:
the Wolfram number `66` sets the bits `4 a + 2 b + c`
listed in `f66_values`. -/
def f66 (a b c : ZMod 2) : ZMod 2 := c + b * c + a * c + a * b

/-- Quiescence of `f66`. -/
theorem hq66 : f66 0 0 0 = 0 := by decide

/-- The eight values of `f66` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `66`. -/
theorem f66_values :
    f66 0 0 0 = 0 ∧ f66 0 0 1 = 1 ∧ f66 0 1 0 = 0 ∧
      f66 0 1 1 = 0 ∧ f66 1 0 0 = 0 ∧ f66 1 0 1 = 0 ∧
      f66 1 1 0 = 1 ∧ f66 1 1 1 = 0 := by decide

/-- **Table `174`**, `f a b c = c + b + b·c + a·b + a·b·c`:
the Wolfram number `174` sets the bits `4 a + 2 b + c`
listed in `f174_values`. -/
def f174 (a b c : ZMod 2) : ZMod 2 := c + b + b * c + a * b + a * b * c

/-- Quiescence of `f174`. -/
theorem hq174 : f174 0 0 0 = 0 := by decide

/-- The eight values of `f174` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `174`. -/
theorem f174_values :
    f174 0 0 0 = 0 ∧ f174 0 0 1 = 1 ∧ f174 0 1 0 = 1 ∧
      f174 0 1 1 = 1 ∧ f174 1 0 0 = 0 ∧ f174 1 0 1 = 1 ∧
      f174 1 1 0 = 0 ∧ f174 1 1 1 = 1 := by decide

/-- **The diameter grows by at most two at `f38`**: the set of pairs other than `(0, 1)` is
closed at the right end (`diamBoundedBy_two_of_endClosure`)
([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem diamBoundedBy_f38 : DiamBoundedBy (tableRule f38 hq38) 2 :=
  diamBoundedBy_two_of_endClosure (by decide) (fun p q => ¬ (p = 0 ∧ q = 1)) (by decide) (by decide)
    (by decide)

/-- **The diameter grows by at most two at `f46`**: the set of pairs other than `(0, 1)` is
closed at the right end (`diamBoundedBy_two_of_endClosure`)
([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem diamBoundedBy_f46 : DiamBoundedBy (tableRule f46 hq46) 2 :=
  diamBoundedBy_two_of_endClosure (by decide) (fun p q => ¬ (p = 0 ∧ q = 1)) (by decide) (by decide)
    (by decide)

/-- **The diameter grows by at most two at `f66`**: the set of pairs other than `(1, 1)` is
closed at the right end (`diamBoundedBy_two_of_endClosure`)
([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem diamBoundedBy_f66 : DiamBoundedBy (tableRule f66 hq66) 2 :=
  diamBoundedBy_two_of_endClosure (by decide) (fun p q => ¬ (p = 1 ∧ q = 1)) (by decide) (by decide)
    (by decide)

/-- **The diameter grows by at most two at `f174`**: the set of pairs other than `(0, 1)` is
closed at the right end (`diamBoundedBy_two_of_endClosure`)
([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem diamBoundedBy_f174 : DiamBoundedBy (tableRule f174 hq174) 2 :=
  diamBoundedBy_two_of_endClosure (by decide) (fun p q => ¬ (p = 0 ∧ q = 1)) (by decide) (by decide)
    (by decide)

/-! ## Table `166`: the diameter grows by at most one -/

/-- A block of set cells ending at `m` of even length: a start `L` with `m = L + 2 k + 1`, every
cell of `[L, m]` set and the cell left of `L` clear. -/
private def EvenEnd (x : ℤ → ZMod 2) (m : ℤ) : Prop :=
  ∃ (L : ℤ) (k : ℕ), L + 2 * (k : ℤ) + 1 = m ∧ (∀ i, L ≤ i → i ≤ m → x i = 1) ∧ x (L - 1) = 0

/-- The right-end invariant at `f166`: nothing is set to the right of `m`, and when `m` is set the
block of set cells ending at `m` has even length. -/
private def RightEnd (x : ℤ → ZMod 2) (m : ℤ) : Prop :=
  (∀ i, m < i → x i = 0) ∧ (x m = 1 → EvenEnd x m)

private theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- A start `L` (a set cell with a clear cell to its left) followed to its left by single set
cells at alternate positions: the image `y`, read at the same cells, is set on a run `[L', L - 1]`
of odd length, with the cell left of the run clear. -/
private theorem run_left_f166 (x y : ℤ → ZMod 2)
    (hy : ∀ i, y i = f166 (x (i - 1)) (x i) (x (i + 1))) (lo : ℤ) (hlo : ∀ i, i < lo → x i = 0) :
    ∀ n : ℕ, ∀ L : ℤ, L = lo + n → x L = 1 → x (L - 1) = 0 →
      ∃ (L' : ℤ) (k : ℕ), L' + 2 * (k : ℤ) = L - 1 ∧ (∀ i, L' ≤ i → i ≤ L - 1 → y i = 1) ∧
        y (L' - 1) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hL hxL hxL1
    have hyL1 := hy (L - 1)
    rw [show L - 1 - 1 = L - 2 by ring, show L - 1 + 1 = L by ring, hxL, hxL1] at hyL1
    have hyL2 := hy (L - 2)
    rw [show L - 2 - 1 = L - 3 by ring, show L - 2 + 1 = L - 1 by ring, hxL1] at hyL2
    have hy1 : y (L - 1) = 1 := by
      rcases zmod2_cases (x (L - 2)) with h | h <;> rw [h] at hyL1 <;> rw [hyL1] <;> decide
    have short : y (L - 2) = 0 → ∃ (L' : ℤ) (k : ℕ), L' + 2 * (k : ℤ) = L - 1 ∧
        (∀ i, L' ≤ i → i ≤ L - 1 → y i = 1) ∧ y (L' - 1) = 0 := by
      intro h0
      refine ⟨L - 1, 0, by ring, fun i h1 h2 => ?_, ?_⟩
      · have : i = L - 1 := by omega
        subst this; exact hy1
      · rw [show L - 1 - 1 = L - 2 by ring]; exact h0
    rcases zmod2_cases (x (L - 2)) with h2 | h2
    · apply short
      rw [hyL2, h2]; rcases zmod2_cases (x (L - 3)) with h | h <;> rw [h] <;> decide
    · rcases zmod2_cases (x (L - 3)) with h3 | h3
      · have hlo2 : lo ≤ L - 2 := by
          by_contra hc
          have := hlo (L - 2) (by omega)
          rw [h2] at this; exact absurd this (by decide)
        obtain ⟨L', k, hk, hrun, hL'⟩ :=
          ih (n - 2) (by omega) (L - 2) (by push_cast [Nat.cast_sub (by omega : 2 ≤ n)]; omega) h2
            (by rw [show L - 2 - 1 = L - 3 by ring]; exact h3)
        have hy2 : y (L - 2) = 1 := by rw [hyL2, h2, h3]; decide
        refine ⟨L', k + 1, by push_cast; omega, fun i h1 h4 => ?_, hL'⟩
        by_cases hi : i ≤ L - 2 - 1
        · exact hrun i h1 hi
        · have : i = L - 2 ∨ i = L - 1 := by omega
          rcases this with rfl | rfl
          · exact hy2
          · exact hy1
      · apply short
        rw [hyL2, h2, h3]; decide

/-- **The right-end invariant is carried by one step at `f166`**: if nothing is set right of `m`
and the block ending at `m` has even length whenever `m` is set, then the image has nothing set
right of `m - 1` and the same property there. -/
private theorem rightEnd_step_f166 (x y : ℤ →₀ ZMod 2)
    (hy : ∀ i, y i = f166 (x (i - 1)) (x i) (x (i + 1))) (m : ℤ) (hx : RightEnd x m) :
    RightEnd y (m - 1) := by
  obtain ⟨hz, hev⟩ := hx
  obtain ⟨lo, hlo⟩ := x.support.bddBelow
  have hlo' : ∀ i, i < lo → x i = 0 := by
    intro i hi
    by_contra hc
    have := hlo (Finsupp.mem_support_iff.mpr hc)
    omega
  have ym : y m = 0 := by
    rw [hy, hz (m + 1) (by omega)]
    rcases zmod2_cases (x m) with h | h
    · rw [h]; rcases zmod2_cases (x (m - 1)) with h' | h' <;> rw [h'] <;> decide
    · obtain ⟨L, k, hk, hrun, -⟩ := hev h
      rw [hrun (m - 1) (by omega) (by omega), h]; decide
  refine ⟨fun i hi => ?_, fun hE => ?_⟩
  · rcases (by omega : i = m ∨ m < i) with rfl | h
    · exact ym
    · rw [hy, hz i h, hz (i + 1) (by omega)]
      rcases zmod2_cases (x (i - 1)) with h' | h' <;> rw [h'] <;> decide
  · by_cases hxm : x m = 1
    · obtain ⟨L, k, hk, hrun, hL⟩ := hev hxm
      have hxE : x (m - 1) = 1 := hrun (m - 1) (by omega) (by omega)
      have hyE := hy (m - 1)
      rw [show m - 1 + 1 = m by ring, hxE, hxm] at hyE
      have hxE1 : x (m - 1 - 1) = 1 := by
        rw [hyE] at hE
        rcases zmod2_cases (x (m - 1 - 1)) with h | h
        · rw [h] at hE; exact absurd hE (by decide)
        · exact h
      have hk1 : 1 ≤ k := by
        by_contra hc
        have : k = 0 := by omega
        subst this
        have : m - 1 - 1 = L - 1 := by omega
        rw [this, hL] at hxE1; exact absurd hxE1 (by decide)
      refine ⟨L + 1, k - 1, by push_cast [Nat.cast_sub hk1]; omega, fun i h1 h2 => ?_, ?_⟩
      · rw [hy, hrun (i - 1) (by omega) (by omega), hrun i (by omega) (by omega),
          hrun (i + 1) (by omega) (by omega)]
        decide
      · rw [show L + 1 - 1 = L by ring, hy, hL, hrun L le_rfl (by omega),
          hrun (L + 1) (by omega) (by omega)]
        decide
    · have hxm0 : x m = 0 := (zmod2_cases _).resolve_right hxm
      have hyE := hy (m - 1)
      rw [show m - 1 + 1 = m by ring, hxm0] at hyE
      have hxE : x (m - 1) = 1 ∧ x (m - 1 - 1) = 0 := by
        rw [hyE] at hE
        rcases zmod2_cases (x (m - 1)) with h | h <;>
          rcases zmod2_cases (x (m - 1 - 1)) with h' | h' <;> rw [h, h'] at hE <;>
          first | exact ⟨h, h'⟩ | exact absurd hE (by decide)
      have hlo2 : lo ≤ m - 1 := by
        by_contra hc
        have := hlo' (m - 1) (by omega)
        rw [hxE.1] at this; exact absurd this (by decide)
      obtain ⟨L', k, hk, hrun, hL'⟩ := run_left_f166 x y hy lo hlo' (m - 1 - lo).toNat (m - 1)
        (by omega) hxE.1 hxE.2
      have hyE1 : y (m - 1) = 1 := by
        rw [hyE, hxE.1, hxE.2]; decide
      refine ⟨L', k, by omega, fun i h1 h2 => ?_, hL'⟩
      by_cases hi : i ≤ m - 1 - 1
      · exact hrun i h1 hi
      · have : i = m - 1 := by omega
        subst this; exact hyE1

private theorem rightEnd_iterate_f166 (s : ℤ →₀ ZMod 2) (m : ℤ) (hs : RightEnd s m) :
    ∀ k : ℕ, RightEnd ((tableRule f166 hq166)^[k] s) (m - k)
  | 0 => by simpa using hs
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    have := rightEnd_step_f166 ((tableRule f166 hq166)^[k] s)
      (tableRule f166 hq166 ((tableRule f166 hq166)^[k] s))
      (fun i => tableRule_apply f166 hq166 _ i) _ (rightEnd_iterate_f166 s m hs k)
    rwa [show m - ((k + 1 : ℕ) : ℤ) = m - k - 1 by push_cast; ring]

/-- **The diameter grows by at most one at `f166`**: the block of set cells ending at the rightmost
cell, with its parity, is carried one step at a time, and the rightmost cell moves left by one a
step up to a fixed offset of one ([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem diamBoundedBy_f166 : DiamBoundedBy (tableRule f166 hq166) 1 := by
  intro s k
  by_cases hs : s = 0
  · subst hs
    rw [Function.iterate_fixed (tableRule_zero' f166 hq166)]
    omega
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hL := iterate_left_zero (f := f166) (hq := hq166) (m := s.support.min' hne)
      (fun i hi => below_min'_eq_zero hne hi) k
    have hRt := (rightEnd_iterate_f166 s (s.support.max' hne + 1)
      ⟨fun i hi => above_max'_eq_zero hne (by omega),
        fun h => absurd h (by rw [above_max'_eq_zero hne (by omega)]; decide)⟩ k).1
    have hmm := Finset.min'_le_max' s.support hne
    refine (diam_le_of_support_subset (m := s.support.min' hne - k)
      (M := s.support.max' hne - k + 1) ?_ (by omega)).trans ?_
    · intro x hx
      rw [Finsupp.mem_support_iff] at hx
      constructor
      · by_contra hlt
        exact hx (hL x (by omega))
      · by_contra hlt
        exact hx (hRt x (by omega))
    · rw [diam_eq' hne]
      omega

/-- Joint satisfaction of the four hypotheses of `diamBoundedBy_two_of_endClosure`, at the table
`f38` and the set of pairs other than `(0, 1)`. -/
theorem diamBoundedBy_two_of_endClosure_nonvacuous :
    f38 1 0 0 = 0 ∧ (¬ ((0 : ZMod 2) = 0 ∧ (0 : ZMod 2) = 1)) ∧
      (∀ u v p q : ZMod 2, ¬ (p = 0 ∧ q = 1) → ¬ (f38 u v p = 0 ∧ f38 v p q = 1)) ∧
      (∀ p q : ZMod 2, ¬ (p = 0 ∧ q = 1) → f38 p q 0 = 0) :=
  ⟨by decide, by decide, by decide, by decide⟩

private theorem diam_single_zero_one : diam (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = 1 := by
  have hne : (Finsupp.single (0 : ℤ) (1 : ZMod 2)).support.Nonempty :=
    ⟨0, Finsupp.mem_support_iff.mpr (by simp)⟩
  rw [diam_eq' hne]
  have hx : ∀ x ∈ (Finsupp.single (0 : ℤ) (1 : ZMod 2)).support, x = 0 := fun x hx => by
    simpa using hx
  have h1 := hx _ (Finset.min'_mem _ hne)
  have h2 := hx _ (Finset.max'_mem _ hne)
  omega

/-- **The diameter grows at `f38`**: one step from the one-cell state at `0` gives a diameter one
more than the state's, so the growth bound of `diamBoundedBy_f38` is not vacuous at this table. -/
theorem diam_iterate_one_single_f38 :
    diam ((tableRule f38 hq38)^[1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) =
      diam (Finsupp.single (0 : ℤ) (1 : ZMod 2)) + 1 := by
  rw [diam_single_zero_one, Function.iterate_one]
  set u := tableRule f38 hq38 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) with hu
  have hval : ∀ x : ℤ, u x = if x = -1 ∨ x = 0 then 1 else 0 := by
    intro x
    rw [hu, tableRule_apply]
    simp only [Finsupp.single_apply]
    split_ifs <;> first | (exfalso; omega) | decide
  have hm1 : u (-1) ≠ 0 := by rw [hval]; simp
  have hm0 : u 0 ≠ 0 := by rw [hval]; simp
  have hne : u.support.Nonempty := ⟨0, Finsupp.mem_support_iff.mpr hm0⟩
  have hlo := Finset.min'_le u.support (-1) (Finsupp.mem_support_iff.mpr hm1)
  have hhi := Finset.le_max' u.support 0 (Finsupp.mem_support_iff.mpr hm0)
  have hup : diam u ≤ 2 := by
    have := diam_le_of_support_subset (t' := u) (m := -1) (M := 0) (fun x hx => by
      rw [Finsupp.mem_support_iff, hval] at hx
      by_contra hc
      apply hx
      exact ite_eq_right_iff.mpr (fun h => absurd h (by omega))) (by omega)
    simpa using this
  rw [diam_eq' hne] at hup ⊢
  omega

/-- **The diameter grows at `f166`**: one step from the one-cell state at `0` gives a diameter one
more than the state's, so the growth bound of `diamBoundedBy_f166` is attained. -/
theorem diam_iterate_one_single_f166 :
    diam ((tableRule f166 hq166)^[1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) =
      diam (Finsupp.single (0 : ℤ) (1 : ZMod 2)) + 1 := by
  rw [diam_single_zero_one, Function.iterate_one]
  set u := tableRule f166 hq166 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) with hu
  have hval : ∀ x : ℤ, u x = if x = -1 ∨ x = 0 then 1 else 0 := by
    intro x
    rw [hu, tableRule_apply]
    simp only [Finsupp.single_apply]
    split_ifs <;> first | (exfalso; omega) | decide
  have hm1 : u (-1) ≠ 0 := by rw [hval]; simp
  have hm0 : u 0 ≠ 0 := by rw [hval]; simp
  have hne : u.support.Nonempty := ⟨0, Finsupp.mem_support_iff.mpr hm0⟩
  have hlo := Finset.min'_le u.support (-1) (Finsupp.mem_support_iff.mpr hm1)
  have hhi := Finset.le_max' u.support 0 (Finsupp.mem_support_iff.mpr hm0)
  have hup : diam u ≤ 2 := by
    have := diam_le_of_support_subset (t' := u) (m := -1) (M := 0) (fun x hx => by
      rw [Finsupp.mem_support_iff, hval] at hx
      by_contra hc
      apply hx
      exact ite_eq_right_iff.mpr (fun h => absurd h (by omega))) (by omega)
    simpa using this
  rw [diam_eq' hne] at hup ⊢
  omega

/-- **The two-cell state** `{0, 1}`: cells `0` and `1` set, all others clear. -/
noncomputable def seedOneOne : ℤ →₀ ZMod 2 := Finsupp.single 0 1 + Finsupp.single 1 1

set_option maxRecDepth 8000 in
/-- **None of the twelve tables is in either class**: the six tables above and their mirrors lie
in neither `AccretesByEndpoints` nor `ZeroByEndpoints`. -/
theorem not_mem_endpoint_classes_middle_twelve :
    ∀ f ∈ ([f106, f166, f38, f46, f66, f174, mirrorTable f106, mirrorTable f166, mirrorTable f38,
        mirrorTable f46, mirrorTable f66, mirrorTable f174] :
        List (ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)),
      ¬ AccretesByEndpoints f ∧ ¬ ZeroByEndpoints f := by
  decide

/-! ## Table `106`: the two-cell state is no image -/

private theorem tableRule_f106_apply (s : ℤ →₀ ZMod 2) (i : ℤ) :
    tableRule f106 hq106 s i = s (i + 1) + s (i - 1) * s i := by
  rw [tableRule_apply]
  rfl

private theorem exists_below_zero (x y : ℤ →₀ ZMod 2) :
    ∃ B : ℤ, ∀ i ≤ B, x i = 0 ∧ y i = 0 := by
  refine ⟨-((x.support ∪ y.support).sup Int.natAbs : ℕ) - 1, fun i hi => ?_⟩
  have hb : ∀ z : ℤ →₀ ZMod 2, z.support ⊆ x.support ∪ y.support → z i = 0 := by
    intro z hz
    by_contra hne
    have hmem : i ∈ z.support := Finsupp.mem_support_iff.mpr hne
    have := Finset.le_sup (f := Int.natAbs) (hz hmem)
    omega
  exact ⟨hb x Finset.subset_union_left, hb y Finset.subset_union_right⟩

/-- **The rule of table `106` is injective**: the value at `i + 1` is the image at `i` plus the
product of the values at `i - 1` and `i`, so two states with the same image agree below a common
cell and then at every cell above it, by induction on the cell
([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem tableRule_f106_injective : Function.Injective (tableRule f106 hq106) := by
  intro x y hxy
  have hrec : ∀ i : ℤ, x (i - 1) = y (i - 1) → x i = y i → x (i + 1) = y (i + 1) := by
    intro i h1 h2
    have h := DFunLike.congr_fun hxy i
    rw [tableRule_f106_apply, tableRule_f106_apply, h1, h2] at h
    exact add_right_cancel h
  obtain ⟨B, hB⟩ := exists_below_zero x y
  have hall : ∀ n : ℕ, x (B + n) = y (B + n) ∧ x (B + n + 1) = y (B + n + 1) := by
    intro n
    induction n with
    | zero =>
      have h0 : x B = y B := by rw [(hB B le_rfl).1, (hB B le_rfl).2]
      refine ⟨by simpa using h0, ?_⟩
      have := hrec B (by rw [(hB (B - 1) (by omega)).1, (hB (B - 1) (by omega)).2]) h0
      simpa using this
    | succ n ih =>
      refine ⟨by push_cast; rw [← add_assoc]; exact ih.2, ?_⟩
      have := hrec (B + n + 1) (by simpa using ih.1) ih.2
      push_cast
      rw [show B + (n + 1) + 1 = B + n + 1 + 1 by ring]
      exact this
  ext i
  by_cases hi : i ≤ B
  · rw [(hB i hi).1, (hB i hi).2]
  · have hn : B + ((i - B).toNat : ℤ) = i := by omega
    have := (hall (i - B).toNat).1
    rwa [hn] at this

private theorem seedOneOne_apply (i : ℤ) :
    seedOneOne i = if i = 0 then 1 else if i = 1 then 1 else 0 := by
  by_cases h0 : i = 0
  · subst h0; simp [seedOneOne]
  · by_cases h1 : i = 1
    · subst h1; simp [seedOneOne]
    · simp [seedOneOne, h0, h1]

/-- **The two-cell state is no image at table `106`**: a preimage would have its leftmost cell at
`1`, and the recursion of `tableRule_f106_injective` would then set every cell from `1` on, against
finite support ([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem seedOneOne_notMem_range_f106 : seedOneOne ∉ Set.range (tableRule f106 hq106) := by
  rintro ⟨x, hx⟩
  have h1 : f106 0 0 1 = 1 := by decide
  have hseed0 : seedOneOne 0 = 1 := by rw [seedOneOne_apply]; simp
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [tableRule_zero' f106 hq106] at hx
    have := hseed0
    rw [← hx] at this
    simp at this
  have hne : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hxne
  have hne' : (tableRule f106 hq106 x).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr
      (tableRule_ne_zero_of_leftTap (f := f106) (hq := hq106) h1 hxne)
  have hmin := tableRule_min'_of_leftTap (f := f106) (hq := hq106) h1 hne hne'
  have hmin0 : (tableRule f106 hq106 x).support.min' hne' = 0 := by
    apply le_antisymm
    · apply Finset.min'_le
      rw [Finsupp.mem_support_iff, hx, hseed0]; exact one_ne_zero
    · apply Finset.le_min'
      intro y hy
      rw [Finsupp.mem_support_iff, hx, seedOneOne_apply] at hy
      by_contra hlt
      have h0 : y ≠ 0 := by omega
      have h1' : y ≠ 1 := by omega
      simp [h0, h1'] at hy
  have hmin' : x.support.min' hne = 1 := by omega
  have hx0 : x 0 = 0 := by
    by_contra h
    have := Finset.min'_le x.support 0 (Finsupp.mem_support_iff.mpr h)
    omega
  have hx1 : x 1 = 1 := by
    have h := Finsupp.mem_support_iff.mp (hmin' ▸ Finset.min'_mem x.support hne)
    have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact key _ h
  have hrec : ∀ i : ℤ, x (i + 1) = seedOneOne i + x (i - 1) * x i := by
    intro i
    have h := DFunLike.congr_fun hx i
    rw [tableRule_f106_apply] at h
    have h2 : ∀ a b : ZMod 2, a = a + b + b := by decide
    rw [← h]
    exact h2 _ _
  have hall : ∀ n : ℕ, x ((n : ℤ) + 1) = 1 ∧ x ((n : ℤ) + 2) = 1 := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simpa using hx1, ?_⟩
      have := hrec 1
      rw [seedOneOne_apply] at this
      norm_num at this
      simp only [Nat.cast_zero, zero_add]
      rw [this, hx0, hx1]
      simp
    | succ n ih =>
      refine ⟨by push_cast; rw [show (n : ℤ) + 1 + 1 = n + 2 by ring]; exact ih.2, ?_⟩
      have := hrec ((n : ℤ) + 2)
      rw [seedOneOne_apply, show (n : ℤ) + 2 - 1 = n + 1 by ring, ih.1, ih.2] at this
      have e1 : ((n : ℤ) + 2 = 0) = False := by simp; omega
      have e2 : ((n : ℤ) + 2 = 1) = False := by simp; omega
      simp only [e1, e2, ite_false] at this
      push_cast
      rw [show (n : ℤ) + 1 + 2 = n + 2 + 1 by ring, this]
      simp
  have hS := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.mpr
    (show x ((x.support.sup Int.natAbs : ℕ) + 1 : ℤ) ≠ 0 by
      rw [(hall _).1]; exact one_ne_zero))
  omega

/-- **The two-cell state has an orbit of unbounded diameter at table `106`**, which discharges
the hypothesis of `growingWidth_lightCone_middle_twelve` on that table
([RuleSpace] §3 Proposition 3.2's boundary paragraph). -/
theorem seedOneOne_mem_growingPart_f106 :
    seedOneOne ∈ GrowingPart (tableRule f106 hq106) diam :=
  mem_growingPart_of_injective_of_notMem_range (by decide) tableRule_f106_injective
    seedOneOne_notMem_range_f106

/-- Joint satisfaction of the three hypotheses of
`mem_growingPart_of_injective_of_notMem_range`, at the table `f106` and the two-cell state
`seedOneOne`. -/
theorem mem_growingPart_of_injective_of_notMem_range_nonvacuous :
    f106 0 0 1 = 1 ∧ Function.Injective (tableRule f106 hq106) ∧
      seedOneOne ∉ Set.range (tableRule f106 hq106) :=
  ⟨by decide, tableRule_f106_injective, seedOneOne_notMem_range_f106⟩

/-! ## The per-table statements -/

/-- **Unbounded growing width at `f106`**: the orbit of `seedOneOne` under `f106` has unbounded
diameter (`seedOneOne_mem_growingPart_f106`). -/
theorem growingWidth_lightCone_unbounded_f106 (n : ℕ) :
    ∀ N : ℕ, ∃ t, (N : ℕ∞) <
      growingWidth (tableRule f106 hq106) diam (lightCone n) t :=
  growingWidth_lightCone_unbounded_of_mem_growingPart seedOneOne_mem_growingPart_f106 n

/-- **Unbounded growing width at `mirrorTable f106`**: the orbit of `seedOneOne` under `f106` has
unbounded diameter (`seedOneOne_mem_growingPart_f106`), and reflection carries it across. -/
theorem growingWidth_lightCone_unbounded_mirror_f106 (n : ℕ) :
    ∀ N : ℕ, ∃ t, (N : ℕ∞) <
      growingWidth (tableRule (mirrorTable f106) hq106) diam (lightCone n) t :=
  growingWidth_lightCone_unbounded_of_mem_growingPart
    (reflect_mem_growingPart_mirrorTable seedOneOne_mem_growingPart_f106) n

/-- **Identically zero growing width at `f38`**: the diameter along `f38`'s orbits grows by at
most `2` (`diamBoundedBy_f38`). -/
theorem growingWidth_lightCone_eq_zero_f38 (n t : ℕ) :
    growingWidth (tableRule f38 hq38) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy diamBoundedBy_f38 n t

/-- **Identically zero growing width at `mirrorTable f38`**: the diameter along `f38`'s orbits
grows by at most `2` (`diamBoundedBy_f38`), and the bound passes to the mirror. -/
theorem growingWidth_lightCone_eq_zero_mirror_f38 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f38) hq38) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy (diamBoundedBy_mirrorTable diamBoundedBy_f38)
    n t

/-- **Identically zero growing width at `f46`**: the diameter along `f46`'s orbits grows by at
most `2` (`diamBoundedBy_f46`). -/
theorem growingWidth_lightCone_eq_zero_f46 (n t : ℕ) :
    growingWidth (tableRule f46 hq46) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy diamBoundedBy_f46 n t

/-- **Identically zero growing width at `mirrorTable f46`**: the diameter along `f46`'s orbits
grows by at most `2` (`diamBoundedBy_f46`), and the bound passes to the mirror. -/
theorem growingWidth_lightCone_eq_zero_mirror_f46 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f46) hq46) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy (diamBoundedBy_mirrorTable diamBoundedBy_f46)
    n t

/-- **Identically zero growing width at `f66`**: the diameter along `f66`'s orbits grows by at
most `2` (`diamBoundedBy_f66`). -/
theorem growingWidth_lightCone_eq_zero_f66 (n t : ℕ) :
    growingWidth (tableRule f66 hq66) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy diamBoundedBy_f66 n t

/-- **Identically zero growing width at `mirrorTable f66`**: the diameter along `f66`'s orbits
grows by at most `2` (`diamBoundedBy_f66`), and the bound passes to the mirror. -/
theorem growingWidth_lightCone_eq_zero_mirror_f66 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f66) hq66) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy (diamBoundedBy_mirrorTable diamBoundedBy_f66)
    n t

/-- **Identically zero growing width at `f174`**: the diameter along `f174`'s orbits grows by at
most `2` (`diamBoundedBy_f174`). -/
theorem growingWidth_lightCone_eq_zero_f174 (n t : ℕ) :
    growingWidth (tableRule f174 hq174) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy diamBoundedBy_f174 n t

/-- **Identically zero growing width at `mirrorTable f174`**: the diameter along `f174`'s orbits
grows by at most `2` (`diamBoundedBy_f174`), and the bound passes to the mirror. -/
theorem growingWidth_lightCone_eq_zero_mirror_f174 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f174) hq174) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy (diamBoundedBy_mirrorTable diamBoundedBy_f174)
    n t

/-- **Identically zero growing width at `f166`**: the diameter along `f166`'s orbits grows by at
most `1` (`diamBoundedBy_f166`). -/
theorem growingWidth_lightCone_eq_zero_f166 (n t : ℕ) :
    growingWidth (tableRule f166 hq166) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy diamBoundedBy_f166 n t

/-- **Identically zero growing width at `mirrorTable f166`**: the diameter along `f166`'s orbits
grows by at most `1` (`diamBoundedBy_f166`), and the bound passes to the mirror. -/
theorem growingWidth_lightCone_eq_zero_mirror_f166 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f166) hq166) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy (diamBoundedBy_mirrorTable diamBoundedBy_f166)
    n t

/-- **The twelve tables between the classes**
([RuleSpace] §3 Proposition 3.1's boundary paragraph). For every window width `n`: the growing
width along the light cone is unbounded in the stage at `f106` and at its mirror; and it is zero
at every stage at `f38`, `f46`, `f66`, `f174` and `f166` and at their five mirrors. The unbounded
side is proved in this file (`seedOneOne_mem_growingPart_f106`), and so are the diameter bounds at
`f38`, `f46`, `f66`, `f174` and `f166` (`diamBoundedBy_f38`, `diamBoundedBy_f46`,
`diamBoundedBy_f66`, `diamBoundedBy_f174`, `diamBoundedBy_f166`). -/
theorem growingWidth_lightCone_middle_twelve (n : ℕ) :
    (∀ N : ℕ, ∃ t, (N : ℕ∞) < growingWidth (tableRule f106 hq106) diam (lightCone n) t) ∧
    (∀ N : ℕ, ∃ t, (N : ℕ∞) <
      growingWidth (tableRule (mirrorTable f106) hq106) diam (lightCone n) t) ∧
    (∀ t, growingWidth (tableRule f38 hq38) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule (mirrorTable f38) hq38) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule f46 hq46) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule (mirrorTable f46) hq46) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule f66 hq66) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule (mirrorTable f66) hq66) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule f174 hq174) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule (mirrorTable f174) hq174) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule f166 hq166) diam (lightCone n) t = 0) ∧
    (∀ t, growingWidth (tableRule (mirrorTable f166) hq166) diam (lightCone n) t = 0) :=
  ⟨growingWidth_lightCone_unbounded_f106 n,
    growingWidth_lightCone_unbounded_mirror_f106 n,
    fun t => growingWidth_lightCone_eq_zero_f38 n t,
    fun t => growingWidth_lightCone_eq_zero_mirror_f38 n t,
    fun t => growingWidth_lightCone_eq_zero_f46 n t,
    fun t => growingWidth_lightCone_eq_zero_mirror_f46 n t,
    fun t => growingWidth_lightCone_eq_zero_f66 n t,
    fun t => growingWidth_lightCone_eq_zero_mirror_f66 n t,
    fun t => growingWidth_lightCone_eq_zero_f174 n t,
    fun t => growingWidth_lightCone_eq_zero_mirror_f174 n t,
    fun t => growingWidth_lightCone_eq_zero_f166 n t,
    fun t => growingWidth_lightCone_eq_zero_mirror_f166 n t⟩

/-! ## Instances at landed tables -/

/-- The single cell lies in the growing part at `f90`: every nonzero state does. -/
theorem single_mem_growingPart_f90 :
    Finsupp.single (0 : ℤ) (1 : ZMod 2) ∈ GrowingPart (tableRule f90 (by decide)) diam := by
  have h1 : f90 0 0 1 = 1 := by decide
  have h2 : f90 1 0 0 = 1 := by decide
  have hpart := growingPart_eq_ne_zero (U := tableRule f90 (by decide))
    (fun {s} => ⟨fun h => by
        by_contra hs
        exact tableRule_ne_zero_of_leftTap (f := f90) (hq := by decide) h1 hs h,
      fun h => by subst h; exact tableRule_zero' f90 (by decide)⟩)
    (fun {s} hne hne' => tableRule_min'_of_leftTap (f := f90) (hq := by decide) h1 hne hne')
    (fun {s} hne hne' => tableRule_max'_of_rightTap (f := f90) (hq := by decide) h2 hne hne')
  rw [hpart]
  exact Finsupp.single_ne_zero.mpr one_ne_zero

/-- **The one-state lower bound at `f90`, from the single cell**: at least `n + 2 t + 1 - 1`. -/
theorem linear_le_growingWidth_lightCone_f90_single (n t : ℕ) :
    ((n + 2 * t + 1 - diam (Finsupp.single (0 : ℤ) (1 : ZMod 2)) : ℕ) : ℕ∞) ≤
      growingWidth (tableRule f90 (by decide)) diam (lightCone n) t :=
  linear_le_growingWidth_lightCone_of_mem_growingPart single_mem_growingPart_f90 n t

/-- **The diameter never grows at the shift `f170`**: `f170` is a landed zero table. -/
theorem diamBoundedBy_f170 : DiamBoundedBy (tableRule f170 hq170) 0 := by
  intro s k
  have hmono : ∀ k : ℕ, diam ((tableRule f170 hq170)^[k] s) ≤ diam s := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (diam_tableRule_le_of_leftTap_rightDies (f := f170) (hq := hq170)
        (by decide) (by decide) (by decide) (by decide) _).trans ih
  simpa using hmono k

/-- **The mirror of the shift `f170`**, by `diamBoundedBy_mirrorTable`. -/
theorem diamBoundedBy_mirrorTable_f170 : DiamBoundedBy (tableRule (mirrorTable f170) hq170) 0 :=
  diamBoundedBy_mirrorTable diamBoundedBy_f170

/-- **The zero side at `f170`**, from `growingWidth_lightCone_eq_zero_of_diamBoundedBy`. -/
theorem growingWidth_lightCone_eq_zero_f170 (n t : ℕ) :
    growingWidth (tableRule f170 hq170) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diamBoundedBy diamBoundedBy_f170 n t


/-! ## The traffic class: the diameter at most doubles -/

/-- The number of set cells at or beyond `q`. -/
private def cellsFrom (x : ℤ →₀ ZMod 2) (q : ℤ) : ℕ :=
  (x.support.filter (fun i => q ≤ i)).card

private theorem zmod2_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

private theorem cellsFrom_pred {x : ℤ →₀ ZMod 2} {r : ℤ} (h : x (r - 1) = 1) :
    cellsFrom x (r - 1) = cellsFrom x r + 1 := by
  unfold cellsFrom
  have hmem : (r - 1) ∈ x.support := Finsupp.mem_support_iff.mpr (by rw [h]; exact one_ne_zero)
  have hset : x.support.filter (fun i => r - 1 ≤ i) =
      insert (r - 1) (x.support.filter (fun i => r ≤ i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hi, hle⟩
      by_cases hr : r ≤ i
      · exact Or.inr ⟨hi, hr⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨hi, hle⟩)
      · exact ⟨hmem, le_refl _⟩
      · exact ⟨hi, by omega⟩
  rw [hset, Finset.card_insert_of_notMem]
  simp

/-- **One step of the traffic rule**: the cells at or beyond `q - 1` after a step number at most
the cells at or beyond `q` before it, plus one when the cells `q - 1` and `q - 2` are both set. -/
private theorem cellsFrom_step_le {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1))
    (x : ℤ →₀ ZMod 2) (q : ℤ) :
    cellsFrom (tableRule f hq x) (q - 1) ≤
      cellsFrom x q + (if x (q - 1) = 1 ∧ x (q - 2) = 1 then 1 else 0) := by
  classical
  have key : ∀ i, i ∈ (tableRule f hq x).support →
      (x i = 0 ∧ x (i + 1) = 1) ∨ (x (i - 1) = 1 ∧ x i = 1) := by
    intro i hi
    rw [Finsupp.mem_support_iff, tableRule_apply] at hi
    have h1 := hf _ _ _ (zmod2_one_of_ne_zero _ hi)
    rcases h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact Or.inl ⟨h2, h3⟩
    · exact Or.inr ⟨h2, h3⟩
  have hmemx : ∀ j, x j = 1 → j ∈ x.support := fun j h =>
    Finsupp.mem_support_iff.mpr (by rw [h]; exact one_ne_zero)
  let g : ℤ → ℤ := fun i => if x i = 1 then i else i + 1
  let T : Finset ℤ := x.support.filter (fun i => q ≤ i) ∪
    (if x (q - 1) = 1 ∧ x (q - 2) = 1 then {q - 1} else ∅)
  have hcard : cellsFrom (tableRule f hq x) (q - 1) ≤ T.card := by
    unfold cellsFrom
    apply Finset.card_le_card_of_injOn g
    · intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      have hk := key i hi1
      simp only [T, Finset.mem_coe, Finset.mem_union, Finset.mem_filter]
      by_cases hxi : x i = 1
      · have hgi : g i = i := by simp [g, hxi]
        rw [hgi]
        by_cases hiq : q ≤ i
        · exact Or.inl ⟨hmemx i hxi, hiq⟩
        · have hi' : i = q - 1 := by omega
          subst hi'
          rcases hk with ⟨h0, _⟩ | ⟨h0, _⟩
          · rw [hxi] at h0; exact absurd h0 (by decide)
          · right
            have hcond : x (q - 1) = 1 ∧ x (q - 2) = 1 :=
              ⟨hxi, by rw [show q - 2 = q - 1 - 1 by ring]; exact h0⟩
            simp [hcond]
      · have hgi : g i = i + 1 := by simp [g, hxi]
        rw [hgi]
        rcases hk with ⟨h0, h1⟩ | ⟨_, h1⟩
        · exact Or.inl ⟨hmemx _ h1, by omega⟩
        · exact absurd h1 hxi
    · intro i hi j hj hij
      replace hi := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      replace hj := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
      have ki := key i hi.1
      have kj := key j hj.1
      by_cases hxi : x i = 1 <;> by_cases hxj : x j = 1
      · simpa [g, hxi, hxj] using hij
      · have hgi : g i = i := by simp [g, hxi]
        have hgj : g j = j + 1 := by simp [g, hxj]
        have hji : i = j + 1 := by simp only [hgi, hgj] at hij; exact hij
        rcases ki with ⟨h0, _⟩ | ⟨h0, _⟩
        · rw [hxi] at h0; exact absurd h0 (by decide)
        · rw [hji, show j + 1 - 1 = j by ring] at h0
          exact absurd h0 hxj
      · have hgi : g i = i + 1 := by simp [g, hxi]
        have hgj : g j = j := by simp [g, hxj]
        have hji : i + 1 = j := by simp only [hgi, hgj] at hij; exact hij
        rcases kj with ⟨h0, _⟩ | ⟨h0, _⟩
        · rw [hxj] at h0; exact absurd h0 (by decide)
        · rw [← hji, show i + 1 - 1 = i by ring] at h0
          exact absurd h0 hxi
      · simpa [g, hxi, hxj] using hij
  refine hcard.trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  unfold cellsFrom
  split_ifs <;> simp

/-- **The count invariant**: along every orbit, the cells at or beyond `q - k` after `k` steps
number at most half of `K + 1 - q`, where `K` is the left end plus twice the diameter. -/
private theorem cellsFrom_iterate_le {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1))
    {s : ℤ →₀ ZMod 2} {m₀ M : ℤ} (hm : m₀ ≤ M)
    (hlo : ∀ x ∈ s.support, m₀ ≤ x) (hhi : ∀ x ∈ s.support, x ≤ M) :
    ∀ k : ℕ, ∀ q : ℤ, 2 * cellsFrom ((tableRule f hq)^[k] s) (q - k) ≤
      (m₀ + 2 * (M - m₀ + 1) + 1 - q).toNat
  | 0 => by
    intro q
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero]
    have hsub : s.support.filter (fun i => q ≤ i) ⊆ Finset.Icc (max q m₀) M := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_Icc]
      exact ⟨max_le hi.2 (hlo i hi.1), hhi i hi.1⟩
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    unfold cellsFrom
    omega
  | k + 1 => by
    intro q
    have hq1 : q - ((k + 1 : ℕ) : ℤ) = (q - k) - 1 := by push_cast; ring
    have ih := cellsFrom_iterate_le (hq := hq) hf hm hlo hhi k q
    have ih2 := cellsFrom_iterate_le (hq := hq) hf hm hlo hhi k (q - 2)
    rw [hq1, Function.iterate_succ_apply']
    generalize (tableRule f hq)^[k] s = x at ih ih2 ⊢
    have hstep := cellsFrom_step_le (hq := hq) hf x (q - k)
    by_cases hc : x (q - k - 1) = 1 ∧ x (q - k - 2) = 1
    · simp only [hc.1, hc.2, and_self, ite_true] at hstep
      have e1 := cellsFrom_pred (x := x) (r := q - k) hc.1
      have e2 := cellsFrom_pred (x := x) (r := q - k - 1)
        (by rw [show q - (k : ℤ) - 1 - 1 = q - k - 2 by ring]; exact hc.2)
      rw [show q - 2 - (k : ℤ) = q - k - 1 - 1 by ring, e2, e1] at ih2
      omega
    · simp only [hc, ite_false] at hstep
      omega

/-- **The traffic class at most doubles the diameter**: if every set cell of a step's output has
either a clear cell and a set cell to its right in the input, or a set cell to its left and itself
set, the diameter of every orbit is at most twice its start's. -/
theorem diam_iterate_le_two_mul_of_traffic
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1))
    (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule f hq)^[k] s) ≤ 2 * diam s := by
  by_cases hs : s = 0
  · subst hs
    rw [Function.iterate_fixed (tableRule_zero' f hq), diam_zero']
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hmm := Finset.min'_le_max' s.support hne
    have hlo : ∀ x ∈ s.support, s.support.min' hne ≤ x := fun x hx => Finset.min'_le _ _ hx
    have hhi : ∀ x ∈ s.support, x ≤ s.support.max' hne := fun x hx => Finset.le_max' _ _ hx
    have hinv := cellsFrom_iterate_le (hq := hq) hf hmm hlo hhi k
      (s.support.min' hne + 2 * (s.support.max' hne - s.support.min' hne + 1))
    have hzero : cellsFrom ((tableRule f hq)^[k] s)
        (s.support.min' hne + 2 * (s.support.max' hne - s.support.min' hne + 1) - k) = 0 := by
      omega
    unfold cellsFrom at hzero
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
    have hL := iterate_left_zero (f := f) (hq := hq) (m := s.support.min' hne)
      (fun i hi => below_min'_eq_zero hne hi) k
    refine (diam_le_of_support_subset (m := s.support.min' hne - k)
      (M := s.support.min' hne + 2 * (s.support.max' hne - s.support.min' hne + 1) - k - 1)
      ?_ (by omega)).trans ?_
    · intro x hx
      constructor
      · by_contra hlt
        exact (Finsupp.mem_support_iff.mp hx) (hL x (by omega))
      · by_contra hlt
        exact hzero hx (by omega)
    · rw [diam_eq' hne]
      omega

/-- **The traffic bound passes to the mirror table**, by reflection. -/
theorem diam_iterate_le_two_mul_of_traffic_mirror
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1))
    (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule (mirrorTable f) hq)^[k] s) ≤ 2 * diam s := by
  have h1 := diam_iterate_le_two_mul_of_traffic (hq := hq) hf (reflect s) k
  rw [diam_reflect] at h1
  have e : (tableRule (mirrorTable f) hq)^[k] s =
      reflect ((tableRule f hq)^[k] (reflect s)) := by
    conv_lhs => rw [← reflect_reflect s]
    exact iterate_mirror_reflect f hq (reflect s) k
  rw [e, diam_reflect]
  exact h1

/-- **A doubled diameter bound forces a zero growing width**: no state has an orbit of unbounded
diameter, so the growing part is empty. -/
theorem growingWidth_lightCone_eq_zero_of_diam_le_two_mul
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} (h : ∀ (s : ℤ →₀ ZMod 2) (k : ℕ),
      diam (U^[k] s) ≤ 2 * diam s) (n t : ℕ) :
    growingWidth U diam (lightCone n) t = 0 := by
  apply growingWidth_eq_zero_of_growingPart_eq_empty
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨k, hk⟩ := hs (2 * diam s)
  have := h s k
  omega

/-- **Identically zero growing width in the traffic class**
([RuleSpace] §3 Proposition 3.6): the diameter along every orbit is at most twice its start's
(`diam_iterate_le_two_mul_of_traffic`). -/
theorem growingWidth_lightCone_eq_zero_of_traffic
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1)) (n t : ℕ) :
    growingWidth (tableRule f hq) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_two_mul
    (fun s k => diam_iterate_le_two_mul_of_traffic hf s k) n t

/-- **Identically zero growing width at the mirror of a traffic-class table**
([RuleSpace] §3 Proposition 3.6): the doubled bound passes to the mirror by reflection
(`diam_iterate_le_two_mul_of_traffic_mirror`). -/
theorem growingWidth_lightCone_eq_zero_mirror_of_traffic
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1)) (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f) hq) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_two_mul
    (fun s k => diam_iterate_le_two_mul_of_traffic_mirror hf s k) n t

/-! ## The three tables, and the guards -/

/-- **Table `226`**, `f a b c = if b = 1 then a else c`: the traffic rule `184` mirrored. The
Wolfram number `226` sets the bits `4 a + 2 b + c` listed in `f226_values`. -/
def f226 (a b c : ZMod 2) : ZMod 2 := if b = 1 then a else c

/-- Quiescence of `f226`. -/
theorem hq226 : f226 0 0 0 = 0 := by decide

/-- The eight values of `f226` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `226`. -/
theorem f226_values :
    f226 0 0 0 = 0 ∧ f226 0 0 1 = 1 ∧ f226 0 1 0 = 0 ∧
      f226 0 1 1 = 0 ∧ f226 1 0 0 = 0 ∧ f226 1 0 1 = 1 ∧
      f226 1 1 0 = 1 ∧ f226 1 1 1 = 1 := by decide

/-- `f226` meets the traffic-class hypothesis. -/
theorem f226_traffic : ∀ a b c, f226 a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1) := by decide

/-- **Table `194`**, `f a b c = if b = 1 then a else c * (1 + a)`.
The Wolfram number `194` sets the bits `4 a + 2 b + c` listed in `f194_values`. -/
def f194 (a b c : ZMod 2) : ZMod 2 := if b = 1 then a else c * (1 + a)

/-- Quiescence of `f194`. -/
theorem hq194 : f194 0 0 0 = 0 := by decide

/-- The eight values of `f194` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `194`. -/
theorem f194_values :
    f194 0 0 0 = 0 ∧ f194 0 0 1 = 1 ∧ f194 0 1 0 = 0 ∧
      f194 0 1 1 = 0 ∧ f194 1 0 0 = 0 ∧ f194 1 0 1 = 0 ∧
      f194 1 1 0 = 1 ∧ f194 1 1 1 = 1 := by decide

/-- `f194` meets the traffic-class hypothesis. -/
theorem f194_traffic : ∀ a b c, f194 a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1) := by decide

/-- **Table `98`**, `f a b c = if b = 1 then a * (1 + c) else c`.
The Wolfram number `98` sets the bits `4 a + 2 b + c` listed in `f98_values`. -/
def f98 (a b c : ZMod 2) : ZMod 2 := if b = 1 then a * (1 + c) else c

/-- Quiescence of `f98`. -/
theorem hq98 : f98 0 0 0 = 0 := by decide

/-- The eight values of `f98` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `98`. -/
theorem f98_values :
    f98 0 0 0 = 0 ∧ f98 0 0 1 = 1 ∧ f98 0 1 0 = 0 ∧
      f98 0 1 1 = 0 ∧ f98 1 0 0 = 0 ∧ f98 1 0 1 = 1 ∧
      f98 1 1 0 = 1 ∧ f98 1 1 1 = 0 := by decide

/-- `f98` meets the traffic-class hypothesis. -/
theorem f98_traffic : ∀ a b c, f98 a b c = 1 → (b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1) := by decide

set_option maxRecDepth 8000 in
/-- **None of the six traffic tables is in either endpoint class**: `f226`, `f194`, `f98` and
their mirrors lie in neither `AccretesByEndpoints` nor `ZeroByEndpoints`. -/
theorem not_mem_endpoint_classes_traffic_six :
    ∀ f ∈ ([f226, f194, f98, mirrorTable f226, mirrorTable f194, mirrorTable f98] :
        List (ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)),
      ¬ AccretesByEndpoints f ∧ ¬ ZeroByEndpoints f := by
  decide

/-- **Identically zero growing width at `f226`** ([RuleSpace] §3 Proposition 3.6). -/
theorem growingWidth_lightCone_eq_zero_f226 (n t : ℕ) :
    growingWidth (tableRule f226 hq226) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_traffic f226_traffic n t

/-- **Identically zero growing width at `mirrorTable f226`**
([RuleSpace] §3 Proposition 3.6). -/
theorem growingWidth_lightCone_eq_zero_mirror_f226 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f226) hq226) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_mirror_of_traffic f226_traffic n t

/-- **Identically zero growing width at `f194`** ([RuleSpace] §3 Proposition 3.6). -/
theorem growingWidth_lightCone_eq_zero_f194 (n t : ℕ) :
    growingWidth (tableRule f194 hq194) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_traffic f194_traffic n t

/-- **Identically zero growing width at `mirrorTable f194`**
([RuleSpace] §3 Proposition 3.6). -/
theorem growingWidth_lightCone_eq_zero_mirror_f194 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f194) hq194) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_mirror_of_traffic f194_traffic n t

/-- **Identically zero growing width at `f98`** ([RuleSpace] §3 Proposition 3.6). -/
theorem growingWidth_lightCone_eq_zero_f98 (n t : ℕ) :
    growingWidth (tableRule f98 hq98) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_traffic f98_traffic n t

/-- **Identically zero growing width at `mirrorTable f98`**
([RuleSpace] §3 Proposition 3.6). -/
theorem growingWidth_lightCone_eq_zero_mirror_f98 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f98) hq98) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_mirror_of_traffic f98_traffic n t

/-- **The six traffic tables** ([RuleSpace] §3 Proposition 3.6). For every window width `n` and
every stage `t`, the growing width along the light cone is zero at `f226`, `f194`, `f98` and at
their three mirrors. -/
theorem growingWidth_lightCone_traffic_six (n t : ℕ) :
    growingWidth (tableRule f226 hq226) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f226) hq226) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule f194 hq194) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f194) hq194) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule f98 hq98) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f98) hq98) diam (lightCone n) t = 0 :=
  ⟨growingWidth_lightCone_eq_zero_f226 n t, growingWidth_lightCone_eq_zero_mirror_f226 n t,
    growingWidth_lightCone_eq_zero_f194 n t, growingWidth_lightCone_eq_zero_mirror_f194 n t,
    growingWidth_lightCone_eq_zero_f98 n t, growingWidth_lightCone_eq_zero_mirror_f98 n t⟩

/-- **The traffic-class hypothesis is load-bearing**: `f106` fails it at the arguments `0 1 1`,
and its growing part under the diameter is not empty, since the two-cell state has an orbit of
unbounded diameter (`seedOneOne_mem_growingPart_f106`). -/
theorem traffic_hypothesis_load_bearing :
    (f106 0 1 1 = 1 ∧ ¬ (((1 : ZMod 2) = 0 ∧ (1 : ZMod 2) = 1) ∨
      ((0 : ZMod 2) = 1 ∧ (1 : ZMod 2) = 1))) ∧
    seedOneOne ∈ GrowingPart (tableRule f106 hq106) diam ∧
    GrowingPart (tableRule f106 hq106) diam ≠ ∅ :=
  ⟨⟨by decide, by decide⟩, seedOneOne_mem_growingPart_f106,
    Set.nonempty_iff_ne_empty.mp ⟨_, seedOneOne_mem_growingPart_f106⟩⟩

private theorem diam_eq_of_cells (s : ℤ →₀ ZMod 2) {a b : ℤ} (hab : a ≤ b) (ha : s a ≠ 0)
    (hb : s b ≠ 0) (h : ∀ x, x < a ∨ b < x → s x = 0) : diam s = (b - a).toNat + 1 := by
  have hne : s.support.Nonempty := ⟨a, Finsupp.mem_support_iff.mpr ha⟩
  have h1 := Finset.min'_le s.support a (Finsupp.mem_support_iff.mpr ha)
  have h2 := Finset.le_max' s.support b (Finsupp.mem_support_iff.mpr hb)
  have h3 : a ≤ s.support.min' hne := by
    by_contra hc
    exact (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne)) (h _ (Or.inl (by omega)))
  have h4 : s.support.max' hne ≤ b := by
    by_contra hc
    exact (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne)) (h _ (Or.inr (by omega)))
  rw [diam_eq' hne]
  omega

/-- **The factor two is nearly attained at `f226`**: the two-cell state `seedOneOne` has diameter
`2`, and one step of `f226` gives diameter `3`, against the bound `4` of
`diam_iterate_le_two_mul_of_traffic`. -/
theorem diam_seedOneOne_and_step_f226 :
    diam seedOneOne = 2 ∧ diam (tableRule f226 hq226 seedOneOne) = 3 := by
  constructor
  · rw [diam_eq_of_cells seedOneOne (a := 0) (b := 1) (by omega)
      (by rw [seedOneOne_apply]; simp) (by rw [seedOneOne_apply]; simp) (fun x hx => by
        simp [seedOneOne_apply, show x ≠ 0 by omega, show x ≠ 1 by omega])]
    rfl
  · have hval : ∀ x : ℤ, tableRule f226 hq226 seedOneOne x = if x = -1 ∨ x = 1 then 1 else 0 := by
      intro x
      rw [tableRule_apply, seedOneOne_apply, seedOneOne_apply, seedOneOne_apply]
      split_ifs <;> first | (exfalso; omega) | decide
    rw [diam_eq_of_cells _ (a := -1) (b := 1) (by omega) (by rw [hval]; simp)
      (by rw [hval]; simp) (fun x hx => by simp [hval, show x ≠ -1 by omega, show x ≠ 1 by omega])]
    rfl

end OneTapWidth

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'OneTapWidth.reflect_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.reflect_reflect

/-- info: 'OneTapWidth.tableRule_mirrorTable_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.tableRule_mirrorTable_reflect

/-- info: 'OneTapWidth.diam_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diam_reflect

/-- info: 'OneTapWidth.linear_le_growingWidth_lightCone_of_mem_growingPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.linear_le_growingWidth_lightCone_of_mem_growingPart

/-- info: 'OneTapWidth.growingWidth_lightCone_unbounded_of_mem_growingPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_unbounded_of_mem_growingPart

/-- info: 'OneTapWidth.growingWidth_lightCone_zero_or_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_zero_or_unbounded

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_of_diamBoundedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_of_diamBoundedBy

/-- info: 'OneTapWidth.diamBoundedBy_mirrorTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_mirrorTable

/-- info: 'OneTapWidth.reflect_mem_growingPart_mirrorTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.reflect_mem_growingPart_mirrorTable

/-- info: 'OneTapWidth.hq106' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq106

/-- info: 'OneTapWidth.f106_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f106_values

/-- info: 'OneTapWidth.hq166' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq166

/-- info: 'OneTapWidth.f166_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f166_values

/-- info: 'OneTapWidth.hq38' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq38

/-- info: 'OneTapWidth.f38_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f38_values

/-- info: 'OneTapWidth.hq46' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq46

/-- info: 'OneTapWidth.f46_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f46_values

/-- info: 'OneTapWidth.hq66' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq66

/-- info: 'OneTapWidth.f66_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f66_values

/-- info: 'OneTapWidth.hq174' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq174

/-- info: 'OneTapWidth.f174_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f174_values

/-- info: 'OneTapWidth.not_mem_endpoint_classes_middle_twelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.not_mem_endpoint_classes_middle_twelve

/-- info: 'OneTapWidth.growingWidth_lightCone_unbounded_f106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_unbounded_f106

/-- info: 'OneTapWidth.growingWidth_lightCone_unbounded_mirror_f106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_unbounded_mirror_f106

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f38

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f38

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f46' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f46

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f46' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f46

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f66' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f66

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f66' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f66

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f174' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f174

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f174' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f174

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f166' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f166

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f166' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f166

/-- info: 'OneTapWidth.diamBoundedBy_two_of_endClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_two_of_endClosure

/-- info: 'OneTapWidth.diamBoundedBy_f38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_f38

/-- info: 'OneTapWidth.diamBoundedBy_f46' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_f46

/-- info: 'OneTapWidth.diamBoundedBy_f66' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_f66

/-- info: 'OneTapWidth.diamBoundedBy_f174' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_f174

/-- info: 'OneTapWidth.diamBoundedBy_f166' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_f166

/-- info: 'OneTapWidth.diam_iterate_one_single_f166' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diam_iterate_one_single_f166

/-- info: 'OneTapWidth.diamBoundedBy_two_of_endClosure_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_two_of_endClosure_nonvacuous

/-- info: 'OneTapWidth.diam_iterate_one_single_f38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diam_iterate_one_single_f38

/-- info: 'OneTapWidth.growingWidth_lightCone_middle_twelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_middle_twelve

/-- info: 'OneTapWidth.single_mem_growingPart_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.single_mem_growingPart_f90

/-- info: 'OneTapWidth.linear_le_growingWidth_lightCone_f90_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.linear_le_growingWidth_lightCone_f90_single

/-- info: 'OneTapWidth.diamBoundedBy_f170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_f170

/-- info: 'OneTapWidth.diamBoundedBy_mirrorTable_f170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diamBoundedBy_mirrorTable_f170

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f170

/-- info: 'OneTapWidth.mem_growingPart_of_injective_of_notMem_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.mem_growingPart_of_injective_of_notMem_range

/-- info: 'OneTapWidth.tableRule_f106_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.tableRule_f106_injective

/-- info: 'OneTapWidth.seedOneOne_notMem_range_f106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.seedOneOne_notMem_range_f106

/-- info: 'OneTapWidth.seedOneOne_mem_growingPart_f106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.seedOneOne_mem_growingPart_f106

/-- info: 'OneTapWidth.mem_growingPart_of_injective_of_notMem_range_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.mem_growingPart_of_injective_of_notMem_range_nonvacuous

/-- info: 'OneTapWidth.diam_iterate_le_two_mul_of_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diam_iterate_le_two_mul_of_traffic

/-- info: 'OneTapWidth.diam_iterate_le_two_mul_of_traffic_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diam_iterate_le_two_mul_of_traffic_mirror

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_of_diam_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_of_diam_le_two_mul

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_of_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_of_traffic

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_of_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_of_traffic

/-- info: 'OneTapWidth.hq226' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq226

/-- info: 'OneTapWidth.f226_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f226_values

/-- info: 'OneTapWidth.f226_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f226_traffic

/-- info: 'OneTapWidth.hq194' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq194

/-- info: 'OneTapWidth.f194_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f194_values

/-- info: 'OneTapWidth.f194_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f194_traffic

/-- info: 'OneTapWidth.hq98' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.hq98

/-- info: 'OneTapWidth.f98_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f98_values

/-- info: 'OneTapWidth.f98_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.f98_traffic

/-- info: 'OneTapWidth.not_mem_endpoint_classes_traffic_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.not_mem_endpoint_classes_traffic_six

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f226' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f226

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f226' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f226

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f194' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f194

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f194' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f194

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_f98' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_f98

/-- info: 'OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f98' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_eq_zero_mirror_f98

/-- info: 'OneTapWidth.growingWidth_lightCone_traffic_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.growingWidth_lightCone_traffic_six

/-- info: 'OneTapWidth.traffic_hypothesis_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.traffic_hypothesis_load_bearing

/-- info: 'OneTapWidth.diam_seedOneOne_and_step_f226' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneTapWidth.diam_seedOneOne_and_step_f226
