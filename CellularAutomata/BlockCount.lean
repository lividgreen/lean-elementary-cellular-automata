/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Batteries.Tactic.OpenPrivate
public import CellularAutomata.Accretion
import all CellularAutomata.Accretion
import all CellularAutomata.EndpointClasses
-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing width at the left-clear tables: a count of block starts bounds every diameter
([RuleSpace] §3 Proposition 3.7)

`Accretion.lean` decides the six traffic tables by a count of set cells. This file decides four
more of the `28` tables between the endpoint classes, `6`, `14` and their mirrors, by the same
method run on a count of block starts, the set cells whose left neighbour is clear.

* **The class.** A table is *left-clear* when a cell is set after a step only where its left
  neighbour was clear and it or its right neighbour was set, and a clear cell with a clear left
  neighbour and a set right neighbour becomes set. The members among the quiescent radius-one
  tables are the numbers `2`, `6`, `10` and `14`.
* **The class theorem.** At a left-clear table every orbit's diameter is at most five times its
  start's plus five (`diam_iterate_le_of_leftClear`), by one count: no image has three set cells in
  a row, a start of an image is a start of the state or the cell before one, and the starts
  at or beyond a cell `q` of the next image number at most the starts at or beyond `q + 1` of the
  state, plus one when the cells `q`, `q - 1`, `q - 2` carry the pattern set, clear, set.
  With no three in a row that pattern costs two further starts to the left
  of it, which is the step of the abstract count lemma `count_invariant_of_step`.
* **The width.** An affine diameter bound forces a zero growing width along the light cone
  (`growingWidth_lightCone_eq_zero_of_diam_le_affine`); with the class theorem and its mirror this
  decides the growing width at `f14`, `f6` and the mirrors of both.
* **Table `142`.** A count of block ends, the set cells whose right neighbour is clear, bounds
  every orbit's diameter at table `142` and its mirror by five times the start's plus five
  (`diam_iterate_le_f142`), though `142` is outside the left-clear class (`f142_not_leftClear`);
  the step gains one end at a pattern clear, set, clear, and that costs two further ends to the
  left only where every isolated set cell has a set cell two or three places to its left, which
  every image has (`endsFrom_pattern_gain_one` is the state where the gain is one).
* **Table `134`.** The step is table `6`'s except at three set cells in a row, and runs shorten by
  two under a step (a run of three or more set cells in an image sits inside a run two cells longer
  of the state), so after as many steps as the start's diameter no image has three in a row and the
  orbit continues as an orbit of `6`: every diameter is at most ten times the start's plus five
  (`diam_iterate_le_f134`), though `134` is outside the left-clear class (`f134_not_leftClear`) and
  the agreement with `f6` needs its hypothesis (`tableRule_f134_ne_f6_block`).
* **Table `74`.** A count of long starts, the set cells with a clear left neighbour and a set right
  neighbour, bounds every orbit's diameter at table `74` and its mirror by eight times the start's
  plus nineteen (`diam_iterate_le_f74`), though `74` is outside the left-clear class
  (`f74_not_leftClear`). No image has four set cells in a row; one step gains a long start only at
  the pattern set, clear, set, set, clear, and from the third image on that pattern costs two
  further long starts within seven cells to its left, a fact about fourteen cells of the state
  decided by the kernel; two steps do not give it (`three_steps_needed_f74`).
* **The ten middle tables.** `growingWidth_lightCone_middle_ten` states the zero growing width at
  `f6`, `f14`, `f74`, `f134`, `f142` and their five mirrors in one statement, and
  `not_mem_endpoint_classes_middle_ten` that none of the ten is in either endpoint class.
* **Guards.** The tap hypothesis alone does not suffice (`leftClear_hypothesis_load_bearing`: at
  `f106` the tap holds, the shape hypothesis fails, and the two-cell state has an orbit of unbounded
  diameter), and the diameter does grow in the class, by more than two
  (`diam_iterate_five_alternating_f14`).

## Main results

* `count_invariant_of_step` — an abstract count lemma: a count that falls by the step
  `N (j + 1) (q - 1) ≤ N j q + 1`, with the extra unit paid for by two further counts at a distance
  `D`, is bounded linearly along every orbit.
* `diam_iterate_le_of_leftClear` / `diam_iterate_le_of_leftClear_mirror` /
  `growingWidth_lightCone_eq_zero_of_diam_le_affine` /
  `growingWidth_lightCone_eq_zero_of_leftClear` /
  `growingWidth_lightCone_eq_zero_mirror_of_leftClear` — the class and its mirror.
* `f14`, `f6`, the value lists, the four width statements, `not_mem_endpoint_classes_leftClear_four`
  and `growingWidth_lightCone_leftClear_four` — the four tables.
* `diam_iterate_le_of_leftClear_nonvacuous`, `leftClear_hypothesis_load_bearing`,
  `diam_iterate_five_alternating_f14` — the hypotheses hold together, the shape hypothesis is
  load-bearing, and the diameter grows.
* `f74`, `diam_iterate_le_f74`, `diam_iterate_le_mirror_f74` and the width statements at `f74` and
  its mirror — table `74`.
* `growingWidth_lightCone_middle_ten` and `not_mem_endpoint_classes_middle_ten` — the ten middle
  tables.

## Scope

Four tables are decided by the block-start count, `142` by the block-end count, `134` by the
shortening of runs and the class bound at `6`, and `74` by the long-start count.
The constants are not sharp: the true growth at the tables observed is far below the bound.
-/

open private iterate_left_zero zmod2_one_of_ne_zero seedOneOne_apply iterate_mirror_reflect
  diam_eq_of_cells from CellularAutomata.Accretion
open private below_min'_eq_zero above_max'_eq_zero diam_zero' diam_eq' diam_le_of_support_subset
  tableRule_zero' from CellularAutomata.EndpointClasses

@[expose] public section

namespace BlockTrainWidth

open GrowingWidth MemoryWidth GrowingCore GrowingWorld ExtremeTapWidth LightConeWidth OneTapWidth

/-! ## An abstract count lemma -/

/-- **A count with a paid-for extra unit is bounded linearly along every orbit.** Let `N j q` be a
count at stage `j` and position `q`, and `P j q` a condition. If one step lowers the position by
one and raises the count by at most one (`hstep`), by nothing unless `P j q` holds (`hhold`),
`P j q` forces two further counts to the left at distance `D` (`hP`), and the base satisfies
`D * N 0 q ≤ (K - q).toNat`, then `D * N j (q - j) ≤ (K - q).toNat` at every stage `j`. -/
theorem count_invariant_of_step {N : ℕ → ℤ → ℕ} {P : ℕ → ℤ → Prop} (D : ℕ) (K : ℤ)
    (hstep : ∀ j q, N (j + 1) (q - 1) ≤ N j q + 1)
    (hhold : ∀ j q, ¬ P j q → N (j + 1) (q - 1) ≤ N j q)
    (hP : ∀ j q, P j q → N j q + 2 ≤ N j (q - D))
    (hbase : ∀ q, D * N 0 q ≤ (K - q).toNat) :
    ∀ j : ℕ, ∀ q : ℤ, D * N j (q - j) ≤ (K - q).toNat := by
  intro j
  induction j with
  | zero => intro q; simpa using hbase q
  | succ j ih =>
    intro q
    have e : q - ((j + 1 : ℕ) : ℤ) = (q - j) - 1 := by push_cast; ring
    rw [e]
    by_cases hc : P j (q - j)
    · have h1 : D * N (j + 1) (q - j - 1) ≤ D * (N j (q - j) + 1) :=
        Nat.mul_le_mul_left D (hstep j (q - j))
      have h2 : D * (N j (q - j) + 2) ≤ D * N j (q - j - D) :=
        Nat.mul_le_mul_left D (hP j _ hc)
      have ih2 := ih (q - D)
      rw [show q - (D : ℤ) - j = q - j - D by ring] at ih2
      rw [Nat.mul_add] at h1 h2
      omega
    · have h1 : D * N (j + 1) (q - j - 1) ≤ D * N j (q - j) :=
        Nat.mul_le_mul_left D (hhold j _ hc)
      have := ih q
      omega

/-! ## Block starts -/

/-- The number of block starts at or beyond `q`: set cells whose left neighbour is clear. -/
private def startsFrom (x : ℤ →₀ ZMod 2) (q : ℤ) : ℕ :=
  (x.support.filter (fun i => q ≤ i ∧ x (i - 1) = 0)).card

private theorem zmod2_eq_zero_of_ne_one : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide

/-- The states with no three set cells in a row. -/
private def NoThree (x : ℤ →₀ ZMod 2) : Prop :=
  ∀ i, ¬ (x i = 1 ∧ x (i + 1) = 1 ∧ x (i + 2) = 1)

private theorem mem_support_of_eq_one {x : ℤ →₀ ZMod 2} {j : ℤ} (h : x j = 1) : j ∈ x.support :=
  Finsupp.mem_support_iff.mpr (by rw [h]; exact one_ne_zero)

/-- No image has three set cells in a row. -/
private theorem noThree_tableRule {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) (x : ℤ →₀ ZMod 2) :
    NoThree (tableRule f hq x) := by
  intro i ⟨h0, h1, h2⟩
  rw [tableRule_apply] at h0 h1 h2
  obtain ⟨_, b0⟩ := hf _ _ _ h0
  obtain ⟨a1, _⟩ := hf _ _ _ h1
  obtain ⟨a2, _⟩ := hf _ _ _ h2
  rw [show i + 1 - 1 = i by ring] at a1
  rw [show i + 2 - 1 = i + 1 by ring] at a2
  rw [show i + 1 = i + 1 from rfl] at b0
  rcases b0 with h | h
  · rw [a1] at h; exact absurd h (by decide)
  · rw [a2] at h; exact absurd h (by decide)

/-- **One step of the left-clear rule**: the block starts at or beyond `q - 1` after a step number
at most the block starts at or beyond `q` before it, plus one when the cells `q - 1`, `q - 2`,
`q - 3` read set, clear, set. -/
private theorem startsFrom_step_le {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) (htap : f 0 0 1 = 1)
    (x : ℤ →₀ ZMod 2) (q : ℤ) :
    startsFrom (tableRule f hq x) (q - 1) ≤
      startsFrom x q + (if x (q - 1) = 1 ∧ x (q - 2) = 0 ∧ x (q - 3) = 1 then 1 else 0) := by
  classical
  have key : ∀ i, tableRule f hq x i = 1 → x (i - 1) = 0 ∧ (x i = 1 ∨ x (i + 1) = 1) := by
    intro i hi
    rw [tableRule_apply] at hi
    exact hf _ _ _ hi
  have held : ∀ i, tableRule f hq x (i - 1) = 0 → x (i - 1) = 0 → x i = 1 → x (i - 1 - 1) = 1 := by
    intro i h0 h1 h2
    rw [tableRule_apply, h1, show i - 1 + 1 = i by ring, h2] at h0
    by_contra hne
    rw [zmod2_eq_zero_of_ne_one _ hne] at h0
    exact absurd (h0.symm.trans htap) (by decide)
  let g : ℤ → ℤ := fun i => if x i = 1 then i else i + 1
  let T : Finset ℤ := x.support.filter (fun i => q ≤ i ∧ x (i - 1) = 0) ∪
    (if x (q - 1) = 1 ∧ x (q - 2) = 0 ∧ x (q - 3) = 1 then {q - 1} else ∅)
  have hcard : startsFrom (tableRule f hq x) (q - 1) ≤ T.card := by
    unfold startsFrom
    apply Finset.card_le_card_of_injOn g
    · intro i hi
      obtain ⟨hi1, hi2, hi3⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      have hz1 : tableRule f hq x i = 1 := zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi1)
      obtain ⟨k1, k2⟩ := key i hz1
      simp only [T, Finset.mem_coe, Finset.mem_union, Finset.mem_filter]
      by_cases hxi : x i = 1
      · have hgi : g i = i := by simp [g, hxi]
        rw [hgi]
        by_cases hiq : q ≤ i
        · exact Or.inl ⟨mem_support_of_eq_one hxi, hiq, k1⟩
        · have hi' : i = q - 1 := by omega
          subst hi'
          right
          have h3 := held (q - 1) hi3 k1 hxi
          rw [show q - 1 - 1 = q - 2 by ring] at k1 h3
          have h3' : x (q - 3) = 1 := by rw [show q - 3 = q - 2 - 1 by ring]; exact h3
          have hcond : x (q - 1) = 1 ∧ x (q - 2) = 0 ∧ x (q - 3) = 1 := ⟨hxi, k1, h3'⟩
          simp [hcond]
      · have hgi : g i = i + 1 := by simp [g, hxi]
        rw [hgi]
        have hx1 : x (i + 1) = 1 := by
          rcases k2 with h | h
          · exact absurd h hxi
          · exact h
        refine Or.inl ⟨mem_support_of_eq_one hx1, by omega, ?_⟩
        rw [show i + 1 - 1 = i by ring]
        exact zmod2_eq_zero_of_ne_one _ hxi
    · intro i hi j hj hij
      replace hi := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      replace hj := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
      by_cases hxi : x i = 1 <;> by_cases hxj : x j = 1
      · simpa [g, hxi, hxj] using hij
      · have hgi : g i = i := by simp [g, hxi]
        have hgj : g j = j + 1 := by simp [g, hxj]
        have hji : i = j + 1 := by simp only [hgi, hgj] at hij; exact hij
        have h3 := hi.2.2
        rw [hji, show j + 1 - 1 = j by ring] at h3
        exact absurd h3 (Finsupp.mem_support_iff.mp hj.1)
      · have hgi : g i = i + 1 := by simp [g, hxi]
        have hgj : g j = j := by simp [g, hxj]
        have hji : i + 1 = j := by simp only [hgi, hgj] at hij; exact hij
        have h3 := hj.2.2
        rw [← hji, show i + 1 - 1 = i by ring] at h3
        exact absurd h3 (Finsupp.mem_support_iff.mp hi.1)
      · simpa [g, hxi, hxj] using hij
  refine hcard.trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  unfold startsFrom
  split_ifs <;> simp

/-- **The pattern set, clear, set costs two further starts to its left**, where no three cells in a
row are set: the cell `q - 1` is a start, and the run through `q - 3` starts at `q - 3` or
`q - 4`. -/
private theorem startsFrom_pattern_le {x : ℤ →₀ ZMod 2} (hN : NoThree x) (q : ℤ)
    (h1 : x (q - 1) = 1) (h2 : x (q - 2) = 0) (h3 : x (q - 3) = 1) :
    startsFrom x q + 2 ≤ startsFrom x (q - 4) := by
  classical
  obtain ⟨p, hp1, hp2, hp3, hp4, hp5⟩ :
      ∃ p : ℤ, p ≠ q - 1 ∧ p < q ∧ q - 4 ≤ p ∧ x p = 1 ∧ x (p - 1) = 0 := by
    by_cases h4 : x (q - 4) = 0
    · exact ⟨q - 3, by omega, by omega, by omega, h3,
        by rw [show q - 3 - 1 = q - 4 by ring]; exact h4⟩
    · have h4' := zmod2_one_of_ne_zero _ h4
      refine ⟨q - 4, by omega, by omega, le_refl _, h4', ?_⟩
      have := hN (q - 5)
      rw [show q - 5 + 1 = q - 4 by ring, show q - 5 + 2 = q - 3 by ring] at this
      rw [show q - 4 - 1 = q - 5 by ring]
      by_contra hne
      exact this ⟨zmod2_one_of_ne_zero _ hne, h4', h3⟩
  have hsub : insert (q - 1) (insert p (x.support.filter (fun i => q ≤ i ∧ x (i - 1) = 0))) ⊆
      x.support.filter (fun i => q - 4 ≤ i ∧ x (i - 1) = 0) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_filter] at hi ⊢
    rcases hi with rfl | rfl | ⟨hs, hq, hz⟩
    · exact ⟨mem_support_of_eq_one h1, by omega, by rw [show q - 1 - 1 = q - 2 by ring]; exact h2⟩
    · exact ⟨mem_support_of_eq_one hp4, hp3, hp5⟩
    · exact ⟨hs, by omega, hz⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] at hc
  · unfold startsFrom
    omega
  · simp only [Finset.mem_filter]
    omega
  · simp only [Finset.mem_insert, Finset.mem_filter]
    omega

/-- The diameter bound from the two ends of the support: every image from the first on spreads
at most to `5 * (M - m) + 10` cells. -/
private theorem diam_succ_iterate_le {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) (htap : f 0 0 1 = 1)
    {s : ℤ →₀ ZMod 2} {m M : ℤ} (hmM : m ≤ M)
    (hlo : ∀ x ∈ s.support, m ≤ x) (hhi : ∀ x ∈ s.support, x ≤ M) (j : ℕ) :
    diam ((tableRule f hq)^[j + 1] s) ≤ (5 * (M - m) + 9).toNat + 1 := by
  have hN : ∀ j : ℕ, NoThree ((tableRule f hq)^[j] (tableRule f hq s)) := fun j => by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
    exact noThree_tableRule hf _
  have hbase : ∀ q : ℤ, 4 * startsFrom ((tableRule f hq)^[0] (tableRule f hq s)) q ≤
      (5 * M - 4 * m + 11 - q).toNat := by
    intro q
    simp only [Function.iterate_zero, id_eq]
    have hsub : (tableRule f hq s).support.filter (fun i => q ≤ i ∧ tableRule f hq s (i - 1) = 0)
        ⊆ Finset.Icc (max q (m - 1)) M := by
      intro i hi
      obtain ⟨hi1, hi2, _⟩ := Finset.mem_filter.mp hi
      have hz : tableRule f hq s i = 1 := zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi1)
      rw [tableRule_apply] at hz
      obtain ⟨_, hb⟩ := hf _ _ _ hz
      rw [Finset.mem_Icc]
      rcases hb with h | h
      · exact ⟨max_le hi2 (by have := hlo _ (mem_support_of_eq_one h); omega),
          hhi _ (mem_support_of_eq_one h)⟩
      · have := hlo _ (mem_support_of_eq_one h)
        have := hhi _ (mem_support_of_eq_one h)
        exact ⟨max_le hi2 (by omega), by omega⟩
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    unfold startsFrom
    omega
  have hstep : ∀ (j : ℕ) (q : ℤ),
      startsFrom ((tableRule f hq)^[j + 1] (tableRule f hq s)) (q - 1) ≤
        startsFrom ((tableRule f hq)^[j] (tableRule f hq s)) q + 1 := by
    intro j q
    rw [Function.iterate_succ_apply']
    refine (startsFrom_step_le hf htap _ q).trans ?_
    split_ifs <;> omega
  have hhold : ∀ (j : ℕ) (q : ℤ),
      ¬ (((tableRule f hq)^[j] (tableRule f hq s)) (q - 1) = 1 ∧
        ((tableRule f hq)^[j] (tableRule f hq s)) (q - 2) = 0 ∧
        ((tableRule f hq)^[j] (tableRule f hq s)) (q - 3) = 1) →
      startsFrom ((tableRule f hq)^[j + 1] (tableRule f hq s)) (q - 1) ≤
        startsFrom ((tableRule f hq)^[j] (tableRule f hq s)) q := by
    intro j q hc
    rw [Function.iterate_succ_apply']
    refine (startsFrom_step_le hf htap _ q).trans ?_
    simp [hc]
  have hP : ∀ (j : ℕ) (q : ℤ),
      (((tableRule f hq)^[j] (tableRule f hq s)) (q - 1) = 1 ∧
        ((tableRule f hq)^[j] (tableRule f hq s)) (q - 2) = 0 ∧
        ((tableRule f hq)^[j] (tableRule f hq s)) (q - 3) = 1) →
      startsFrom ((tableRule f hq)^[j] (tableRule f hq s)) q + 2 ≤
        startsFrom ((tableRule f hq)^[j] (tableRule f hq s)) (q - ((4 : ℕ) : ℤ)) := by
    intro j q ⟨h1, h2, h3⟩
    exact startsFrom_pattern_le (hN j) q h1 h2 h3
  have inv := count_invariant_of_step (N := fun j q => startsFrom ((tableRule f hq)^[j]
      (tableRule f hq s)) q)
    (P := fun j q => ((tableRule f hq)^[j] (tableRule f hq s)) (q - 1) = 1 ∧
        ((tableRule f hq)^[j] (tableRule f hq s)) (q - 2) = 0 ∧
        ((tableRule f hq)^[j] (tableRule f hq s)) (q - 3) = 1) 4 (5 * M - 4 * m + 11)
    hstep hhold hP hbase j (5 * M - 4 * m + 8)
  have hz0 : startsFrom ((tableRule f hq)^[j] (tableRule f hq s))
      (5 * M - 4 * m + 8 - j) = 0 := by
    beta_reduce at inv
    omega
  unfold startsFrom at hz0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hz0
  have hx : (tableRule f hq)^[j + 1] s = (tableRule f hq)^[j] (tableRule f hq s) :=
    Function.iterate_succ_apply _ _ _
  have hL := iterate_left_zero (f := f) (hq := hq) (m := m)
    (fun i hi => by
      by_contra hc
      have := hlo i (Finsupp.mem_support_iff.mpr hc)
      omega) (j + 1)
  refine (diam_le_of_support_subset (m := m - (j + 1)) (M := 5 * M - 4 * m + 8 - j) ?_
    (by omega)).trans ?_
  · intro i hi
    constructor
    · by_contra hlt
      exact (Finsupp.mem_support_iff.mp hi) (hL i (by push_cast; omega))
    · by_contra hlt
      rw [hx] at hi
      have hi1 : (tableRule f hq)^[j] (tableRule f hq s) i = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi)
      by_cases h0 : (tableRule f hq)^[j] (tableRule f hq s) (i - 1) = 0
      · exact hz0 hi ⟨by omega, h0⟩
      · have h0' := zmod2_one_of_ne_zero _ h0
        by_cases h2 : (tableRule f hq)^[j] (tableRule f hq s) (i - 1 - 1) = 0
        · exact hz0 (mem_support_of_eq_one h0') ⟨by omega, h2⟩
        · have h2' := zmod2_one_of_ne_zero _ h2
          have := hN j (i - 2)
          rw [show i - 2 + 1 = i - 1 by ring, show i - 2 + 2 = i by ring,
            show i - 2 = i - 1 - 1 by ring] at this
          exact this ⟨h2', h0', hi1⟩
  · omega

/-! ## The class theorem -/

/-- **The left-clear class: the diameter grows at most five-fold.** If a cell is set after a step
only where its left neighbour was clear and it or its right neighbour was set, and a clear cell
with a clear left neighbour and a set right neighbour becomes set (the members among the quiescent
radius-one tables are the Wolfram numbers `2`, `6`, `10` and `14`), then every orbit's diameter is
at most five times its start's plus five. -/
theorem diam_iterate_le_of_leftClear
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) (htap : f 0 0 1 = 1)
    (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule f hq)^[k] s) ≤ 5 * diam s + 5 := by
  by_cases hs : s = 0
  · subst hs
    rw [Function.iterate_fixed (tableRule_zero' f hq), diam_zero']
    omega
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hmm := Finset.min'_le_max' s.support hne
    have hd := diam_eq' hne
    rcases k with _ | j
    · simp only [Function.iterate_zero, id_eq]
      omega
    · have := diam_succ_iterate_le (f := f) (hq := hq) hf htap hmm
        (fun x hx => Finset.min'_le _ _ hx) (fun x hx => Finset.le_max' _ _ hx) j
      omega

/-- **The left-clear bound passes to the mirror table**, by reflection. -/
theorem diam_iterate_le_of_leftClear_mirror
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) (htap : f 0 0 1 = 1)
    (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule (mirrorTable f) hq)^[k] s) ≤ 5 * diam s + 5 := by
  have h1 := diam_iterate_le_of_leftClear (hq := hq) hf htap (reflect s) k
  rw [diam_reflect] at h1
  have e : (tableRule (mirrorTable f) hq)^[k] s =
      reflect ((tableRule f hq)^[k] (reflect s)) := by
    conv_lhs => rw [← reflect_reflect s]
    exact iterate_mirror_reflect f hq (reflect s) k
  rw [e, diam_reflect]
  exact h1

/-- **An affine diameter bound forces a zero growing width**: no state has an orbit of unbounded
diameter, so the growing part is empty. -/
theorem growingWidth_lightCone_eq_zero_of_diam_le_affine
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℕ}
    (h : ∀ (s : ℤ →₀ ZMod 2) (k : ℕ), diam (U^[k] s) ≤ a * diam s + b) (n t : ℕ) :
    growingWidth U diam (lightCone n) t = 0 := by
  apply growingWidth_eq_zero_of_growingPart_eq_empty
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨k, hk⟩ := hs (a * diam s + b)
  have := h s k
  omega

/-- **Identically zero growing width in the left-clear class**: the diameter along every orbit is
at most five times its start's plus five (`diam_iterate_le_of_leftClear`). -/
theorem growingWidth_lightCone_eq_zero_of_leftClear
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) (htap : f 0 0 1 = 1) (n t : ℕ) :
    growingWidth (tableRule f hq) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_affine
    (fun s k => diam_iterate_le_of_leftClear hf htap s k) n t

/-- **Identically zero growing width at the mirror of a left-clear table**, by reflection
(`diam_iterate_le_of_leftClear_mirror`). -/
theorem growingWidth_lightCone_eq_zero_mirror_of_leftClear
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    (hf : ∀ a b c, f a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) (htap : f 0 0 1 = 1) (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f) hq) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_affine
    (fun s k => diam_iterate_le_of_leftClear_mirror hf htap s k) n t

/-! ## The two tables -/

/-- **Table `14`**, `f a b c = if a = 1 then 0 else (if b = 1 then 1 else c)`. The Wolfram number
`14` sets the bits `4 a + 2 b + c` listed in `f14_values`. -/
def f14 (a b c : ZMod 2) : ZMod 2 := if a = 1 then 0 else (if b = 1 then 1 else c)

/-- Quiescence of `f14`. -/
theorem hq14 : f14 0 0 0 = 0 := by decide

/-- The eight values of `f14` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `14`. -/
theorem f14_values :
    f14 0 0 0 = 0 ∧ f14 0 0 1 = 1 ∧ f14 0 1 0 = 1 ∧
      f14 0 1 1 = 1 ∧ f14 1 0 0 = 0 ∧ f14 1 0 1 = 0 ∧
      f14 1 1 0 = 0 ∧ f14 1 1 1 = 0 := by decide

/-- `f14` meets the left-clear hypothesis. -/
theorem f14_leftClear : ∀ a b c, f14 a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1) := by decide

/-- `f14` sets a clear cell with a clear left neighbour and a set right neighbour. -/
theorem f14_tap : f14 0 0 1 = 1 := by decide

/-- **Table `6`**, `f a b c = if a = 1 then 0 else b + c`. The Wolfram number `6` sets the bits
`4 a + 2 b + c` listed in `f6_values`. -/
def f6 (a b c : ZMod 2) : ZMod 2 := if a = 1 then 0 else b + c

/-- Quiescence of `f6`. -/
theorem hq6 : f6 0 0 0 = 0 := by decide

/-- The eight values of `f6` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `6`. -/
theorem f6_values :
    f6 0 0 0 = 0 ∧ f6 0 0 1 = 1 ∧ f6 0 1 0 = 1 ∧
      f6 0 1 1 = 0 ∧ f6 1 0 0 = 0 ∧ f6 1 0 1 = 0 ∧
      f6 1 1 0 = 0 ∧ f6 1 1 1 = 0 := by decide

/-- `f6` meets the left-clear hypothesis. -/
theorem f6_leftClear : ∀ a b c, f6 a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1) := by decide

/-- `f6` sets a clear cell with a clear left neighbour and a set right neighbour. -/
theorem f6_tap : f6 0 0 1 = 1 := by decide

set_option maxRecDepth 8000 in
/-- **None of the four left-clear tables is in either endpoint class**: `f14`, `f6` and their
mirrors lie in neither `AccretesByEndpoints` nor `ZeroByEndpoints`. -/
theorem not_mem_endpoint_classes_leftClear_four :
    ∀ f ∈ ([f14, f6, mirrorTable f14, mirrorTable f6] :
        List (ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)),
      ¬ EndpointClasses.AccretesByEndpoints f ∧ ¬ EndpointClasses.ZeroByEndpoints f := by
  decide

/-- **Identically zero growing width at `f14`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_f14 (n t : ℕ) :
    growingWidth (tableRule f14 hq14) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_leftClear f14_leftClear f14_tap n t

/-- **Identically zero growing width at `mirrorTable f14`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_mirror_f14 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f14) hq14) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_mirror_of_leftClear f14_leftClear f14_tap n t

/-- **Identically zero growing width at `f6`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_f6 (n t : ℕ) :
    growingWidth (tableRule f6 hq6) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_leftClear f6_leftClear f6_tap n t

/-- **Identically zero growing width at `mirrorTable f6`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_mirror_f6 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f6) hq6) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_mirror_of_leftClear f6_leftClear f6_tap n t

/-- **The four left-clear tables** ([RuleSpace] §3 Proposition 3.7). For every
window width `n` and every stage `t`, the growing width along the light cone is zero at `f14`, `f6`
and at their two mirrors. -/
theorem growingWidth_lightCone_leftClear_four (n t : ℕ) :
    growingWidth (tableRule f14 hq14) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f14) hq14) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule f6 hq6) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f6) hq6) diam (lightCone n) t = 0 :=
  ⟨growingWidth_lightCone_eq_zero_f14 n t, growingWidth_lightCone_eq_zero_mirror_f14 n t,
    growingWidth_lightCone_eq_zero_f6 n t, growingWidth_lightCone_eq_zero_mirror_f6 n t⟩

/-! ## The hypotheses together, the guard, and the growth -/

/-- **The two hypotheses of the class theorem hold together**, at table `14`, and the bound they
give is an instance. -/
theorem diam_iterate_le_of_leftClear_nonvacuous :
    ((∀ a b c, f14 a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) ∧ f14 0 0 1 = 1) ∧
      ∀ (s : ℤ →₀ ZMod 2) (k : ℕ),
        diam ((tableRule f14 hq14)^[k] s) ≤ 5 * diam s + 5 :=
  ⟨⟨f14_leftClear, f14_tap⟩, fun s k => diam_iterate_le_of_leftClear f14_leftClear f14_tap s k⟩

/-- **The shape hypothesis is load-bearing**: `f106` sets a clear cell with a clear left neighbour
and a set right neighbour, its shape hypothesis fails (`f106 1 1 0 = 1`, with a set left
neighbour), and its growing part under the diameter is not empty, since the two-cell state has an
orbit of unbounded diameter (`seedOneOne_mem_growingPart_f106`). -/
theorem leftClear_hypothesis_load_bearing :
    f106 0 0 1 = 1 ∧
    (f106 1 1 0 = 1 ∧ ¬ (∀ a b c, f106 a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1))) ∧
    seedOneOne ∈ GrowingPart (tableRule f106 hq106) diam ∧
    GrowingPart (tableRule f106 hq106) diam ≠ ∅ :=
  ⟨by decide, ⟨by decide, by decide⟩, seedOneOne_mem_growingPart_f106,
    Set.nonempty_iff_ne_empty.mp ⟨_, seedOneOne_mem_growingPart_f106⟩⟩

/-- The state with exactly the cells of a list set. -/
private noncomputable def stateOf (L : List ℤ) : ℤ →₀ ZMod 2 :=
  ∑ i ∈ L.toFinset, Finsupp.single i 1

private theorem stateOf_apply (L : List ℤ) (x : ℤ) : stateOf L x = if x ∈ L then 1 else 0 := by
  classical
  simp [stateOf, Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem diam_stateOf {L : List ℤ} {a b : ℤ} (hab : a ≤ b) (ha : a ∈ L) (hb : b ∈ L)
    (h : ∀ x ∈ L, a ≤ x ∧ x ≤ b) : diam (stateOf L) = (b - a).toNat + 1 :=
  diam_eq_of_cells _ hab (by simp [stateOf_apply, ha])
    (by simp [stateOf_apply, hb]) (fun x hx => by
      have hm : x ∉ L := fun hm => by have := h x hm; omega
      simp [stateOf_apply, hm])

private theorem step_stateOf {L L' : List ℤ}
    (h : ∀ x : ℤ, f14 (if x - 1 ∈ L then 1 else 0) (if x ∈ L then 1 else 0)
      (if x + 1 ∈ L then 1 else 0) = if x ∈ L' then 1 else 0) :
    tableRule f14 hq14 (stateOf L) = stateOf L' := by
  ext x
  rw [tableRule_apply, stateOf_apply, stateOf_apply, stateOf_apply, stateOf_apply]
  exact h x

/-- **The diameter does grow in the left-clear class, by more than two**: the alternating state on
the cells `0`, `2`, `4` has diameter `5`, and after five steps of `f14` its diameter is `10`. -/
theorem diam_iterate_five_alternating_f14 :
    diam (Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 4 1 : ℤ →₀ ZMod 2) = 5 ∧
    diam ((tableRule f14 hq14)^[5]
      (Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 4 1 : ℤ →₀ ZMod 2)) = 10 := by
  have e0 : (Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 4 1 : ℤ →₀ ZMod 2) =
      stateOf [0, 2, 4] := by
    ext x
    rw [stateOf_apply]
    simp only [Finsupp.add_apply, Finsupp.single_apply, List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> first | (exfalso; omega) | decide
  have s1 : tableRule f14 hq14 (stateOf [0, 2, 4]) = stateOf [-1, 0, 2, 4] := by
    apply step_stateOf; intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> first | (exfalso; omega) | decide
  have s2 : tableRule f14 hq14 (stateOf [-1, 0, 2, 4]) = stateOf [-2, -1, 2, 4] := by
    apply step_stateOf; intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> first | (exfalso; omega) | decide
  have s3 : tableRule f14 hq14 (stateOf [-2, -1, 2, 4]) = stateOf [-3, -2, 1, 2, 4] := by
    apply step_stateOf; intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> first | (exfalso; omega) | decide
  have s4 : tableRule f14 hq14 (stateOf [-3, -2, 1, 2, 4]) = stateOf [-4, -3, 0, 1, 4] := by
    apply step_stateOf; intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> first | (exfalso; omega) | decide
  have s5 : tableRule f14 hq14 (stateOf [-4, -3, 0, 1, 4]) = stateOf [-5, -4, -1, 0, 3, 4] := by
    apply step_stateOf; intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> first | (exfalso; omega) | decide
  rw [e0]
  refine ⟨?_, ?_⟩
  · rw [diam_stateOf (a := 0) (b := 4) (by omega) (by simp) (by simp) (by simp)]
    rfl
  · simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq]
    rw [s1, s2, s3, s4, s5]
    rw [diam_stateOf (a := -5) (b := 4) (by omega) (by simp) (by simp) (by simp)]
    rfl

/-! ## Block ends, and table `142` -/

/-- The number of block ends at or beyond `q`: set cells whose right neighbour is clear. -/
def endsFrom (x : ℤ →₀ ZMod 2) (q : ℤ) : ℕ :=
  (x.support.filter (fun i => q ≤ i ∧ x (i + 1) = 0)).card

/-- **Table `142`**, `f a b c = if a = 1 then b * c else (if b = 1 then 1 else c)`. The Wolfram
number `142` sets the bits `4 a + 2 b + c` listed in `f142_values`. -/
def f142 (a b c : ZMod 2) : ZMod 2 := if a = 1 then b * c else (if b = 1 then 1 else c)

/-- Quiescence of `f142`. -/
theorem hq142 : f142 0 0 0 = 0 := by decide

/-- The eight values of `f142` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `142`. -/
theorem f142_values :
    f142 0 0 0 = 0 ∧ f142 0 0 1 = 1 ∧ f142 0 1 0 = 1 ∧
      f142 0 1 1 = 1 ∧ f142 1 0 0 = 0 ∧ f142 1 0 1 = 0 ∧
      f142 1 1 0 = 0 ∧ f142 1 1 1 = 1 := by decide

/-- A block end of an image of `f142` is a one-cell block of the state, or the cell before a block
end of the state. -/
private theorem f142_one_end : ∀ a b c d : ZMod 2, f142 a b c = 1 → f142 b c d = 0 →
    (a = 0 ∧ b = 1 ∧ c = 0) ∨ (b = 1 ∧ c = 1 ∧ d = 0) := by decide

/-- The seven cells `x (i - 4) .. x (i + 2)` of a state decide the reach of an isolated set cell of
its image: a set cell with both neighbours clear has a set cell two or three places to its left. -/
private theorem f142_reach : ∀ a0 a1 a2 a3 a4 a5 a6 : ZMod 2,
    f142 a3 a4 a5 = 1 → f142 a2 a3 a4 = 0 → f142 a4 a5 a6 = 0 →
    f142 a1 a2 a3 = 1 ∨ f142 a0 a1 a2 = 1 := by decide

/-- The states in which every set cell with both neighbours clear has a set cell two or three
places to its left. -/
private def Reaches (x : ℤ →₀ ZMod 2) : Prop :=
  ∀ i, x i = 1 → x (i - 1) = 0 → x (i + 1) = 0 → x (i - 2) = 1 ∨ x (i - 3) = 1

/-- Every image of `f142` has the reach property. -/
private theorem reaches_tableRule_f142 (x : ℤ →₀ ZMod 2) : Reaches (tableRule f142 hq142 x) := by
  intro i h1 h2 h3
  have := f142_reach (x (i - 4)) (x (i - 3)) (x (i - 2)) (x (i - 1)) (x i) (x (i + 1)) (x (i + 2))
  simp only [tableRule_apply, show i - 2 - 1 = i - 3 by ring, show i - 2 + 1 = i - 1 by ring,
    show i - 3 - 1 = i - 4 by ring, show i - 3 + 1 = i - 2 by ring,
    show i - 1 - 1 = i - 2 by ring, show i - 1 + 1 = i by ring, show i + 1 - 1 = i by ring,
    show i + 1 + 1 = i + 2 by ring] at h1 h2 h3 ⊢
  exact this h1 h2 h3

/-- **One step of `f142`**: the block ends at or beyond `q - 1` after a step number at most the
block ends at or beyond `q` before it, plus one when the cells `q - 2`, `q - 1`, `q` read clear,
set, clear. -/
private theorem endsFrom_step_le_f142 (x : ℤ →₀ ZMod 2) (q : ℤ) :
    endsFrom (tableRule f142 hq142 x) (q - 1) ≤
      endsFrom x q + (if x (q - 2) = 0 ∧ x (q - 1) = 1 ∧ x q = 0 then 1 else 0) := by
  classical
  have key : ∀ i, tableRule f142 hq142 x i = 1 → tableRule f142 hq142 x (i + 1) = 0 →
      (x (i - 1) = 0 ∧ x i = 1 ∧ x (i + 1) = 0) ∨ (x i = 1 ∧ x (i + 1) = 1 ∧ x (i + 2) = 0) := by
    intro i h1 h2
    rw [tableRule_apply] at h1 h2
    rw [show i + 1 + 1 = i + 2 by ring, show i + 1 - 1 = i by ring] at h2
    exact f142_one_end _ _ _ _ h1 h2
  let g : ℤ → ℤ := fun i => if x (i + 1) = 1 then i + 1 else i
  let T : Finset ℤ := x.support.filter (fun i => q ≤ i ∧ x (i + 1) = 0) ∪
    (if x (q - 2) = 0 ∧ x (q - 1) = 1 ∧ x q = 0 then {q - 1} else ∅)
  have hcard : endsFrom (tableRule f142 hq142 x) (q - 1) ≤ T.card := by
    unfold endsFrom
    apply Finset.card_le_card_of_injOn g
    · intro i hi
      obtain ⟨hi1, hi2, hi3⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      have hz1 : tableRule f142 hq142 x i = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi1)
      simp only [T, Finset.mem_coe, Finset.mem_union, Finset.mem_filter]
      rcases key i hz1 hi3 with ⟨k0, k1, k2⟩ | ⟨k1, k2, k3⟩
      · have hgi : g i = i := by simp [g, k2]
        rw [hgi]
        by_cases hiq : q ≤ i
        · exact Or.inl ⟨mem_support_of_eq_one k1, hiq, k2⟩
        · have hi' : i = q - 1 := by omega
          subst hi'
          right
          rw [show q - 1 - 1 = q - 2 by ring] at k0
          rw [show q - 1 + 1 = q by ring] at k2
          have hcond : x (q - 2) = 0 ∧ x (q - 1) = 1 ∧ x q = 0 := ⟨k0, k1, k2⟩
          simp [hcond]
      · have hgi : g i = i + 1 := by simp [g, k2]
        rw [hgi]
        refine Or.inl ⟨mem_support_of_eq_one k2, by omega, ?_⟩
        rw [show i + 1 + 1 = i + 2 by ring]
        exact k3
    · intro i hi j hj hij
      replace hi := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      replace hj := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
      have hzi : tableRule f142 hq142 x i = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi.1)
      have hzj : tableRule f142 hq142 x j = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hj.1)
      by_cases hxi : x (i + 1) = 1 <;> by_cases hxj : x (j + 1) = 1
      · simpa [g, hxi, hxj] using hij
      · have hgi : g i = i + 1 := by simp [g, hxi]
        have hgj : g j = j := by simp [g, hxj]
        have hji : i + 1 = j := by simp only [hgi, hgj] at hij; exact hij
        rw [← hji] at hzj
        rw [hzj] at hi
        exact absurd hi.2.2 (by decide)
      · have hgi : g i = i := by simp [g, hxi]
        have hgj : g j = j + 1 := by simp [g, hxj]
        have hji : i = j + 1 := by simp only [hgi, hgj] at hij; exact hij
        rw [hji] at hzi
        rw [hzi] at hj
        exact absurd hj.2.2 (by decide)
      · simpa [g, hxi, hxj] using hij
  refine hcard.trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  unfold endsFrom
  split_ifs <;> simp

/-- **The pattern clear, set, clear costs two further ends to its left**, where every isolated set
cell has a set cell two or three places to its left: the cell `q - 1` is an end, and the run
through `q - 3` or `q - 4` ends at `q - 3` or `q - 4`. -/
private theorem endsFrom_pattern_le_f142 {x : ℤ →₀ ZMod 2} (hR : Reaches x) (q : ℤ)
    (h0 : x (q - 2) = 0) (h1 : x (q - 1) = 1) (h2 : x q = 0) :
    endsFrom x q + 2 ≤ endsFrom x (q - 4) := by
  classical
  have hr := hR (q - 1) h1 (by rw [show q - 1 - 1 = q - 2 by ring]; exact h0)
    (by rw [show q - 1 + 1 = q by ring]; exact h2)
  rw [show q - 1 - 2 = q - 3 by ring, show q - 1 - 3 = q - 4 by ring] at hr
  obtain ⟨p, hp1, hp2, hp3, hp4, hp5⟩ :
      ∃ p : ℤ, p ≠ q - 1 ∧ p < q ∧ q - 4 ≤ p ∧ x p = 1 ∧ x (p + 1) = 0 := by
    by_cases h3 : x (q - 3) = 1
    · exact ⟨q - 3, by omega, by omega, by omega, h3,
        by rw [show q - 3 + 1 = q - 2 by ring]; exact h0⟩
    · have h4 : x (q - 4) = 1 := hr.resolve_left h3
      refine ⟨q - 4, by omega, by omega, le_refl _, h4, ?_⟩
      rw [show q - 4 + 1 = q - 3 by ring]
      exact zmod2_eq_zero_of_ne_one _ h3
  have hsub : insert (q - 1) (insert p (x.support.filter (fun i => q ≤ i ∧ x (i + 1) = 0))) ⊆
      x.support.filter (fun i => q - 4 ≤ i ∧ x (i + 1) = 0) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_filter] at hi ⊢
    rcases hi with rfl | rfl | ⟨hs, hq, hz⟩
    · exact ⟨mem_support_of_eq_one h1, by omega, by rw [show q - 1 + 1 = q by ring]; exact h2⟩
    · exact ⟨mem_support_of_eq_one hp4, hp3, hp5⟩
    · exact ⟨hs, by omega, hz⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] at hc
  · unfold endsFrom
    omega
  · simp only [Finset.mem_filter]
    omega
  · simp only [Finset.mem_insert, Finset.mem_filter]
    omega

/-- The diameter bound of the images of `f142` from the two ends of the support: every image from
the first on spreads at most to `4 * (M - m) + 5` cells. -/
private theorem diam_succ_iterate_le_f142 {s : ℤ →₀ ZMod 2} {m M : ℤ} (hmM : m ≤ M)
    (hlo : ∀ x ∈ s.support, m ≤ x) (hhi : ∀ x ∈ s.support, x ≤ M) (j : ℕ) :
    diam ((tableRule f142 hq142)^[j + 1] s) ≤ (4 * (M - m) + 4).toNat + 1 := by
  classical
  have hR : ∀ j : ℕ, Reaches ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) := fun j => by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
    exact reaches_tableRule_f142 _
  have hbase : ∀ q : ℤ, 4 * endsFrom ((tableRule f142 hq142)^[0] (tableRule f142 hq142 s)) q ≤
      (4 * M - 3 * m + 7 - q).toNat := by
    intro q
    simp only [Function.iterate_zero, id_eq]
    have hsub : (tableRule f142 hq142 s).support.filter
        (fun i => q ≤ i ∧ tableRule f142 hq142 s (i + 1) = 0) ⊆ Finset.Icc (max q (m - 1)) M := by
      intro i hi
      obtain ⟨hi1, hi2, _⟩ := Finset.mem_filter.mp hi
      have hz : tableRule f142 hq142 s i = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi1)
      rw [tableRule_apply] at hz
      have hb : s i = 1 ∨ s (i + 1) = 1 := by
        revert hz
        generalize s (i - 1) = a
        generalize s i = b
        generalize s (i + 1) = c
        revert a b c
        decide
      rw [Finset.mem_Icc]
      rcases hb with h | h
      · have := hlo _ (mem_support_of_eq_one h)
        have := hhi _ (mem_support_of_eq_one h)
        exact ⟨max_le hi2 (by omega), by omega⟩
      · have := hlo _ (mem_support_of_eq_one h)
        have := hhi _ (mem_support_of_eq_one h)
        exact ⟨max_le hi2 (by omega), by omega⟩
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    unfold endsFrom
    omega
  have hstep : ∀ (j : ℕ) (q : ℤ),
      endsFrom ((tableRule f142 hq142)^[j + 1] (tableRule f142 hq142 s)) (q - 1) ≤
        endsFrom ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) q + 1 := by
    intro j q
    rw [Function.iterate_succ_apply']
    refine (endsFrom_step_le_f142 _ q).trans ?_
    split_ifs <;> omega
  have hhold : ∀ (j : ℕ) (q : ℤ),
      ¬ (((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) (q - 2) = 0 ∧
        ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) (q - 1) = 1 ∧
        ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) q = 0) →
      endsFrom ((tableRule f142 hq142)^[j + 1] (tableRule f142 hq142 s)) (q - 1) ≤
        endsFrom ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) q := by
    intro j q hc
    rw [Function.iterate_succ_apply']
    refine (endsFrom_step_le_f142 _ q).trans ?_
    simp [hc]
  have hP : ∀ (j : ℕ) (q : ℤ),
      (((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) (q - 2) = 0 ∧
        ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) (q - 1) = 1 ∧
        ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) q = 0) →
      endsFrom ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) q + 2 ≤
        endsFrom ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) (q - ((4 : ℕ) : ℤ)) := by
    intro j q ⟨h0, h1, h2⟩
    exact endsFrom_pattern_le_f142 (hR j) q h0 h1 h2
  have inv := count_invariant_of_step (N := fun j q => endsFrom ((tableRule f142 hq142)^[j]
      (tableRule f142 hq142 s)) q)
    (P := fun j q => ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) (q - 2) = 0 ∧
        ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) (q - 1) = 1 ∧
        ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)) q = 0) 4 (4 * M - 3 * m + 7)
    hstep hhold hP hbase j (4 * M - 3 * m + 4)
  have hz0 : endsFrom ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s))
      (4 * M - 3 * m + 4 - j) = 0 := by
    beta_reduce at inv
    omega
  have hx : (tableRule f142 hq142)^[j + 1] s =
      (tableRule f142 hq142)^[j] (tableRule f142 hq142 s) :=
    Function.iterate_succ_apply _ _ _
  have hL := iterate_left_zero (f := f142) (hq := hq142) (m := m)
    (fun i hi => by
      by_contra hc
      have := hlo i (Finsupp.mem_support_iff.mpr hc)
      omega) (j + 1)
  refine (diam_le_of_support_subset (m := m - (j + 1)) (M := 4 * M - 3 * m + 3 - j) ?_
    (by omega)).trans ?_
  · intro i hi
    constructor
    · by_contra hlt
      exact (Finsupp.mem_support_iff.mp hi) (hL i (by push_cast; omega))
    · by_contra hlt
      rw [hx] at hi
      have hne : ((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)).support.Nonempty := ⟨i, hi⟩
      have hmax := Finset.max'_mem _ hne
      have hge := Finset.le_max' _ i hi
      have hmax1 := zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hmax)
      have hmax0 : (tableRule f142 hq142)^[j] (tableRule f142 hq142 s)
          (((tableRule f142 hq142)^[j] (tableRule f142 hq142 s)).support.max' hne + 1) = 0 := by
        by_contra hc
        have := Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hc)
        omega
      unfold endsFrom at hz0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hz0
      exact hz0 hmax ⟨by omega, hmax0⟩
  · omega

/-- **Table `142` does not accrete: a count of block ends bounds every orbit's diameter.** Every
orbit's diameter at `f142` is at most five times its start's plus five. The block ends at or
beyond a cell `q` of an image number at most the block ends at or beyond `q + 1` of the state,
plus one when the cells `q - 2`, `q - 1`, `q` of the state read clear, set, clear; in an image that
pattern costs two further block ends to the left, since an isolated set cell of an image has a set
cell two or three places to its left. -/
theorem diam_iterate_le_f142 (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule f142 hq142)^[k] s) ≤ 5 * diam s + 5 := by
  by_cases hs : s = 0
  · subst hs
    rw [Function.iterate_fixed (tableRule_zero' f142 hq142), diam_zero']
    omega
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hmm := Finset.min'_le_max' s.support hne
    have hd := diam_eq' hne
    rcases k with _ | j
    · simp only [Function.iterate_zero, id_eq]
      omega
    · have := diam_succ_iterate_le_f142 hmm
        (fun x hx => Finset.min'_le _ _ hx) (fun x hx => Finset.le_max' _ _ hx) j
      omega

/-- **The bound passes to the mirror of table `142`**, by reflection. -/
theorem diam_iterate_le_mirror_f142 (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule (mirrorTable f142) hq142)^[k] s) ≤ 5 * diam s + 5 := by
  have h1 := diam_iterate_le_f142 (reflect s) k
  rw [diam_reflect] at h1
  have e : (tableRule (mirrorTable f142) hq142)^[k] s =
      reflect ((tableRule f142 hq142)^[k] (reflect s)) := by
    conv_lhs => rw [← reflect_reflect s]
    exact iterate_mirror_reflect f142 hq142 (reflect s) k
  rw [e, diam_reflect]
  exact h1

/-- **Identically zero growing width at `f142`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_f142 (n t : ℕ) :
    growingWidth (tableRule f142 hq142) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_affine
    (fun s k => diam_iterate_le_f142 s k) n t

/-- **Identically zero growing width at `mirrorTable f142`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_mirror_f142 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f142) hq142) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_affine
    (fun s k => diam_iterate_le_mirror_f142 s k) n t

set_option maxRecDepth 8000 in
/-- **Table `142` and its mirror are in neither endpoint class**: `f142` and `mirrorTable f142`
lie in neither `AccretesByEndpoints` nor `ZeroByEndpoints`. -/
theorem not_mem_endpoint_classes_f142 :
    ∀ f ∈ ([f142, mirrorTable f142] : List (ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)),
      ¬ EndpointClasses.AccretesByEndpoints f ∧ ¬ EndpointClasses.ZeroByEndpoints f := by
  decide

/-- **Table `142` is outside the left-clear class**: it sets a clear cell with a clear left
neighbour and a set right neighbour, and it sets a cell whose left neighbour is set
(`f142 1 1 1 = 1`), so the shape hypothesis of `diam_iterate_le_of_leftClear` fails. -/
theorem f142_not_leftClear :
    f142 0 0 1 = 1 ∧ f142 1 1 1 = 1 ∧
      ¬ (∀ a b c, f142 a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := (h 1 1 1 (by decide)).1
  exact absurd this (by decide)

/-- **The reach property is load-bearing for the end count.** The state with the single cell `0`
set has clear cells at `-1`, `1`, `-2` and `-3` beside it, so a set cell with both neighbours
clear has no set cell two or three places to its left; at `q = 1` the cells `q - 2`, `q - 1`, `q`
read clear, set, clear, and the block ends at or beyond `q - 4` number only one more than the
block ends at or beyond `q`: the gain is one, not two. -/
theorem endsFrom_pattern_gain_one :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 = 1 ∧ (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-1) = 0 ∧
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 = 0 ∧ (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-2) = 0 ∧
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-3) = 0 ∧
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (1 - 2) = 0 ∧
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (1 - 1) = 1 ∧
    endsFrom (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 = 0 ∧
    endsFrom (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (1 - 4) = 1 := by
  have hs : (Finsupp.single (0 : ℤ) (1 : ZMod 2)).support = {0} :=
    Finsupp.support_single _ (by decide)
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, ?_, ?_⟩
  · unfold endsFrom
    rw [hs]
    decide
  · unfold endsFrom
    rw [hs]
    simp [Finset.filter_singleton]

/-! ## Table `134` -/

/-- **Table `134`**, `f a b c = if a = 1 then b * c else b + c`. The Wolfram number `134` sets the
bits `4 a + 2 b + c` listed in `f134_values`: the triples `001`, `010` and `111`. Away from the
triple `111` it agrees with `f6`. -/
def f134 (a b c : ZMod 2) : ZMod 2 := if a = 1 then b * c else b + c

/-- Quiescence of `f134`. -/
theorem hq134 : f134 0 0 0 = 0 := by decide

/-- The eight values of `f134` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
the bit pattern of the Wolfram number `134`. -/
theorem f134_values :
    f134 0 0 0 = 0 ∧ f134 0 0 1 = 1 ∧ f134 0 1 0 = 1 ∧
      f134 0 1 1 = 0 ∧ f134 1 0 0 = 0 ∧ f134 1 0 1 = 0 ∧
      f134 1 1 0 = 0 ∧ f134 1 1 1 = 1 := by decide

/-- Three consecutive set cells of an image of `f134` come from five consecutive set cells. -/
private theorem f134_three_run : ∀ a0 a1 a2 a3 a4 : ZMod 2,
    f134 a0 a1 a2 = 1 → f134 a1 a2 a3 = 1 → f134 a2 a3 a4 = 1 →
      a0 = 1 ∧ a1 = 1 ∧ a2 = 1 ∧ a3 = 1 ∧ a4 = 1 := by decide

/-- Away from the triple `111` the tables `f134` and `f6` agree. -/
private theorem f134_eq_f6 : ∀ a b c : ZMod 2, ¬ (a = 1 ∧ b = 1 ∧ c = 1) →
    f134 a b c = f6 a b c := by decide

/-- A set cell of an image of `f134` has itself or its right neighbour set. -/
private theorem f134_self_or_right : ∀ a b c : ZMod 2, f134 a b c = 1 → b = 1 ∨ c = 1 := by
  decide

/-- The cells of five consecutive positions behind three consecutive set cells of an image. -/
private theorem f134_cells (x : ℤ →₀ ZMod 2) (p : ℤ)
    (h0 : tableRule f134 hq134 x p = 1) (h1 : tableRule f134 hq134 x (p + 1) = 1)
    (h2 : tableRule f134 hq134 x (p + 2) = 1) :
    x (p - 1) = 1 ∧ x p = 1 ∧ x (p + 1) = 1 ∧ x (p + 2) = 1 ∧ x (p + 3) = 1 := by
  rw [tableRule_apply] at h0 h1 h2
  rw [show p + 1 - 1 = p by ring, show p + 1 + 1 = p + 2 by ring] at h1
  rw [show p + 2 - 1 = p + 1 by ring, show p + 2 + 1 = p + 3 by ring] at h2
  exact f134_three_run _ _ _ _ _ h0 h1 h2

/-- A run of `L` consecutive set cells. -/
private def HasRun (x : ℤ →₀ ZMod 2) (L : ℕ) : Prop :=
  ∃ i : ℤ, ∀ t : ℕ, t < L → x (i + t) = 1

/-- **Runs shorten by two**: a run of `n + 3` set cells in an image of `f134` comes from a run of
`n + 5` set cells. -/
private theorem hasRun_shorten (x : ℤ →₀ ZMod 2) (n : ℕ)
    (hr : HasRun (tableRule f134 hq134 x) (n + 3)) : HasRun x (n + 5) := by
  obtain ⟨i, h⟩ := hr
  have win : ∀ u : ℕ, u ≤ n →
      x (i + u - 1) = 1 ∧ x (i + u) = 1 ∧ x (i + u + 1) = 1 ∧ x (i + u + 2) = 1 ∧
        x (i + u + 3) = 1 := by
    intro u hu
    refine f134_cells x (i + u) (h u (by omega)) ?_ ?_
    · have := h (u + 1) (by omega)
      rwa [Nat.cast_succ, ← add_assoc] at this
    · have := h (u + 2) (by omega)
      rwa [Nat.cast_add, ← add_assoc, Nat.cast_ofNat] at this
  refine ⟨i - 1, fun t ht => ?_⟩
  by_cases htn : t ≤ n
  · have := (win t htn).1
    rwa [show i + (t : ℤ) - 1 = i - 1 + t by ring] at this
  · have w := win n le_rfl
    have hcase : t = n + 1 ∨ t = n + 2 ∨ t = n + 3 ∨ t = n + 4 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · rw [show i - 1 + ((n + 1 : ℕ) : ℤ) = i + n by push_cast; ring]; exact w.2.1
    · rw [show i - 1 + ((n + 2 : ℕ) : ℤ) = i + n + 1 by push_cast; ring]; exact w.2.2.1
    · rw [show i - 1 + ((n + 3 : ℕ) : ℤ) = i + n + 2 by push_cast; ring]; exact w.2.2.2.1
    · rw [show i - 1 + ((n + 4 : ℕ) : ℤ) = i + n + 3 by push_cast; ring]; exact w.2.2.2.2

/-- No run of three set cells is the absence of three set cells in a row. -/
private theorem noThree_of_not_hasRun {x : ℤ →₀ ZMod 2} (h : ¬ HasRun x 3) : NoThree x := by
  intro i ⟨h0, h1, h2⟩
  refine h ⟨i, fun t ht => ?_⟩
  have ht3 : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases ht3 with rfl | rfl | rfl
  · simpa using h0
  · simpa using h1
  · simpa [add_assoc] using h2

/-- A state with a run of `L` set cells has diameter at least `L`. -/
private theorem le_diam_of_hasRun {x : ℤ →₀ ZMod 2} {L : ℕ} (hL : 1 ≤ L) (h : HasRun x L) :
    L ≤ diam x := by
  obtain ⟨i, hi⟩ := h
  have h0 : i ∈ x.support := mem_support_of_eq_one (by simpa using hi 0 (by omega))
  have h1 : i + ((L - 1 : ℕ) : ℤ) ∈ x.support := mem_support_of_eq_one (hi (L - 1) (by omega))
  have hne : x.support.Nonempty := ⟨i, h0⟩
  have a1 := Finset.min'_le x.support i h0
  have a2 := Finset.le_max' x.support _ h1
  rw [diam_eq' hne]
  omega

/-- **No long runs survive**: if the start has diameter `d`, the `j`-th image of `f134` has no run
of `L` set cells once `3 ≤ L` and `d + 1 ≤ L + 2 j`. -/
private theorem noRun_iterate_f134 (s : ℤ →₀ ZMod 2) (j : ℕ) :
    ∀ L : ℕ, 3 ≤ L → diam s + 1 ≤ L + 2 * j → ¬ HasRun ((tableRule f134 hq134)^[j] s) L := by
  induction j with
  | zero =>
    intro L hL hd hr
    simp only [Function.iterate_zero, id_eq] at hr
    have := le_diam_of_hasRun (by omega) hr
    omega
  | succ j ih =>
    intro L hL hd hr
    obtain ⟨n, rfl⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
    rw [Function.iterate_succ_apply'] at hr
    exact ih (n + 5) (by omega) (by omega) (hasRun_shorten _ n hr)

/-- Off the triple `111` the images agree: if `x` has no three set cells in a row, one step of
`f134` is one step of `f6`. -/
private theorem tableRule_f134_eq_f6_of_noThree {x : ℤ →₀ ZMod 2} (hN : NoThree x) :
    tableRule f134 hq134 x = tableRule f6 hq6 x := by
  ext i
  rw [tableRule_apply, tableRule_apply]
  refine f134_eq_f6 _ _ _ fun ⟨a, b, c⟩ => hN (i - 1) ⟨a, ?_, ?_⟩
  · rwa [show i - 1 + 1 = i by ring]
  · rwa [show i - 1 + 2 = i + 1 by ring]

/-- One step of `f134` lengthens the diameter by at most one. -/
private theorem diam_tableRule_f134_le (x : ℤ →₀ ZMod 2) :
    diam (tableRule f134 hq134 x) ≤ diam x + 1 := by
  by_cases hne : x.support.Nonempty
  · have hmM := Finset.min'_le_max' x.support hne
    have key := diam_le_of_support_subset (t' := tableRule f134 hq134 x)
      (m := x.support.min' hne - 1) (M := x.support.max' hne) (fun y hy => by
        have hz : tableRule f134 hq134 x y = 1 :=
          zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hy)
        rw [tableRule_apply] at hz
        rcases f134_self_or_right _ _ _ hz with h | h
        · have a1 := Finset.min'_le x.support y (mem_support_of_eq_one h)
          have a2 := Finset.le_max' x.support y (mem_support_of_eq_one h)
          omega
        · have a1 := Finset.min'_le x.support (y + 1) (mem_support_of_eq_one h)
          have a2 := Finset.le_max' x.support (y + 1) (mem_support_of_eq_one h)
          omega) (by omega)
    rw [diam_eq' hne]
    omega
  · have : x = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hne)
    subst this
    rw [tableRule_zero' f134 hq134, diam_zero']
    omega

/-- **Table `134` does not accrete**: every orbit's diameter is at most ten times its start's plus
five. Runs of three or more set cells in an image of `f134` lie inside runs two cells longer of the
state, so after as many steps as the start's diameter no image has three set cells in a row, and
from then on `f134` and `f6` agree. The first steps lengthen the diameter by at most one each, and
the class bound at `f6` (`diam_iterate_le_of_leftClear`) takes over from a state of diameter at
most twice the start's. -/
theorem diam_iterate_le_f134 (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule f134 hq134)^[k] s) ≤ 10 * diam s + 5 := by
  have hN : ∀ j : ℕ, diam s ≤ j → NoThree ((tableRule f134 hq134)^[j] s) := fun j hj =>
    noThree_of_not_hasRun (noRun_iterate_f134 s j 3 le_rfl (by omega))
  have hag : ∀ j : ℕ, (tableRule f134 hq134)^[diam s + j] s =
      (tableRule f6 hq6)^[j] ((tableRule f134 hq134)^[diam s] s) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← add_assoc, Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      exact tableRule_f134_eq_f6_of_noThree (hN _ (by omega))
  have hgrow : ∀ j : ℕ, diam ((tableRule f134 hq134)^[j] s) ≤ diam s + j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      have := diam_tableRule_f134_le ((tableRule f134 hq134)^[j] s)
      omega
  rcases le_or_gt k (diam s) with hk | hk
  · have := hgrow k
    omega
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    rw [hag]
    have h1 := diam_iterate_le_of_leftClear (hq := hq6) f6_leftClear f6_tap
      ((tableRule f134 hq134)^[diam s] s) j
    have h2 := hgrow (diam s)
    omega

/-- **The bound passes to the mirror of table `134`**, by reflection. -/
theorem diam_iterate_le_mirror_f134 (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule (mirrorTable f134) hq134)^[k] s) ≤ 10 * diam s + 5 := by
  have h1 := diam_iterate_le_f134 (reflect s) k
  rw [diam_reflect] at h1
  have e : (tableRule (mirrorTable f134) hq134)^[k] s =
      reflect ((tableRule f134 hq134)^[k] (reflect s)) := by
    conv_lhs => rw [← reflect_reflect s]
    exact iterate_mirror_reflect f134 hq134 (reflect s) k
  rw [e, diam_reflect]
  exact h1

/-- **Identically zero growing width at `f134`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_f134 (n t : ℕ) :
    growingWidth (tableRule f134 hq134) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_affine
    (fun s k => diam_iterate_le_f134 s k) n t

/-- **Identically zero growing width at `mirrorTable f134`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_mirror_f134 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f134) hq134) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_affine
    (fun s k => diam_iterate_le_mirror_f134 s k) n t

set_option maxRecDepth 8000 in
/-- **Table `134` and its mirror are in neither endpoint class**: `f134` and `mirrorTable f134`
lie in neither `AccretesByEndpoints` nor `ZeroByEndpoints`. -/
theorem not_mem_endpoint_classes_f134 :
    ∀ f ∈ ([f134, mirrorTable f134] : List (ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)),
      ¬ EndpointClasses.AccretesByEndpoints f ∧ ¬ EndpointClasses.ZeroByEndpoints f := by
  decide

/-- **Table `134` is outside the left-clear class**: it sets a clear cell with a clear left
neighbour and a set right neighbour, and it sets a cell whose left neighbour is set
(`f134 1 1 1 = 1`), so the shape hypothesis of `diam_iterate_le_of_leftClear` fails. -/
theorem f134_not_leftClear :
    f134 0 0 1 = 1 ∧ f134 1 1 1 = 1 ∧
      ¬ (∀ a b c, f134 a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := (h 1 1 1 (by decide)).1
  exact absurd this (by decide)

/-- **The agreement of `f134` with `f6` needs its hypothesis**: at the state set on exactly the
cells `0`, `1` and `2`, one step of `f134` sets the cell `1` and one step of `f6` leaves it clear,
since the two tables differ at the triple `111`. -/
theorem tableRule_f134_ne_f6_block :
    tableRule f134 hq134
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 + Finsupp.single 2 1) 1 = 1 ∧
      tableRule f6 hq6
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 + Finsupp.single 2 1) 1 = 0 ∧
      tableRule f134 hq134
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 + Finsupp.single 2 1) 1 ≠
      tableRule f6 hq6
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 + Finsupp.single 2 1) 1 := by
  have e : ∀ x : ℤ, (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 +
      Finsupp.single 2 1 : ℤ →₀ ZMod 2) x = if x = 0 ∨ x = 1 ∨ x = 2 then 1 else 0 := by
    intro x
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    by_cases h0 : x = 0
    · subst h0; decide
    · by_cases h1 : x = 1
      · subst h1; decide
      · by_cases h2 : x = 2
        · subst h2; decide
        · simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, h0, h1, h2]
  have c1 : (tableRule f134 hq134
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 + Finsupp.single 2 1) 1) = 1 := by
    rw [tableRule_apply, e, e, e]; decide
  have c2 : (tableRule f6 hq6
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 + Finsupp.single 2 1) 1) = 0 := by
    rw [tableRule_apply, e, e, e]; decide
  exact ⟨c1, c2, by rw [c1, c2]; decide⟩

/-! ## Table `74` -/

/-- **Table `74`**, `f a b c = if a = 1 then b * (1 + c) else c`. The Wolfram number `74` sets the
bits `4 a + 2 b + c` listed in `f74_values`: the triples `001`, `011` and `110`. -/
def f74 (a b c : ZMod 2) : ZMod 2 := if a = 1 then b * (1 + c) else c

/-- Quiescence of `f74`. -/
theorem hq74 : f74 0 0 0 = 0 := by decide

/-- The eight values of `f74` in the order `000, 001, 010, 011, 100, 101, 110, 111`, which is
bit `4 a + 2 b + c` of the Wolfram number `74`. -/
theorem f74_values :
    f74 0 0 0 = 0 ∧ f74 0 0 1 = 1 ∧ f74 0 1 0 = 0 ∧
      f74 0 1 1 = 1 ∧ f74 1 0 0 = 0 ∧ f74 1 0 1 = 0 ∧
      f74 1 1 0 = 1 ∧ f74 1 1 1 = 0 := by decide

/-- The rule at a cell, with the three neighbouring positions given by equations. -/
private theorem tableRule_apply_at (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (x : ℤ →₀ ZMod 2) (j a c : ℤ) (ha : a = j - 1) (hc : c = j + 1) :
    tableRule f hq x j = f (x a) (x j) (x c) := by
  subst ha hc
  exact tableRule_apply f hq x j

/-- The long starts at or beyond `q`: set cells with a clear left neighbour and a set right
neighbour. -/
private def longFrom (x : ℤ →₀ ZMod 2) (q : ℤ) : ℕ :=
  (x.support.filter (fun i => q ≤ i ∧ x (i - 1) = 0 ∧ x (i + 1) = 1)).card

/-- The states with no four set cells in a row. -/
private def NoFour (x : ℤ →₀ ZMod 2) : Prop :=
  ∀ i, ¬ (x i = 1 ∧ x (i + 1) = 1 ∧ x (i + 2) = 1 ∧ x (i + 3) = 1)

/-- The states where a clear, set, clear, set, set, clear pattern is preceded by two set cells
at distances four and five. -/
private def Behind (x : ℤ →₀ ZMod 2) : Prop :=
  ∀ i, x (i - 3) = 0 → x (i - 2) = 1 → x (i - 1) = 0 → x i = 1 → x (i + 1) = 1 → x (i + 2) = 0 →
    x (i - 4) = 1 ∧ x (i - 5) = 1

/-- No image of `f74` has four set cells in a row: a six-cell statement. -/
private theorem f74_no_four : ∀ a0 a1 a2 a3 a4 a5 : ZMod 2,
    f74 a0 a1 a2 = 1 → f74 a1 a2 a3 = 1 → f74 a2 a3 a4 = 1 → f74 a3 a4 a5 = 1 → False := by
  decide

private theorem noFour_tableRule (x : ℤ →₀ ZMod 2) : NoFour (tableRule f74 hq74 x) := by
  intro i ⟨h0, h1, h2, h3⟩
  rw [tableRule_apply_at f74 hq74 x i (i - 1) (i + 1) rfl rfl] at h0
  rw [tableRule_apply_at f74 hq74 x (i + 1) i (i + 2) (by ring) (by ring)] at h1
  rw [tableRule_apply_at f74 hq74 x (i + 2) (i + 1) (i + 3) (by ring) (by ring)] at h2
  rw [tableRule_apply_at f74 hq74 x (i + 3) (i + 2) (i + 4) (by ring) (by ring)] at h3
  exact f74_no_four _ _ _ _ _ _ h0 h1 h2 h3

/-- A cell set after a step has itself or its right neighbour set. -/
private theorem f74_self_or_right : ∀ a b c : ZMod 2, f74 a b c = 1 → b = 1 ∨ c = 1 := by decide

/-- A set cell of an image: the right neighbour is set, or the cell and its left neighbour are
set and the right neighbour is clear. -/
private theorem f74_right_or_pair : ∀ a b c : ZMod 2, f74 a b c = 1 →
    c = 1 ∨ (a = 1 ∧ b = 1 ∧ c = 0) := by decide

set_option synthInstance.maxSize 1000 in
/-- A long start of an image of `f74`, from the five cells around it: the start was held (the
cell was a long start, a block of two, with a set cell two places to its left) or moved (the cell
to its right is a long start). -/
private theorem f74_long : ∀ a0 a1 a2 a3 a4 : ZMod 2,
    f74 a0 a1 a2 = 0 → f74 a1 a2 a3 = 1 → f74 a2 a3 a4 = 1 →
      (a1 = 0 ∧ a2 = 1 ∧ a3 = 1 ∧ a0 = 1 ∧ a4 = 0) ∨ (a2 = 0 ∧ a3 = 1 ∧ a4 = 1) := by decide

/-- The image of a state is read off from seven cells after three steps. -/
private def Y2 (a0 a1 a2 a3 a4 : ZMod 2) : ZMod 2 :=
  f74 (f74 a0 a1 a2) (f74 a1 a2 a3) (f74 a2 a3 a4)

private def Y3 (a0 a1 a2 a3 a4 a5 a6 : ZMod 2) : ZMod 2 :=
  f74 (Y2 a0 a1 a2 a3 a4) (Y2 a1 a2 a3 a4 a5) (Y2 a2 a3 a4 a5 a6)

private theorem iter2_apply (w : ℤ →₀ ZMod 2) (p : ℤ) :
    ((tableRule f74 hq74)^[2] w) p =
      Y2 (w (p - 2)) (w (p - 1)) (w p) (w (p + 1)) (w (p + 2)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    tableRule_apply, Y2]
  ring_nf

private theorem iter3_apply (w : ℤ →₀ ZMod 2) (p : ℤ) :
    ((tableRule f74 hq74)^[3] w) p =
      Y3 (w (p - 3)) (w (p - 2)) (w (p - 1)) (w p) (w (p + 1)) (w (p + 2)) (w (p + 3)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    tableRule_apply, Y3, Y2]
  ring_nf

set_option maxRecDepth 100000 in
/-- **The set after three steps** (the kernel decision over fourteen cells): a window of
fourteen cells of a state, whose image after three steps has the clear, set, clear, set, set,
clear pattern, has set cells four and five places before that pattern's last set cell. -/
private theorem f74_behind_decide : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : ZMod 2,
    Y3 a2 a3 a4 a5 a6 a7 a8 = 0 → Y3 a3 a4 a5 a6 a7 a8 a9 = 1 → Y3 a4 a5 a6 a7 a8 a9 a10 = 0 →
    Y3 a5 a6 a7 a8 a9 a10 a11 = 1 → Y3 a6 a7 a8 a9 a10 a11 a12 = 1 →
    Y3 a7 a8 a9 a10 a11 a12 a13 = 0 →
    Y3 a1 a2 a3 a4 a5 a6 a7 = 1 ∧ Y3 a0 a1 a2 a3 a4 a5 a6 = 1 := by
  decide +kernel

/-- Every image from the third on is behind itself in this sense. -/
private theorem behind_iter3 (w : ℤ →₀ ZMod 2) : Behind ((tableRule f74 hq74)^[3] w) := by
  intro i h1 h2 h3 h4 h5 h6
  rw [iter3_apply] at h1 h2 h3 h4 h5 h6
  rw [iter3_apply, iter3_apply]
  ring_nf at h1 h2 h3 h4 h5 h6 ⊢
  exact f74_behind_decide (w (-8 + i)) (w (-7 + i)) (w (-6 + i)) (w (-5 + i)) (w (-4 + i))
    (w (-3 + i)) (w (-2 + i)) (w (-1 + i)) (w i) (w (1 + i)) (w (2 + i)) (w (3 + i))
    (w (4 + i)) (w (5 + i)) h1 h2 h3 h4 h5 h6

/-- **One step of `f74`**: the long starts at or beyond `q - 1` after a step number at most the
long starts at or beyond `q` before it, plus one when the cells `q - 3` to `q + 1` read set,
clear, set, set, clear. -/
private theorem longFrom_step_le (x : ℤ →₀ ZMod 2) (q : ℤ) :
    longFrom (tableRule f74 hq74 x) (q - 1) ≤ longFrom x q +
      (if x (q - 3) = 1 ∧ x (q - 2) = 0 ∧ x (q - 1) = 1 ∧ x q = 1 ∧ x (q + 1) = 0
        then 1 else 0) := by
  classical
  have key : ∀ i, tableRule f74 hq74 x (i - 1) = 0 → tableRule f74 hq74 x i = 1 →
      tableRule f74 hq74 x (i + 1) = 1 →
      (x (i - 1) = 0 ∧ x i = 1 ∧ x (i + 1) = 1 ∧ x (i - 2) = 1 ∧ x (i + 2) = 0) ∨
      (x i = 0 ∧ x (i + 1) = 1 ∧ x (i + 2) = 1) := by
    intro i h0 h1 h2
    rw [tableRule_apply_at f74 hq74 x (i - 1) (i - 2) i (by ring) (by ring)] at h0
    rw [tableRule_apply_at f74 hq74 x i (i - 1) (i + 1) rfl rfl] at h1
    rw [tableRule_apply_at f74 hq74 x (i + 1) i (i + 2) (by ring) (by ring)] at h2
    exact f74_long _ _ _ _ _ h0 h1 h2
  let g : ℤ → ℤ := fun i => if x i = 1 then i else i + 1
  let T : Finset ℤ := x.support.filter (fun i => q ≤ i ∧ x (i - 1) = 0 ∧ x (i + 1) = 1) ∪
    (if x (q - 3) = 1 ∧ x (q - 2) = 0 ∧ x (q - 1) = 1 ∧ x q = 1 ∧ x (q + 1) = 0
      then {q - 1} else ∅)
  have hcard : longFrom (tableRule f74 hq74 x) (q - 1) ≤ T.card := by
    unfold longFrom
    apply Finset.card_le_card_of_injOn g
    · intro i hi
      obtain ⟨hi1, hi2, hi3, hi4⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      have hz1 : tableRule f74 hq74 x i = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi1)
      simp only [T, Finset.mem_coe, Finset.mem_union, Finset.mem_filter]
      rcases key i hi3 hz1 hi4 with ⟨k1, k2, k3, k4, k5⟩ | ⟨k1, k2, k3⟩
      · have hgi : g i = i := by simp [g, k2]
        rw [hgi]
        by_cases hiq : q ≤ i
        · exact Or.inl ⟨mem_support_of_eq_one k2, hiq, k1, k3⟩
        · have e : i = q - 1 := by omega
          right
          have e3 : q - 3 = i - 2 := by omega
          have e2 : q - 2 = i - 1 := by omega
          have e1 : q - 1 = i := by omega
          have e0 : q = i + 1 := by omega
          have e' : q + 1 = i + 2 := by omega
          have hcond : x (q - 3) = 1 ∧ x (q - 2) = 0 ∧ x (q - 1) = 1 ∧ x q = 1 ∧
              x (q + 1) = 0 :=
            ⟨(congrArg x e3).trans k4, (congrArg x e2).trans k1, (congrArg x e1).trans k2,
              (congrArg x e0).trans k3, (congrArg x e').trans k5⟩
          simp [hcond, e]
      · have hxi : ¬ x i = 1 := by rw [k1]; decide
        have hgi : g i = i + 1 := by simp [g, hxi]
        rw [hgi]
        refine Or.inl ⟨mem_support_of_eq_one k2, by omega, ?_, ?_⟩
        · rw [show i + 1 - 1 = i by ring]; exact k1
        · rw [show i + 1 + 1 = i + 2 by ring]; exact k3
    · intro i hi j hj hij
      replace hi := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      replace hj := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
      have hzi : tableRule f74 hq74 x i = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi.1)
      have hzj : tableRule f74 hq74 x j = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hj.1)
      by_cases hxi : x i = 1 <;> by_cases hxj : x j = 1
      · simpa [g, hxi, hxj] using hij
      · have hgi : g i = i := by simp [g, hxi]
        have hgj : g j = j + 1 := by simp [g, hxj]
        have hji : i = j + 1 := by simp only [hgi, hgj] at hij; exact hij
        have h3 := hi.2.2.1
        rw [hji, show j + 1 - 1 = j by ring, hzj] at h3
        exact absurd h3 (by decide)
      · have hgi : g i = i + 1 := by simp [g, hxi]
        have hgj : g j = j := by simp [g, hxj]
        have hji : i + 1 = j := by simp only [hgi, hgj] at hij; exact hij
        have h3 := hj.2.2.1
        rw [← hji, show i + 1 - 1 = i by ring, hzi] at h3
        exact absurd h3 (by decide)
      · simpa [g, hxi, hxj] using hij
  refine hcard.trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  unfold longFrom
  split_ifs <;> simp

/-- **The pattern costs two further long starts to its left**, where no four cells in a row are
set and the state is behind itself: the cell `q - 1` is a long start, and the block ending at
`q - 3` or at `q - 5` has a long start at or beyond `q - 7`. -/
private theorem longFrom_pattern_le {x : ℤ →₀ ZMod 2} (hF : NoFour x) (hB : Behind x) (q : ℤ)
    (h3 : x (q - 3) = 1) (h2 : x (q - 2) = 0) (h1 : x (q - 1) = 1) (h0 : x q = 1)
    (h' : x (q + 1) = 0) :
    longFrom x q + 2 ≤ longFrom x (q - 7) := by
  classical
  obtain ⟨p, hp1, hp2, hp3, hp4, hp5, hp6⟩ :
      ∃ p : ℤ, p ≠ q - 1 ∧ p < q ∧ q - 7 ≤ p ∧ x p = 1 ∧ x (p - 1) = 0 ∧ x (p + 1) = 1 := by
    by_cases h4 : x (q - 4) = 1
    · by_cases h5 : x (q - 5) = 1
      · have h6 : x (q - 6) = 0 := by
          by_contra hne
          have := hF (q - 6)
          rw [show q - 6 + 1 = q - 5 by ring, show q - 6 + 2 = q - 4 by ring,
            show q - 6 + 3 = q - 3 by ring] at this
          exact this ⟨zmod2_one_of_ne_zero _ hne, h5, h4, h3⟩
        refine ⟨q - 5, by omega, by omega, by omega, h5, ?_, ?_⟩
        · rw [show q - 5 - 1 = q - 6 by ring]; exact h6
        · rw [show q - 5 + 1 = q - 4 by ring]; exact h4
      · refine ⟨q - 4, by omega, by omega, by omega, h4, ?_, ?_⟩
        · rw [show q - 4 - 1 = q - 5 by ring]; exact zmod2_eq_zero_of_ne_one _ h5
        · rw [show q - 4 + 1 = q - 3 by ring]; exact h3
    · have h4' : x (q - 4) = 0 := zmod2_eq_zero_of_ne_one _ h4
      have hc := hB (q - 1) (by rw [show q - 1 - 3 = q - 4 by ring]; exact h4')
        (by rw [show q - 1 - 2 = q - 3 by ring]; exact h3)
        (by rw [show q - 1 - 1 = q - 2 by ring]; exact h2) h1
        (by rw [show q - 1 + 1 = q by ring]; exact h0)
        (by rw [show q - 1 + 2 = q + 1 by ring]; exact h')
      rw [show q - 1 - 4 = q - 5 by ring, show q - 1 - 5 = q - 6 by ring] at hc
      obtain ⟨c5, c6⟩ := hc
      by_cases h7 : x (q - 7) = 1
      · have h8 : x (q - 8) = 0 := by
          by_contra hne
          have := hF (q - 8)
          rw [show q - 8 + 1 = q - 7 by ring, show q - 8 + 2 = q - 6 by ring,
            show q - 8 + 3 = q - 5 by ring] at this
          exact this ⟨zmod2_one_of_ne_zero _ hne, h7, c6, c5⟩
        refine ⟨q - 7, by omega, by omega, by omega, h7, ?_, ?_⟩
        · rw [show q - 7 - 1 = q - 8 by ring]; exact h8
        · rw [show q - 7 + 1 = q - 6 by ring]; exact c6
      · refine ⟨q - 6, by omega, by omega, by omega, c6, ?_, ?_⟩
        · rw [show q - 6 - 1 = q - 7 by ring]; exact zmod2_eq_zero_of_ne_one _ h7
        · rw [show q - 6 + 1 = q - 5 by ring]; exact c5
  have hsub : insert (q - 1) (insert p (x.support.filter
      (fun i => q ≤ i ∧ x (i - 1) = 0 ∧ x (i + 1) = 1))) ⊆
      x.support.filter (fun i => q - 7 ≤ i ∧ x (i - 1) = 0 ∧ x (i + 1) = 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_filter] at hi ⊢
    rcases hi with rfl | rfl | ⟨hs, hq, hz⟩
    · refine ⟨mem_support_of_eq_one h1, by omega, ?_, ?_⟩
      · rw [show q - 1 - 1 = q - 2 by ring]; exact h2
      · rw [show q - 1 + 1 = q by ring]; exact h0
    · exact ⟨mem_support_of_eq_one hp4, hp3, hp5, hp6⟩
    · exact ⟨hs, by omega, hz⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] at hc
  · unfold longFrom
    omega
  · simp only [Finset.mem_filter]
    omega
  · simp only [Finset.mem_insert, Finset.mem_filter]
    omega

/-- A step moves the support at most one cell to the left and not to the right. -/
private theorem bounds_step {x : ℤ →₀ ZMod 2} {m M : ℤ}
    (h : ∀ i, x i = 1 → m ≤ i ∧ i ≤ M) :
    ∀ i, tableRule f74 hq74 x i = 1 → m - 1 ≤ i ∧ i ≤ M := by
  intro i hi
  rw [tableRule_apply] at hi
  rcases f74_self_or_right _ _ _ hi with hb | hc
  · have := h i hb
    omega
  · have := h (i + 1) hc
    omega

private theorem bounds_iter {s : ℤ →₀ ZMod 2} {m M : ℤ}
    (h : ∀ i, s i = 1 → m ≤ i ∧ i ≤ M) (k : ℕ) :
    ∀ i, (tableRule f74 hq74)^[k] s i = 1 → m - k ≤ i ∧ i ≤ M := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    intro i hi
    rw [Function.iterate_succ_apply'] at hi
    have := bounds_step ih i hi
    push_cast
    omega

/-- **The diameter from the third image on**, for a state with its set cells in `[m, M]`: the
long-start count of the images numbers at most a linear function of the position, so the last set
cell recedes by one a step beyond `max M (K - 4)`. -/
private theorem diam_iterate_three_add_le_f74 {s : ℤ →₀ ZMod 2} {m M : ℤ}
    (h : ∀ i, s i = 1 → m ≤ i ∧ i ≤ M) (hmM : m ≤ M) (j : ℕ) :
    diam ((tableRule f74 hq74)^[3 + j] s) ≤
      (max M (M + 7 * (M - m + 3) - 4) - m + 3).toNat + 1 := by
  classical
  have hF : ∀ j : ℕ, NoFour ((tableRule f74 hq74)^[3 + j] s) := fun j => by
    rw [show 3 + j = (2 + j) + 1 by omega, Function.iterate_succ_apply']
    exact noFour_tableRule _
  have hB : ∀ j : ℕ, Behind ((tableRule f74 hq74)^[3 + j] s) := fun j => by
    rw [Function.iterate_add_apply]
    exact behind_iter3 _
  have hsucc : ∀ j : ℕ, (tableRule f74 hq74)^[3 + (j + 1)] s =
      tableRule f74 hq74 ((tableRule f74 hq74)^[3 + j] s) := fun j => by
    rw [show 3 + (j + 1) = (3 + j) + 1 from rfl, Function.iterate_succ_apply']
  have hstep : ∀ (j : ℕ) (q : ℤ),
      longFrom ((tableRule f74 hq74)^[3 + (j + 1)] s) (q - 1) ≤
        longFrom ((tableRule f74 hq74)^[3 + j] s) q + 1 := by
    intro j q
    rw [hsucc]
    refine (longFrom_step_le _ q).trans ?_
    split_ifs <;> omega
  have hhold : ∀ (j : ℕ) (q : ℤ),
      ¬ (((tableRule f74 hq74)^[3 + j] s) (q - 3) = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q - 2) = 0 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q - 1) = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) q = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q + 1) = 0) →
      longFrom ((tableRule f74 hq74)^[3 + (j + 1)] s) (q - 1) ≤
        longFrom ((tableRule f74 hq74)^[3 + j] s) q := by
    intro j q hc
    rw [hsucc]
    refine (longFrom_step_le _ q).trans ?_
    simp [hc]
  have hP : ∀ (j : ℕ) (q : ℤ),
      (((tableRule f74 hq74)^[3 + j] s) (q - 3) = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q - 2) = 0 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q - 1) = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) q = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q + 1) = 0) →
      longFrom ((tableRule f74 hq74)^[3 + j] s) q + 2 ≤
        longFrom ((tableRule f74 hq74)^[3 + j] s) (q - ((7 : ℕ) : ℤ)) := by
    intro j q ⟨c3, c2, c1, c0, c'⟩
    have := longFrom_pattern_le (hF j) (hB j) q c3 c2 c1 c0 c'
    push_cast
    exact this
  have hbase : ∀ q : ℤ, 7 * longFrom ((tableRule f74 hq74)^[3 + 0] s) q ≤
      (M + 7 * (M - m + 3) - q).toNat := by
    intro q
    have hb := bounds_iter h (3 + 0)
    have hsub : ((tableRule f74 hq74)^[3 + 0] s).support.filter (fun i => q ≤ i ∧
        ((tableRule f74 hq74)^[3 + 0] s) (i - 1) = 0 ∧
        ((tableRule f74 hq74)^[3 + 0] s) (i + 1) = 1) ⊆ Finset.Icc (max q (m - 3)) (M - 1) := by
      intro i hi
      obtain ⟨hi1, hi2, _, hi4⟩ := Finset.mem_filter.mp hi
      have hz : ((tableRule f74 hq74)^[3 + 0] s) i = 1 :=
        zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi1)
      have b1 := hb i hz
      have b2 := hb (i + 1) hi4
      rw [Finset.mem_Icc]
      push_cast at b1 b2
      exact ⟨max_le hi2 (by omega), by omega⟩
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    unfold longFrom
    omega
  have inv := count_invariant_of_step
    (N := fun j q => longFrom ((tableRule f74 hq74)^[3 + j] s) q)
    (P := fun j q => ((tableRule f74 hq74)^[3 + j] s) (q - 3) = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q - 2) = 0 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q - 1) = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) q = 1 ∧
        ((tableRule f74 hq74)^[3 + j] s) (q + 1) = 0) 7 (M + 7 * (M - m + 3))
    hstep hhold hP hbase
  -- the last set cell
  have hR : ∀ j : ℕ, ∀ i : ℤ, ((tableRule f74 hq74)^[3 + j] s) i = 1 →
      i ≤ max M (M + 7 * (M - m + 3) - 4) - j := by
    intro j
    induction j with
    | zero =>
      intro i hi
      have := (bounds_iter h (3 + 0) i hi).2
      push_cast
      omega
    | succ j ih =>
      intro i hi
      rw [hsucc, tableRule_apply] at hi
      rcases f74_right_or_pair _ _ _ hi with hc | ⟨ha, hb, hc⟩
      · have := ih (i + 1) hc
        push_cast
        omega
      · obtain ⟨p, hp1, hp2, hp3, hp4⟩ : ∃ p : ℤ, i - 2 ≤ p ∧
            ((tableRule f74 hq74)^[3 + j] s) p = 1 ∧
            ((tableRule f74 hq74)^[3 + j] s) (p - 1) = 0 ∧
            ((tableRule f74 hq74)^[3 + j] s) (p + 1) = 1 := by
          by_cases h2 : ((tableRule f74 hq74)^[3 + j] s) (i - 2) = 1
          · have h3 : ((tableRule f74 hq74)^[3 + j] s) (i - 3) = 0 := by
              by_contra hne
              have := hF j (i - 3)
              rw [show i - 3 + 1 = i - 2 by ring, show i - 3 + 2 = i - 1 by ring,
                show i - 3 + 3 = i by ring] at this
              exact this ⟨zmod2_one_of_ne_zero _ hne, h2, ha, hb⟩
            refine ⟨i - 2, le_rfl, h2, ?_, ?_⟩
            · rw [show i - 2 - 1 = i - 3 by ring]; exact h3
            · rw [show i - 2 + 1 = i - 1 by ring]; exact ha
          · refine ⟨i - 1, by omega, ha, ?_, ?_⟩
            · rw [show i - 1 - 1 = i - 2 by ring]; exact zmod2_eq_zero_of_ne_one _ h2
            · rw [show i - 1 + 1 = i by ring]; exact hb
        have hpos : 1 ≤ longFrom ((tableRule f74 hq74)^[3 + j] s) p := by
          unfold longFrom
          exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr
            ⟨mem_support_of_eq_one hp2, le_rfl, hp3, hp4⟩⟩
        have hi' := inv j (p + j)
        beta_reduce at hi'
        rw [add_sub_cancel_right] at hi'
        push_cast
        omega
  have hsupp : ∀ i ∈ ((tableRule f74 hq74)^[3 + j] s).support,
      m - (3 + j : ℕ) ≤ i ∧ i ≤ max M (M + 7 * (M - m + 3) - 4) - j := by
    intro i hi
    have hz : ((tableRule f74 hq74)^[3 + j] s) i = 1 :=
      zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi)
    exact ⟨(bounds_iter h (3 + j) i hz).1, hR j i hz⟩
  have := diam_le_of_support_subset hsupp (by push_cast; omega)
  push_cast at this
  omega

/-- **Table `74` does not accrete: a count of long starts bounds every orbit's diameter.** Every
orbit's diameter at `f74` is at most eight times its start's plus nineteen. A long start is a set
cell with a clear left neighbour and a set right neighbour. No image has four set cells in a row;
the long starts at or beyond a cell `q - 1` of an image number at most the long starts at or
beyond `q` of the state, plus one when the cells `q - 3` to `q + 1` read set, clear, set, set,
clear; and from the third image on that pattern costs two further long starts within seven
cells to its left. The count bounds the long starts of every image from the third on by a
linear function of the position, and the last set cell recedes by one a step beyond it. -/
theorem diam_iterate_le_f74 (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule f74 hq74)^[k] s) ≤ 8 * diam s + 19 := by
  by_cases hs : s = 0
  · subst hs
    rw [Function.iterate_fixed (tableRule_zero' f74 hq74), diam_zero']
    omega
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hmm := Finset.min'_le_max' s.support hne
    have hd := diam_eq' hne
    have h : ∀ i, s i = 1 → s.support.min' hne ≤ i ∧ i ≤ s.support.max' hne := fun i hi =>
      ⟨Finset.min'_le _ _ (mem_support_of_eq_one hi), Finset.le_max' _ _ (mem_support_of_eq_one hi)⟩
    by_cases hk : k < 3
    · have hsupp : ∀ i ∈ ((tableRule f74 hq74)^[k] s).support,
          s.support.min' hne - k ≤ i ∧ i ≤ s.support.max' hne := fun i hi =>
        bounds_iter h k i (zmod2_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi))
      have := diam_le_of_support_subset hsupp (by omega)
      omega
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ k by omega)
      have := diam_iterate_three_add_le_f74 h hmm j
      omega

/-- **The bound passes to the mirror of table `74`**, by reflection. -/
theorem diam_iterate_le_mirror_f74 (s : ℤ →₀ ZMod 2) (k : ℕ) :
    diam ((tableRule (mirrorTable f74) hq74)^[k] s) ≤ 8 * diam s + 19 := by
  have h1 := diam_iterate_le_f74 (reflect s) k
  rw [diam_reflect] at h1
  have e : (tableRule (mirrorTable f74) hq74)^[k] s =
      reflect ((tableRule f74 hq74)^[k] (reflect s)) := by
    conv_lhs => rw [← reflect_reflect s]
    exact iterate_mirror_reflect f74 hq74 (reflect s) k
  rw [e, diam_reflect]
  exact h1

/-- **Identically zero growing width at `f74`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_f74 (n t : ℕ) :
    growingWidth (tableRule f74 hq74) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_affine
    (fun s k => diam_iterate_le_f74 s k) n t

/-- **Identically zero growing width at `mirrorTable f74`** ([RuleSpace] §3 Proposition 3.7). -/
theorem growingWidth_lightCone_eq_zero_mirror_f74 (n t : ℕ) :
    growingWidth (tableRule (mirrorTable f74) hq74) diam (lightCone n) t = 0 :=
  growingWidth_lightCone_eq_zero_of_diam_le_affine
    (fun s k => diam_iterate_le_mirror_f74 s k) n t

set_option maxRecDepth 8000 in
/-- **Table `74` and its mirror are in neither endpoint class**: `f74` and `mirrorTable f74`
lie in neither `AccretesByEndpoints` nor `ZeroByEndpoints`. -/
theorem not_mem_endpoint_classes_f74 :
    ∀ f ∈ ([f74, mirrorTable f74] : List (ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)),
      ¬ EndpointClasses.AccretesByEndpoints f ∧ ¬ EndpointClasses.ZeroByEndpoints f := by
  decide

/-- **Table `74` is outside the left-clear class**: it sets a clear cell with a clear left
neighbour and a set right neighbour, and it sets a cell whose left neighbour is set
(`f74 1 1 0 = 1`), so the shape hypothesis of `diam_iterate_le_of_leftClear` fails. -/
theorem f74_not_leftClear :
    f74 0 0 1 = 1 ∧ f74 1 1 0 = 1 ∧
      ¬ (∀ a b c, f74 a b c = 1 → a = 0 ∧ (b = 1 ∨ c = 1)) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := (h 1 1 0 (by decide)).1
  exact absurd this (by decide)

/-- **The third image is needed for the pattern at table `74`**: at the state set on exactly the
cells `0`, `1`, `4`, `5`, `7` and `8`, the second image reads clear, set, clear, set, set, clear
at the cells `4` to `9`, and its cell `2` is clear, so the set cells five places before the last
set cell of the pattern, which every image from the third on has, are not yet there. -/
theorem three_steps_needed_f74 :
    let y := (tableRule f74 hq74)^[2]
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 + Finsupp.single 4 1 +
        Finsupp.single 5 1 + Finsupp.single 7 1 + Finsupp.single 8 1)
    y (7 - 3) = 0 ∧ y (7 - 2) = 1 ∧ y (7 - 1) = 0 ∧ y 7 = 1 ∧ y (7 + 1) = 1 ∧ y (7 + 2) = 0 ∧
      y (7 - 5) = 0 := by
  intro y
  have e : ∀ x : ℤ, (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 +
      Finsupp.single 4 1 + Finsupp.single 5 1 + Finsupp.single 7 1 + Finsupp.single 8 1 :
      ℤ →₀ ZMod 2) x =
      if x = 0 ∨ x = 1 ∨ x = 4 ∨ x = 5 ∨ x = 7 ∨ x = 8 then 1 else 0 := by
    intro x
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    by_cases h0 : x = 0
    · subst h0; decide
    · by_cases h1 : x = 1
      · subst h1; decide
      · by_cases h4 : x = 4
        · subst h4; decide
        · by_cases h5 : x = 5
          · subst h5; decide
          · by_cases h7 : x = 7
            · subst h7; decide
            · by_cases h8 : x = 8
              · subst h8; decide
              · simp [Ne.symm h0, Ne.symm h1, Ne.symm h4, Ne.symm h5, Ne.symm h7, Ne.symm h8,
                  h0, h1, h4, h5, h7, h8]
  simp only [y]
  rw [iter2_apply, iter2_apply, iter2_apply, iter2_apply, iter2_apply, iter2_apply, iter2_apply]
  simp only [e, Y2]
  decide

/-! ## The ten middle tables -/

/-- **The ten middle tables** ([RuleSpace] §3 Proposition 3.7). For every
window width `n` and every stage `t`, the growing width along the light cone is zero at `f6`,
`f14`, `f74`, `f134`, `f142` and at their five mirrors. -/
theorem growingWidth_lightCone_middle_ten (n t : ℕ) :
    growingWidth (tableRule f6 hq6) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule f14 hq14) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule f74 hq74) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule f134 hq134) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule f142 hq142) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f6) hq6) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f14) hq14) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f74) hq74) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f134) hq134) diam (lightCone n) t = 0 ∧
    growingWidth (tableRule (mirrorTable f142) hq142) diam (lightCone n) t = 0 :=
  ⟨growingWidth_lightCone_eq_zero_f6 n t, growingWidth_lightCone_eq_zero_f14 n t,
    growingWidth_lightCone_eq_zero_f74 n t, growingWidth_lightCone_eq_zero_f134 n t,
    growingWidth_lightCone_eq_zero_f142 n t, growingWidth_lightCone_eq_zero_mirror_f6 n t,
    growingWidth_lightCone_eq_zero_mirror_f14 n t, growingWidth_lightCone_eq_zero_mirror_f74 n t,
    growingWidth_lightCone_eq_zero_mirror_f134 n t,
    growingWidth_lightCone_eq_zero_mirror_f142 n t⟩

/-- **None of the ten middle tables is in either endpoint class**: `f6`, `f14`, `f74`, `f134`,
`f142` and their mirrors lie in neither `AccretesByEndpoints` nor `ZeroByEndpoints`. -/
theorem not_mem_endpoint_classes_middle_ten :
    ∀ f ∈ ([f6, f14, f74, f134, f142, mirrorTable f6, mirrorTable f14, mirrorTable f74,
        mirrorTable f134, mirrorTable f142] : List (ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)),
      ¬ EndpointClasses.AccretesByEndpoints f ∧ ¬ EndpointClasses.ZeroByEndpoints f := by
  intro f hf
  have h4 := not_mem_endpoint_classes_leftClear_four
  have h142 := not_mem_endpoint_classes_f142
  have h134 := not_mem_endpoint_classes_f134
  have h74 := not_mem_endpoint_classes_f74
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf h4 h142 h134 h74
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h4 _ (Or.inr (Or.inl rfl))
  · exact h4 _ (Or.inl rfl)
  · exact h74 _ (Or.inl rfl)
  · exact h134 _ (Or.inl rfl)
  · exact h142 _ (Or.inl rfl)
  · exact h4 _ (Or.inr (Or.inr (Or.inr rfl)))
  · exact h4 _ (Or.inr (Or.inr (Or.inl rfl)))
  · exact h74 _ (Or.inr rfl)
  · exact h134 _ (Or.inr rfl)
  · exact h142 _ (Or.inr rfl)

end BlockTrainWidth

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard axioms, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'BlockTrainWidth.count_invariant_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.count_invariant_of_step

/-- info: 'BlockTrainWidth.diam_iterate_le_of_leftClear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_of_leftClear

/-- info: 'BlockTrainWidth.diam_iterate_le_of_leftClear_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_of_leftClear_mirror

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_of_diam_le_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_of_diam_le_affine

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_of_leftClear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_of_leftClear

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_of_leftClear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_of_leftClear

/-- info: 'BlockTrainWidth.hq14' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.hq14

/-- info: 'BlockTrainWidth.f14_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f14_values

/-- info: 'BlockTrainWidth.f14_leftClear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f14_leftClear

/-- info: 'BlockTrainWidth.f14_tap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f14_tap

/-- info: 'BlockTrainWidth.hq6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.hq6

/-- info: 'BlockTrainWidth.f6_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f6_values

/-- info: 'BlockTrainWidth.f6_leftClear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f6_leftClear

/-- info: 'BlockTrainWidth.f6_tap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f6_tap

/-- info: 'BlockTrainWidth.not_mem_endpoint_classes_leftClear_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.not_mem_endpoint_classes_leftClear_four

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_f14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_f14

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f14

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_f6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_f6

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f6

/-- info: 'BlockTrainWidth.growingWidth_lightCone_leftClear_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_leftClear_four

/-- info: 'BlockTrainWidth.diam_iterate_le_of_leftClear_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_of_leftClear_nonvacuous

/-- info: 'BlockTrainWidth.leftClear_hypothesis_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.leftClear_hypothesis_load_bearing

/-- info: 'BlockTrainWidth.diam_iterate_five_alternating_f14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_five_alternating_f14

/-- info: 'BlockTrainWidth.hq142' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.hq142

/-- info: 'BlockTrainWidth.f142_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f142_values

/-- info: 'BlockTrainWidth.diam_iterate_le_f142' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_f142

/-- info: 'BlockTrainWidth.diam_iterate_le_mirror_f142' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_mirror_f142

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_f142' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_f142

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f142' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f142

/-- info: 'BlockTrainWidth.not_mem_endpoint_classes_f142' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.not_mem_endpoint_classes_f142

/-- info: 'BlockTrainWidth.f142_not_leftClear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f142_not_leftClear

/-- info: 'BlockTrainWidth.endsFrom_pattern_gain_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.endsFrom_pattern_gain_one

/-- info: 'BlockTrainWidth.f134_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f134_values

/-- info: 'BlockTrainWidth.diam_iterate_le_f134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_f134

/-- info: 'BlockTrainWidth.diam_iterate_le_mirror_f134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_mirror_f134

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_f134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_f134

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f134

/-- info: 'BlockTrainWidth.not_mem_endpoint_classes_f134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.not_mem_endpoint_classes_f134

/-- info: 'BlockTrainWidth.f134_not_leftClear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f134_not_leftClear

/-- info: 'BlockTrainWidth.tableRule_f134_ne_f6_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.tableRule_f134_ne_f6_block

/-- info: 'BlockTrainWidth.hq74' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.hq74

/-- info: 'BlockTrainWidth.f74_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f74_values

/-- info: 'BlockTrainWidth.diam_iterate_le_f74' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_f74

/-- info: 'BlockTrainWidth.diam_iterate_le_mirror_f74' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.diam_iterate_le_mirror_f74

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_f74' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_f74

/-- info: 'BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f74' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_eq_zero_mirror_f74

/-- info: 'BlockTrainWidth.not_mem_endpoint_classes_f74' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.not_mem_endpoint_classes_f74

/-- info: 'BlockTrainWidth.f74_not_leftClear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.f74_not_leftClear

/-- info: 'BlockTrainWidth.three_steps_needed_f74' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.three_steps_needed_f74

/-- info: 'BlockTrainWidth.growingWidth_lightCone_middle_ten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.growingWidth_lightCone_middle_ten

/-- info: 'BlockTrainWidth.not_mem_endpoint_classes_middle_ten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockTrainWidth.not_mem_endpoint_classes_middle_ten
