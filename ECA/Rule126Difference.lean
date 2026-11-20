module

public import ECA.ParityEmulation
public import ECA.RationalRaySeeds
public import ECA.ReproductionBracket
public import ECA.Rule126Rays
public import ECA.StretchColumns
public import ErgodicTheory.DrivenColumns
import all ECA.Rule126Rays

/-!
# Rule `126` carried onto rule `18` by one step of rule `102`, and two columns of rule `18`
([RuleSpace] §4 Proposition 4.9, §5 Proposition 5.34)

The difference map `s ↦ (i ↦ s i + s (i + 1))` is one step of rule `102`, and it carries rule `126`
onto rule `18`: one step of rule `102` after one step of rule `126` is one step of rule `18` after
one step of rule `102`. The map is injective on finite configurations, since a difference of two
configurations that is constant along the line vanishes where both are zero.

The seeds `11` and `1001` read from cell `0` are the differences of the single seed at cell `1`
and of its first step of rule `126` at cell `2`. By the semiconjugacy the column of rule `18` at
cell `0` from either is the sum of two neighbouring cells of rule `126` from the single seed,
which `f126_single_two_mul` ([RuleSpace] §5 Proposition 5.34) reads from rule `90` at even steps
and a direct four-cell identity reads at odd steps. The cell `0` of rule `90` from the single
seed is zero past the first step, and its cell `1` is a one exactly at the steps one short of a
power of two, so each column reads `1` exactly one power of two short of a fixed number, and the
gaps between its ones grow without bound.

The seed `1111` is the difference of the seed `101` at the cells `1` and `3`, whose odd steps of
rule `126` are rule `90`'s rows from the seed `111` doubled toward the cell `2`. At the steps
`4 * u + 2` the column of rule `18` from `1111` reads the cells `-2` and `0` of rule `90` from the
single seed at the step `2 * u`, which is `1` exactly when `4 * u + 4` is a power of two, so the
column is not eventually periodic.

## Main results

* `semiconj_f102_f126_f18` — one step of rule `102` carries rule `126` onto rule `18`.
* `finRule_f102_injective` — one step of rule `102` is injective on finite configurations.
* `observedColumn_f18_eleven_eq_one_iff` — the column of rule `18` at cell `0` from the seed
  `11` reads `1` exactly at the steps `t` with `t + 2 = 2 ^ k`, `1 ≤ k`.
* `observedColumn_f18_one_zero_zero_one_eq_one_iff` — the same from the seed `1001`, exactly at
  `t + 4 = 2 ^ k`, `2 ≤ k`.
* `not_eventuallyPeriodic_observedColumn_f18_of_f126` — **the two columns are not eventually
  periodic.**
* `f126_one_zero_one_two_mul_add_one` — the odd rows of rule `126` from the seed `101` at the
  cells `1` and `3` are rule `90`'s rows from the seed `111` at the cells `-1, 0, 1`, doubled
  toward the cell `2` ([RuleSpace] §5 Proposition 5.34's doubling).
* `observedColumn_f18_one_one_one_one_four_mul_add_two_eq_one_iff` — the column of rule `18` at
  cell `0` from the seed `1111` reads `1` at the step `4 * u + 2` exactly when `4 * u + 4 = 2 ^ k`,
  `2 ≤ k`.
* `not_eventuallyPeriodic_observedColumn_f18_one_one_one_one` — **the column from the seed
  `1111` is not eventually periodic.**
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## The semiconjugacy -/

/-- **One step of rule `102` carries rule `126` onto rule `18`** ([RuleSpace] §4 Proposition 4.9):
the cell `i` of rule `102` after rule `126` and of rule `18` after rule `102` both read the four
cells `i - 1, …, i + 2`, and the identity is a check of the sixteen values of those cells. -/
theorem semiconj_f102_f126_f18 :
    Function.Semiconj (finRule f102 hq102) (finRule f126 hq126) (finRule f18 hq18) := by
  intro s
  ext i
  simp only [finRule_apply, f102, add_sub_cancel_right, sub_add_cancel]
  generalize s (i - 1) = a
  generalize s i = b
  generalize s (i + 1) = c
  generalize s (i + 1 + 1) = d
  revert a b c d
  decide

/-- **One step of rule `102` is injective on finite configurations**: two configurations with the
same image have a sum that is constant along the line, so it vanishes beyond the support of both
and therefore everywhere. -/
theorem finRule_f102_injective : Function.Injective (finRule f102 hq102) := by
  intro s s' h
  have hd : ∀ i, s i + s (i + 1) = s' i + s' (i + 1) := by
    intro i
    have := congrFun (congrArg (fun x : FiniteConfiguration => (x : ℤ → ZMod 2)) h) i
    simpa [finRule_apply, f102] using this
  have hc : ∀ i, s i + s' i = s (i + 1) + s' (i + 1) := by
    intro i
    have := hd i
    revert this
    generalize s i = a
    generalize s (i + 1) = b
    generalize s' i = c
    generalize s' (i + 1) = d
    revert a b c d
    decide
  have hk : ∀ (k : ℕ) (i : ℤ), s i + s' i = s (i + k) + s' (i + k) := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [ih i, hc (i + k)]
      simp only [Nat.cast_succ, ← add_assoc]
  obtain ⟨B, hB⟩ := (s.support ∪ s'.support).bddAbove
  ext i
  have hbig : B < i + (B - i).toNat + 1 := by omega
  have h1 : s (i + ((B - i).toNat + 1 : ℕ)) = 0 := by
    by_contra hne
    have := hB (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hne))
    push_cast at this
    omega
  have h2 : s' (i + ((B - i).toNat + 1 : ℕ)) = 0 := by
    by_contra hne
    have := hB (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hne))
    push_cast at this
    omega
  have := hk ((B - i).toNat + 1) i
  rw [h1, h2] at this
  revert this
  generalize s i = a
  generalize s' i = b
  revert a b
  decide


/-! ## The difference of an orbit -/

/-- a translated seed has the translated orbit, for any local rule -/
private theorem iterate_shift (f : LocalRule) (hq : f 0 0 0 = 0) (c : ℤ) (t : ℕ) :
    ∀ (s s' : FiniteConfiguration), (∀ x, s' x = s (x - c)) →
      ∀ x, ((finRule f hq)^[t] s') x = ((finRule f hq)^[t] s) (x - c) := by
  induction t with
  | zero => intro s s' h x; exact h x
  | succ t ih =>
    intro s s' h x
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine ih _ _ ?_ x
    intro y
    rw [finRule_apply, finRule_apply, h, h, h]
    congr 2 <;> ring

/-- the orbit of a difference under rule `18` is the difference of the orbit under rule `126` -/
private theorem iterate_f18_finRule_f102 (t : ℕ) (s : FiniteConfiguration) (i : ℤ) :
    ((finRule f18 hq18)^[t] (finRule f102 hq102 s)) i =
      ((finRule f126 hq126)^[t] s) i + ((finRule f126 hq126)^[t] s) (i + 1) := by
  have h := (semiconj_f102_f126_f18.iterate_right t) s
  rw [← h, finRule_apply]
  simp [f102]

private theorem listSeed_eleven : listSeed [1, 1] =
    finRule f102 hq102 (Finsupp.single (1 : ℤ) (1 : ZMod 2)) := by
  ext i
  simp only [listSeed, finRule_apply, f102]
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    List.getD_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    CharP.cast_eq_zero, Order.lt_two_iff, zero_le, getElem?_pos, List.getElem_cons_zero,
    Option.getD_some, Nat.cast_one, Std.le_refl, List.getElem_cons_succ, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_apply, right_eq_add]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem finRule_f126_single_two :
    finRule f126 hq126 (Finsupp.single (2 : ℤ) (1 : ZMod 2)) =
      Finsupp.single (1 : ℤ) 1 + Finsupp.single (2 : ℤ) 1 + Finsupp.single (3 : ℤ) 1 := by
  ext i
  simp only [finRule_apply, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem listSeed_one_zero_zero_one : listSeed [1, 0, 0, 1] =
    finRule f102 hq102 (finRule f126 hq126 (Finsupp.single (2 : ℤ) (1 : ZMod 2))) := by
  rw [finRule_f126_single_two]
  ext i
  simp only [listSeed, finRule_apply, f102]
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    List.getD_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    CharP.cast_eq_zero, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some,
    Nat.cast_one, Nat.one_lt_ofNat, List.getElem_cons_succ, Finsupp.single_zero, add_zero,
    Nat.cast_ofNat, Nat.reduceLT, Nat.lt_add_one, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply, right_eq_add]
  split_ifs <;> first | rfl | (exfalso; omega)


/-- the column from the seed `11` at cell `0` is the cells `-1` and `0` of rule `126` from the
single seed -/
private theorem observedColumn_eleven (t : ℕ) :
    observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1]) 0 t =
      ((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-1) +
        ((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 := by
  unfold observedColumn
  rw [listSeed_eleven]
  have h := iterate_f18_finRule_f102 t (Finsupp.single (1 : ℤ) (1 : ZMod 2)) 0
  have hs : ∀ x, (Finsupp.single (1 : ℤ) (1 : ZMod 2)) x =
      (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (x - 1) := by
    intro x
    simp only [Finsupp.single_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [h, iterate_shift f126 hq126 1 t _ _ hs 0, iterate_shift f126 hq126 1 t _ _ hs (0 + 1)]
  norm_num

/-- the column from the seed `1001` at cell `0` is the cells `-2` and `-1` of rule `126` from the
single seed, one step later -/
private theorem observedColumn_one_zero_zero_one (t : ℕ) :
    observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 0, 0, 1]) 0 t =
      ((finRule f126 hq126)^[t + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-2) +
        ((finRule f126 hq126)^[t + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-1) := by
  unfold observedColumn
  rw [listSeed_one_zero_zero_one]
  have h := iterate_f18_finRule_f102 t
    (finRule f126 hq126 (Finsupp.single (2 : ℤ) (1 : ZMod 2))) 0
  have hs : ∀ x, (Finsupp.single (2 : ℤ) (1 : ZMod 2)) x =
      (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (x - 2) := by
    intro x
    simp only [Finsupp.single_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [h, ← Function.iterate_succ_apply (finRule f126 hq126),
    iterate_shift f126 hq126 2 (t + 1) _ _ hs 0, iterate_shift f126 hq126 2 (t + 1) _ _ hs (0 + 1)]
  norm_num

/-! ## Rule `90` from the single seed -/

/-- the single seed of rule `90` reads `0` at the cell `0` at every positive step -/
private theorem f90_single_apply_zero_of_pos (u : ℕ) (hu : 0 < u) :
    ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 0 := by
  rcases Nat.even_or_odd' u with ⟨c, rfl | rfl⟩
  · have h := zeroOfShared c c (by rw [Nat.and_self]; omega)
    rw [show c + c = 2 * c by ring, sub_self] at h
    exact h
  · exact f90_single_apply_eq_zero_of_odd _ _ (by push_cast; omega)

/-- two successive integers share no binary digit only when the larger is a power of two -/
private theorem exists_two_pow_of_succ_and_eq_zero :
    ∀ m : ℕ, (m + 1) &&& m = 0 → ∃ j, m + 1 = 2 ^ j := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h
    rcases Nat.even_or_odd' m with ⟨d, rfl | rfl⟩
    · have hd : d = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        have := congrArg (fun z => z.testBit (j + 1)) h
        simp only [Nat.testBit_and, Nat.zero_testBit] at this
        have e1 : (2 * d + 1).testBit (j + 1) = d.testBit j := by
          rw [Nat.testBit_succ]; congr 1; omega
        have e2 : (2 * d).testBit (j + 1) = d.testBit j := by
          rw [Nat.testBit_succ]; congr 1; omega
        rw [e1, e2] at this
        simpa using this
      exact ⟨0, by simp [hd]⟩
    · have h2 : (d + 1) &&& d = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        have := congrArg (fun z => z.testBit (j + 1)) h
        simp only [Nat.testBit_and, Nat.zero_testBit] at this
        have e1 : (2 * d + 1 + 1).testBit (j + 1) = (d + 1).testBit j := by
          rw [Nat.testBit_succ]; congr 1; omega
        have e2 : (2 * d + 1).testBit (j + 1) = d.testBit j := by
          rw [Nat.testBit_succ]; congr 1; omega
        rw [e1, e2] at this
        simpa [Nat.testBit_and] using this
      obtain ⟨j, hj⟩ := ih d (by omega) h2
      exact ⟨j + 1, by rw [pow_succ]; omega⟩

/-- the single seed of rule `90` reads `1` at the cell `1` exactly at the steps `2 ^ i - 1` with
`1 ≤ i` -/
private theorem f90_single_apply_one_eq_one_iff (u : ℕ) :
    ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 1 ↔
      ∃ i, 1 ≤ i ∧ u + 1 = 2 ^ i := by
  constructor
  · intro h
    rcases Nat.even_or_odd' u with ⟨c, rfl | rfl⟩
    · have := f90_single_apply_eq_zero_of_odd (2 * c) 1 (by push_cast; omega)
      rw [this] at h
      exact absurd h (by decide)
    · by_contra hne
      have hsh : (c + 1) &&& c ≠ 0 := by
        intro h0
        obtain ⟨j, hj⟩ := exists_two_pow_of_succ_and_eq_zero c h0
        exact hne ⟨j + 1, by omega, by rw [pow_succ]; omega⟩
      have h0 := zeroOfShared (c + 1) c hsh
      rw [show c + 1 + c = 2 * c + 1 by ring, show (((c + 1 : ℕ) : ℤ) - (c : ℤ)) = 1 by
        push_cast; ring] at h0
      rw [h0] at h
      exact absurd h (by decide)
  · rintro ⟨i, hi, h⟩
    rw [show u = 2 ^ i - 1 by omega]
    exact f90_single_apply_one_two_pow_sub_one i hi

/-- the single seed of rule `90` reads at most one of the cells `-1` and `0` -/
private theorem f90_single_cells_parity (u : ℕ) :
    ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 0 ∨
      (((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 0 ∧
        ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 2 = 0) := by
  rcases Nat.even_or_odd' u with ⟨a, rfl | rfl⟩
  · left
    exact f90_single_apply_eq_zero_of_odd _ _ (by push_cast; omega)
  · right
    constructor <;> exact f90_single_apply_eq_zero_of_odd _ _ (by push_cast; omega)


/-! ## Rule `126` from the single seed near the cell `0` -/

/-- the five cells `-3, …, 1` of rule `126` from the single seed at an even step, read from rule
`90` -/
private theorem f126_single_two_mul_cells (u : ℕ) :
    ((finRule f126 hq126)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-3) =
        ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-2) ∧
      ((finRule f126 hq126)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-2) =
        ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-1) ∧
      ((finRule f126 hq126)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-1) =
        ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-1) ∧
      ((finRule f126 hq126)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 =
        ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 ∧
      ((finRule f126 hq126)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 =
        ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [f126_single_two_mul] <;> norm_num

/-- one more step of rule `126` reads three cells -/
private theorem f126_single_succ_apply (t : ℕ) (y : ℤ) :
    ((finRule f126 hq126)^[t + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) y =
      f126 (((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (y - 1))
        (((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) y)
        (((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (y + 1)) := by
  rw [Function.iterate_succ_apply', finRule_apply]

/-- the cells `-1` and `0` of rule `126` from the single seed at the step `t` sum to `1` exactly
when `t + 2` is a power of two with exponent at least `1` -/
private theorem f126_single_neg_one_add_zero_eq_one_iff (t : ℕ) :
    ((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-1) +
        ((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 1 ↔
      ∃ k, 1 ≤ k ∧ t + 2 = 2 ^ k := by
  rcases Nat.even_or_odd' t with ⟨u, rfl | rfl⟩
  · obtain ⟨-, -, h3, h4, -⟩ := f126_single_two_mul_cells u
    rw [h3, h4, finRule_f90_single_apply_neg u 1]
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · simp only [Function.iterate_zero, id_eq, Finsupp.single_apply]
      norm_num
      exact ⟨1, le_rfl, by norm_num⟩
    · rw [f90_single_apply_zero_of_pos u hu, add_zero, f90_single_apply_one_eq_one_iff]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i + 1, by omega, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk, h⟩
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ] at h
        refine ⟨k', ?_, by omega⟩
        rcases Nat.eq_zero_or_pos k' with rfl | hk'
        · simp at h; omega
        · omega
  · obtain ⟨-, h2, h3, h4, h5⟩ := f126_single_two_mul_cells u
    have e1 := f126_single_succ_apply (2 * u) (-1)
    have e2 := f126_single_succ_apply (2 * u) 0
    simp only [show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) + 1 = 0 by norm_num,
      show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) + 1 = 1 by norm_num] at e1 e2
    rw [e1, e2, h2, h3, h4, h5, finRule_f90_single_apply_neg u 1]
    have hz : ∀ a b : ZMod 2, (a = 0 ∨ b = 0) → f126 a a b + f126 a b a = 0 := by decide
    have hp : ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 0 ∨
        ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 0 := by
      rcases f90_single_cells_parity u with h | ⟨h, -⟩
      · left; exact h
      · right; exact h
    rw [hz _ _ hp]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨k, hk, h⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ] at h
      omega


/-- the cells `-2` and `-1` of rule `126` from the single seed at the step `t + 1` sum to `1`
exactly when `t + 4` is a power of two with exponent at least `2` -/
private theorem f126_single_neg_two_add_neg_one_eq_one_iff (t : ℕ) :
    ((finRule f126 hq126)^[t + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-2) +
        ((finRule f126 hq126)^[t + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-1) = 1 ↔
      ∃ k, 2 ≤ k ∧ t + 4 = 2 ^ k := by
  rcases Nat.even_or_odd' t with ⟨u, rfl | rfl⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := f126_single_two_mul_cells u
    have e1 := f126_single_succ_apply (2 * u) (-2)
    have e2 := f126_single_succ_apply (2 * u) (-1)
    simp only [show (-2 : ℤ) - 1 = -3 by norm_num, show (-2 : ℤ) + 1 = -1 by norm_num,
      show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) + 1 = 0 by norm_num] at e1 e2
    rw [e1, e2, h1, h2, h3, h4, finRule_f90_single_apply_neg u 1,
      finRule_f90_single_apply_neg u 2]
    have hid : ∀ x a b : ZMod 2, (a = 0 ∨ (b = 0 ∧ x = 0)) →
        f126 x a a + f126 a a b = b + x := by decide
    rw [hid _ _ _ (f90_single_cells_parity u)]
    have hstep : ((finRule f90 hq90)^[u + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 =
        ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 +
          ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 2 := by
      rw [Function.iterate_succ_apply', finRule_apply, f90]
      norm_num
    rw [← hstep, f90_single_apply_one_eq_one_iff]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i + 1, by omega, by rw [pow_succ]; omega⟩
    · rintro ⟨k, hk, h⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ] at h
      exact ⟨k', by omega, by omega⟩
  · obtain ⟨-, h2, h3, -, -⟩ := f126_single_two_mul_cells (u + 1)
    rw [show 2 * u + 1 + 1 = 2 * (u + 1) by ring, h2, h3]
    have hz : ∀ a : ZMod 2, a + a = 0 := by decide
    rw [hz]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨k, hk, h⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ] at h
      omega

/-! ## The two columns -/

/-- **The column of rule `18` from the seed `11` at its leftmost cell**
([RuleSpace] §4 Proposition 4.9): it reads `1` exactly at the steps `t` with `t + 2` a power of
two. The seed is the image of the single cell `1` under one step of rule `102`, which rule `18`
and rule `126` carry along `semiconj_f102_f126_f18`, so the column reads the cells `-1` and
`0` of rule `126` from the single seed, whose even rows are those of rule `90`
([RuleSpace] §5 Proposition 5.34, `f126_single_two_mul`). -/
theorem observedColumn_f18_eleven_eq_one_iff (t : ℕ) :
    observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1]) 0 t = 1 ↔
      ∃ k, 1 ≤ k ∧ t + 2 = 2 ^ k := by
  rw [observedColumn_eleven]
  exact f126_single_neg_one_add_zero_eq_one_iff t

/-- **The column of rule `18` from the seed `1001` at its leftmost cell**
([RuleSpace] §4 Proposition 4.9): it reads `1` exactly at the steps `t` with `t + 4` a power of
two of exponent at least `2`. The seed is the image of the first step of rule `126` from the
single cell `2` under one step of rule `102`, so the column reads the cells `-2` and `-1` of rule
`126` from the single seed one step later. -/
theorem observedColumn_f18_one_zero_zero_one_eq_one_iff (t : ℕ) :
    observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 0, 0, 1]) 0 t = 1 ↔
      ∃ k, 2 ≤ k ∧ t + 4 = 2 ^ k := by
  rw [observedColumn_one_zero_zero_one]
  exact f126_single_neg_two_add_neg_one_eq_one_iff t

/-! ## Not eventually periodic -/

/-- a sequence that reads `1` exactly at the steps one power of two short of `c`, from the
exponent `k₀`, is not eventually periodic -/
private theorem not_eventuallyPeriodic_of_two_pow_hits (c k₀ : ℕ) (u : ℕ → ZMod 2)
    (hu : ∀ t, u t = 1 ↔ ∃ k, k₀ ≤ k ∧ t + c = 2 ^ k) :
    ¬ DrivenColumns.EventuallyPeriodic u := by
  rintro ⟨P, N, hP, hper⟩
  set K : ℕ := N + c + P + k₀ with hK
  have hlt : K < 2 ^ K := Nat.lt_two_pow_self
  have h1 : u (2 ^ K - c) = 1 := (hu _).mpr ⟨K, by omega, by omega⟩
  have h2 : u (2 ^ K - c + P) ≠ 1 := by
    intro h
    obtain ⟨k, hk, hkk⟩ := (hu _).mp h
    have hk1 : K < k := by
      by_contra hle
      have : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ (K + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    rw [pow_succ] at this
    omega
  have h3 := hper (2 ^ K - c) (by omega)
  rw [h1] at h3
  exact h2 h3

/-- **Rule `18`: the columns of the seeds `11` and `1001` at their leftmost cell are not
eventually periodic** ([RuleSpace] §4 Proposition 4.9): each reads `1` exactly at the steps one
power of two short of a fixed number, so the gaps between its ones grow without bound. -/
theorem not_eventuallyPeriodic_observedColumn_f18_of_f126 :
    ∀ L ∈ ([[1, 1], [1, 0, 0, 1]] : List (List (ZMod 2))),
      ¬ DrivenColumns.EventuallyPeriodic
        (observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed L) 0) := by
  intro L hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl
  · exact not_eventuallyPeriodic_of_two_pow_hits 2 1 _ observedColumn_f18_eleven_eq_one_iff
  · exact not_eventuallyPeriodic_of_two_pow_hits 4 2 _
      observedColumn_f18_one_zero_zero_one_eq_one_iff


/-! ## The odd rows of rule `126` from the seed `101` -/

/-- the five-cell identity of two steps of rule `126` on a doubled row, from the symmetry of the
row alone -/
private theorem two_steps_halfIndex_symm (v : ℤ → ZMod 2) (hs : ∀ k, v (-k) = v k) (y : ℤ) :
    f126 (f126 (v (halfIndex (y - 2))) (v (halfIndex (y - 1))) (v (halfIndex y)))
        (f126 (v (halfIndex (y - 1))) (v (halfIndex y)) (v (halfIndex (y + 1))))
        (f126 (v (halfIndex y)) (v (halfIndex (y + 1))) (v (halfIndex (y + 2))))
      = v (halfIndex y - 1) + v (halfIndex y + 1) := by
  by_cases h2 : 2 ≤ y
  · obtain ⟨m, hm | hm⟩ := Int.even_or_odd' y
    · have e1 : halfIndex (y - 2) = m - 1 := by unfold halfIndex; split_ifs <;> omega
      have e2 : halfIndex (y - 1) = m := by unfold halfIndex; split_ifs <;> omega
      have e3 : halfIndex y = m := by unfold halfIndex; split_ifs <;> omega
      have e4 : halfIndex (y + 1) = m + 1 := by unfold halfIndex; split_ifs <;> omega
      have e5 : halfIndex (y + 2) = m + 1 := by unfold halfIndex; split_ifs <;> omega
      rw [e1, e2, e3, e4, e5]
      exact f126_two_steps_one _ _ _
    · have e1 : halfIndex (y - 2) = m := by unfold halfIndex; split_ifs <;> omega
      have e2 : halfIndex (y - 1) = m := by unfold halfIndex; split_ifs <;> omega
      have e3 : halfIndex y = m + 1 := by unfold halfIndex; split_ifs <;> omega
      have e4 : halfIndex (y + 1) = m + 1 := by unfold halfIndex; split_ifs <;> omega
      have e5 : halfIndex (y + 2) = m + 2 := by unfold halfIndex; split_ifs <;> omega
      rw [e1, e2, e3, e4, e5, show m + 1 - 1 = m by ring, show m + 1 + 1 = m + 2 by ring]
      exact f126_two_steps_two _ _ _
  · by_cases h3 : y ≤ -2
    · obtain ⟨m, hm | hm⟩ := Int.even_or_odd' y
      · have e1 : halfIndex (y - 2) = m - 1 := by unfold halfIndex; split_ifs <;> omega
        have e2 : halfIndex (y - 1) = m - 1 := by unfold halfIndex; split_ifs <;> omega
        have e3 : halfIndex y = m := by unfold halfIndex; split_ifs <;> omega
        have e4 : halfIndex (y + 1) = m := by unfold halfIndex; split_ifs <;> omega
        have e5 : halfIndex (y + 2) = m + 1 := by unfold halfIndex; split_ifs <;> omega
        rw [e1, e2, e3, e4, e5]
        exact f126_two_steps_two _ _ _
      · have e1 : halfIndex (y - 2) = m - 1 := by unfold halfIndex; split_ifs <;> omega
        have e2 : halfIndex (y - 1) = m := by unfold halfIndex; split_ifs <;> omega
        have e3 : halfIndex y = m := by unfold halfIndex; split_ifs <;> omega
        have e4 : halfIndex (y + 1) = m + 1 := by unfold halfIndex; split_ifs <;> omega
        have e5 : halfIndex (y + 2) = m + 1 := by unfold halfIndex; split_ifs <;> omega
        rw [e1, e2, e3, e4, e5]
        exact f126_two_steps_one _ _ _
    · have s1 := hs 1
      have s2 := hs 2
      have hy : y = -1 ∨ y = 0 ∨ y = 1 := by omega
      rcases hy with rfl | rfl | rfl
      · simp only [halfIndex]
        norm_num
        simp only [s1, s2]
        generalize v 0 = a
        generalize v 1 = b
        generalize v 2 = c
        revert a b c
        decide
      · simp only [halfIndex]
        norm_num
        simp only [s1]
        generalize v 0 = a
        generalize v 1 = b
        generalize v 2 = c
        revert a b c
        decide
      · simp only [halfIndex]
        norm_num
        simp only [s1]
        generalize v 0 = a
        generalize v 1 = b
        generalize v 2 = c
        revert a b c
        decide

/-- rule `90` is additive on configurations -/
private theorem iterate_f90_add (n : ℕ) :
    ∀ (s s' : FiniteConfiguration) (x : ℤ),
      ((finRule f90 hq90)^[n] (s + s')) x =
        ((finRule f90 hq90)^[n] s) x + ((finRule f90 hq90)^[n] s') x := by
  induction n with
  | zero => intro s s' x; simp
  | succ n ih =>
    intro s s' x
    have h : finRule f90 hq90 (s + s') = finRule f90 hq90 s + finRule f90 hq90 s' := by
      ext i
      simp only [finRule_apply, f90, Finsupp.add_apply]
      ring
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, h]
    exact ih _ _ x

/-- rule `90` from the seed `111` at the cells `-1, 0, 1` is the sum of three translates of its
orbit from the single seed -/
private theorem iterate_f90_one_one_one (n : ℕ) (x : ℤ) :
    ((finRule f90 hq90)^[n] (Finsupp.single (-1 : ℤ) (1 : ZMod 2) +
        Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1)) x =
      ((finRule f90 hq90)^[n] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (x + 1) +
        ((finRule f90 hq90)^[n] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x +
        ((finRule f90 hq90)^[n] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (x - 1) := by
  have hs : ∀ c : ℤ, ∀ y, (Finsupp.single c (1 : ZMod 2)) y =
      (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (y - c) := by
    intro c y
    simp only [Finsupp.single_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [iterate_f90_add, iterate_f90_add, iterate_shift f90 hq90 (-1) n _ _ (hs (-1)) x,
    iterate_shift f90 hq90 0 n _ _ (hs 0) x, iterate_shift f90 hq90 1 n _ _ (hs 1) x]
  simp only [sub_neg_eq_add, sub_zero]

/-- rule `90` from the seed `111` is symmetric about the cell `0` at every step -/
private theorem iterate_f90_one_one_one_neg (n : ℕ) (k : ℤ) :
    ((finRule f90 hq90)^[n] (Finsupp.single (-1 : ℤ) (1 : ZMod 2) +
        Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1)) (-k) =
      ((finRule f90 hq90)^[n] (Finsupp.single (-1 : ℤ) (1 : ZMod 2) +
        Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1)) k := by
  rw [iterate_f90_one_one_one, iterate_f90_one_one_one]
  have a1 := finRule_f90_single_apply_neg n (-k + 1)
  have a2 := finRule_f90_single_apply_neg n (-k)
  have a3 := finRule_f90_single_apply_neg n (-k - 1)
  rw [show -(-k + 1) = k - 1 by ring] at a1
  rw [neg_neg] at a2
  rw [show -(-k - 1) = k + 1 by ring] at a3
  rw [← a1, ← a2, ← a3]
  ring

/-- **The odd rows of rule `126` from the seed `101`**
([RuleSpace] §5 Proposition 5.34 doubles the single seed; [RuleSpace] §4 Proposition 4.9 uses
the seed `101` as the difference of `1111`): at the step `2 * v + 1`, rule `126` from the cells `1`
and `3` reads rule `90` from the cells `-1, 0, 1` at the step `v`, doubled toward the cell `2`. -/
theorem f126_one_zero_one_two_mul_add_one (v : ℕ) (y : ℤ) :
    ((finRule f126 hq126)^[2 * v + 1]
        (Finsupp.single (1 : ℤ) (1 : ZMod 2) + Finsupp.single (3 : ℤ) 1)) y =
      ((finRule f90 hq90)^[v] (Finsupp.single (-1 : ℤ) (1 : ZMod 2) +
          Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1))
        (if 0 ≤ y - 2 then (y - 2 + 1) / 2 else (y - 2) / 2) := by
  suffices key : ∀ (v : ℕ) (y : ℤ),
      ((finRule f126 hq126)^[2 * v + 1]
          (Finsupp.single (1 : ℤ) (1 : ZMod 2) + Finsupp.single (3 : ℤ) 1)) y =
        ((finRule f90 hq90)^[v] (Finsupp.single (-1 : ℤ) (1 : ZMod 2) +
            Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1)) (halfIndex (y - 2)) from
    key v y
  intro v
  induction v with
  | zero =>
    intro y
    simp only [mul_zero, zero_add, Function.iterate_one, Function.iterate_zero, id_eq,
      finRule_apply, halfIndex, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  | succ v ih =>
    intro y
    have hs := iterate_f90_one_one_one_neg v
    have key := two_steps_halfIndex_symm
      (fun k => ((finRule f90 hq90)^[v] (Finsupp.single (-1 : ℤ) (1 : ZMod 2) +
        Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1)) k) hs (y - 2)
    have e : 2 * (v + 1) + 1 = 2 * v + 1 + 1 + 1 := by ring
    rw [e, Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply' (finRule f90 hq90) v]
    simp only [finRule_apply, ih, f90, show y - 1 - 1 - 2 = y - 2 - 2 by ring,
      show y - 1 + 1 - 2 = y - 2 by ring, show y + 1 - 1 - 2 = y - 2 by ring,
      show y - 1 - 2 = y - 2 - 1 by ring, show y + 1 - 2 = y - 2 + 1 by ring,
      show y + 1 + 1 - 2 = y - 2 + 2 by ring]
    exact key


/-! ## The column of rule `18` from the seed `1111` -/

private theorem listSeed_one_one_one_one : listSeed [1, 1, 1, 1] =
    finRule f102 hq102 (Finsupp.single (1 : ℤ) (1 : ZMod 2) + Finsupp.single (3 : ℤ) 1) := by
  ext i
  simp only [listSeed, finRule_apply, f102]
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    List.getD_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- rule `90` at the even cells at the doubled step reads rule `90` at the step -/
private theorem iterate_f90_two_mul_apply (u : ℕ) :
    ∀ (s s' : FiniteConfiguration), (∀ j, s' (2 * j) = s j) → ∀ j,
      ((finRule f90 hq90)^[2 * u] s') (2 * j) = ((finRule f90 hq90)^[u] s) j := by
  induction u with
  | zero => intro s s' h j; simpa using h j
  | succ u ih =>
    intro s s' h j
    rw [show 2 * (u + 1) = 2 * u + 2 by ring, Function.iterate_add_apply,
      Function.iterate_succ_apply (finRule f90 hq90) u s]
    refine ih (finRule f90 hq90 s) ((finRule f90 hq90)^[2] s') ?_ j
    intro j'
    change finRule f90 hq90 (finRule f90 hq90 s') (2 * j') = finRule f90 hq90 s j'
    simp only [finRule_apply, f90, show 2 * j' - 1 - 1 = 2 * (j' - 1) by ring,
      show 2 * j' - 1 + 1 = 2 * j' by ring, show 2 * j' + 1 - 1 = 2 * j' by ring,
      show 2 * j' + 1 + 1 = 2 * (j' + 1) by ring, h]
    generalize s (j' - 1) = a
    generalize s j' = b
    generalize s (j' + 1) = c
    revert a b c
    decide

/-- the single seed of rule `90` at the cell `-2` at an even step reads its cell `1` at half the
step -/
private theorem f90_single_two_mul_neg_two (u : ℕ) :
    ((finRule f90 hq90)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-2) =
      ((finRule f90 hq90)^[u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 := by
  have h := iterate_f90_two_mul_apply u (Finsupp.single (0 : ℤ) (1 : ZMod 2))
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (fun j => by
      simp only [Finsupp.single_apply]
      split_ifs <;> first | rfl | (exfalso; omega)) (-1)
  rw [show (2 : ℤ) * (-1) = -2 by norm_num, finRule_f90_single_apply_neg u 1] at h
  exact h

/-- the column from the seed `1111` at cell `0` at the step `4 * u + 2` is the cells `-2` and `0`
of rule `90` from the single seed at the step `2 * u` -/
private theorem observedColumn_one_one_one_one (u : ℕ) :
    observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1, 1, 1]) 0 (4 * u + 2) =
      ((finRule f90 hq90)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-2) +
        ((finRule f90 hq90)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 := by
  unfold observedColumn
  rw [listSeed_one_one_one_one, iterate_f18_finRule_f102,
    show 4 * u + 2 = (2 * (2 * u) + 1) + 1 by ring]
  have hr : ∀ z : ℤ, ((finRule f126 hq126)^[2 * (2 * u) + 1]
      (Finsupp.single (1 : ℤ) (1 : ZMod 2) + Finsupp.single (3 : ℤ) 1)) z =
        ((finRule f90 hq90)^[2 * u] (Finsupp.single (-1 : ℤ) (1 : ZMod 2) +
          Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1)) (halfIndex (z - 2)) := by
    intro z
    rw [f126_one_zero_one_two_mul_add_one]
    rfl
  rw [Function.iterate_succ_apply', finRule_apply, finRule_apply]
  simp only [hr]
  have e1 : halfIndex (0 - 1 - 2) = -2 := by decide
  have e2 : halfIndex (0 - 2) = -1 := by decide
  have e3 : halfIndex (0 + 1 - 2) = -1 := by decide
  have e4 : halfIndex (0 + 1 + 1 - 2) = 0 := by decide
  have e5 : halfIndex (0 + 1 - 1 - 2) = -1 := by decide
  rw [e1, e2, e3, e5, e4]
  have hodd : ∀ x : ℤ, x % 2 = 1 →
      ((finRule f90 hq90)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x = 0 := by
    intro x hx
    exact f90_single_apply_eq_zero_of_odd _ _ (by push_cast; omega)
  have hm1 := hodd (-1) (by norm_num)
  have hm3 := hodd (-3) (by norm_num)
  have hp1 := hodd 1 (by norm_num)
  simp only [iterate_f90_one_one_one]
  norm_num
  rw [hm1, hm3, hp1]
  generalize ((finRule f90 hq90)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-2) = p
  generalize ((finRule f90 hq90)^[2 * u] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = q
  revert p q
  decide

/-- **The column of rule `18` from the seed `1111` at the steps `4 * u + 2`**
([RuleSpace] §4 Proposition 4.9): it reads `1` exactly when `4 * u + 4` is a power of two with
exponent at least `2`. The seed `1111` is the image of the seed `101` under one step of rule
`102`, which rule `18` and rule `126` carry along `semiconj_f102_f126_f18`, so the column reads
the cells `0` and `1` of rule `126` from `101`; at the step `4 * u + 2` they read the cells `-2`
and `0` of rule `90` from the single seed at the step `2 * u`
(`f126_one_zero_one_two_mul_add_one`, [RuleSpace] §5 Proposition 5.34). -/
theorem observedColumn_f18_one_one_one_one_four_mul_add_two_eq_one_iff (u : ℕ) :
    observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1, 1, 1]) 0
        (4 * u + 2) = 1 ↔
      ∃ k, 2 ≤ k ∧ 4 * u + 4 = 2 ^ k := by
  rw [observedColumn_one_one_one_one, f90_single_two_mul_neg_two]
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · constructor
    · intro _
      exact ⟨2, le_rfl, by norm_num⟩
    · intro _
      simp only [mul_zero, Function.iterate_zero, id_eq, Finsupp.single_apply]
      norm_num
  · rw [f90_single_apply_zero_of_pos (2 * u) (by omega), add_zero,
      f90_single_apply_one_eq_one_iff]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i + 2, by omega, by rw [pow_add]; norm_num; omega⟩
    · rintro ⟨k, hk, h⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      rw [pow_add] at h
      norm_num at h
      refine ⟨k', ?_, by omega⟩
      rcases Nat.eq_zero_or_pos k' with rfl | hk'
      · simp at h; omega
      · omega

/-- **Rule `18`: the column of the seed `1111` at its leftmost cell is not eventually periodic**
([RuleSpace] §4 Proposition 4.9, [RuleSpace] §5 Proposition 5.34): an eventually periodic column
is eventually periodic along the steps `4 * u + 2`, where it reads `1` exactly at the `u` one
short of a power of two, so the gaps between its ones grow without bound. -/
theorem not_eventuallyPeriodic_observedColumn_f18_one_one_one_one :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1, 1, 1]) 0) := by
  rintro ⟨P, N, hP, hper⟩
  have hm : ∀ (m : ℕ) (t : ℕ), N ≤ t →
      observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1, 1, 1]) 0
          (t + m * P) =
        observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1, 1, 1]) 0 t := by
    intro m
    induction m with
    | zero => intro t _; simp
    | succ m ih =>
      intro t ht
      rw [show t + (m + 1) * P = (t + m * P) + P by ring, hper _ (by omega)]
      exact ih t ht
  refine not_eventuallyPeriodic_of_two_pow_hits 1 0
    (fun u => observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1, 1, 1]) 0
      (4 * u + 2)) ?_ ⟨P, N, hP, fun u hu => ?_⟩
  · intro u
    rw [observedColumn_f18_one_one_one_one_four_mul_add_two_eq_one_iff]
    constructor
    · rintro ⟨k, hk, h⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      rw [pow_add] at h
      norm_num at h
      exact ⟨k', by omega, by omega⟩
    · rintro ⟨k, -, h⟩
      exact ⟨k + 2, by omega, by rw [pow_add]; norm_num; omega⟩
  · have := hm 4 (4 * u + 2) (by omega)
    change observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1, 1, 1]) 0
        (4 * (u + P) + 2) = _
    rw [show 4 * (u + P) + 2 = 4 * u + 2 + 4 * P by ring]
    exact this

end ECA

/-- info:
'ECA.semiconj_f102_f126_f18' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.semiconj_f102_f126_f18

/-- info:
'ECA.finRule_f102_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f102_injective

/-- info:
'ECA.observedColumn_f18_eleven_eq_one_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedColumn_f18_eleven_eq_one_iff

/-- info:
'ECA.observedColumn_f18_one_zero_zero_one_eq_one_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedColumn_f18_one_zero_zero_one_eq_one_iff

/-- info:
'ECA.not_eventuallyPeriodic_observedColumn_f18_of_f126' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_f18_of_f126

/-- info:
'ECA.f126_one_zero_one_two_mul_add_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f126_one_zero_one_two_mul_add_one

/-- info:
'ECA.observedColumn_f18_one_one_one_one_four_mul_add_two_eq_one_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedColumn_f18_one_one_one_one_four_mul_add_two_eq_one_iff

/-- info:
'ECA.not_eventuallyPeriodic_observedColumn_f18_one_one_one_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_f18_one_one_one_one
