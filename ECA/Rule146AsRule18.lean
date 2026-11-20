module

public import ECA.ReproductionBracket
public import ECA.Rule126Difference
public import ECA.StretchColumns
public import ErgodicTheory.DrivenColumns

/-!
# Rule `146` run as rule `18` away from three adjacent set cells, and six columns it decides
([RuleSpace] §4)

The tables of rules `146` and `18` differ only at the neighbourhood `111`, which rule `146` sends to
`1` and rule `18` to `0`. A configuration with no three adjacent set cells therefore takes the same
step under both. One step of rule `18` produces such a configuration at once. A cell is `1` after a
step of rule `18` only where it was `0` with exactly one neighbour set. Three adjacent ones in an
image would make the two outer cells each `0` before the step with the outside neighbour set, and
the middle one `0` with exactly one of those two cells set, which they are not. So the orbit of rule
`146` from a configuration with no three adjacent ones is the orbit of rule `18`.

The seeds `1101` and `1011` of rule `18` go in one step to the image of the seed `1111`, the state
with set cells exactly `-1` and `4`, so the columns at the leftmost cell agree from step `1` on, and
eventual periodicity is a property of a tail. The four seeds `11`, `1001`, `1101` and `1011` hold no
three adjacent ones, so rule `146` reads as rule `18` along their orbits.

## Main results

* `NoThreeAdjacentOnes` — a finite configuration with no three adjacent set cells.
* `noThreeAdjacentOnes_finRule_f18` — **every image of rule `18` has no three adjacent set cells.**
* `finRule_f146_eq_f18_of_noThreeAdjacentOnes` — the two rules agree on such a configuration.
* `iterate_f146_eq_f18_of_noThreeAdjacentOnes` — the whole orbit of rule `146` is rule `18`'s.
* `finRule_f18_listSeed_merge` — the seeds `1101` and `1011` meet the seed `1111` after one step of
  rule `18`.
* `not_eventuallyPeriodic_observedColumn_f18_odd_weight` — **the columns of rule `18` at the
  leftmost cell from the seeds `1101` and `1011` are not eventually periodic.**
* `not_eventuallyPeriodic_observedColumn_f146` — **the columns of rule `146` at the leftmost cell
  from the seeds `11`, `1001`, `1101` and `1011` are not eventually periodic.**
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## The cells of the five seeds -/

private theorem listSeed_eleven_apply (i : ℤ) :
    listSeed [1, 1] i = if i = 0 ∨ i = 1 then 1 else 0 := by
  simp only [listSeed, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    List.getD_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem listSeed_one_zero_zero_one_apply (i : ℤ) :
    listSeed [1, 0, 0, 1] i = if i = 0 ∨ i = 3 then 1 else 0 := by
  simp only [listSeed, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    List.getD_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem listSeed_one_one_zero_one_apply (i : ℤ) :
    listSeed [1, 1, 0, 1] i = if i = 0 ∨ i = 1 ∨ i = 3 then 1 else 0 := by
  simp only [listSeed, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    List.getD_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem listSeed_one_zero_one_one_apply (i : ℤ) :
    listSeed [1, 0, 1, 1] i = if i = 0 ∨ i = 2 ∨ i = 3 then 1 else 0 := by
  simp only [listSeed, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    List.getD_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem listSeed_one_one_one_one_apply (i : ℤ) :
    listSeed [1, 1, 1, 1] i = if i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 then 1 else 0 := by
  simp only [listSeed, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    List.getD_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **No three adjacent set cells**: among any three consecutive cells of the configuration, one
is `0`. -/
def NoThreeAdjacentOnes (s : FiniteConfiguration) : Prop :=
  ∀ i : ℤ, s (i - 1) = 0 ∨ s i = 0 ∨ s (i + 1) = 0

/-- **Every image of rule `18` has no three adjacent set cells**: a cell is `1` after a step of
rule `18` only where it was `0` with exactly one neighbour set, so two adjacent cells of an image
are never both `1` with a third beside them; the check is a decision over the five cells
`i - 2, …, i + 2`. -/
theorem noThreeAdjacentOnes_finRule_f18 (s : FiniteConfiguration) :
    NoThreeAdjacentOnes (finRule f18 agreesOffAdjacent_f18.1 s) := by
  intro i
  simp only [finRule_apply, f18]
  have h1 : i - 1 - 1 = i - 2 := by ring
  have h2 : i - 1 + 1 = i := by ring
  have h3 : i + 1 - 1 = i := by ring
  have h4 : i + 1 + 1 = i + 2 := by ring
  rw [h1, h2, h3, h4]
  generalize s (i - 2) = a
  generalize s (i - 1) = b
  generalize s i = c
  generalize s (i + 1) = d
  generalize s (i + 2) = e
  revert a b c d e
  decide

/-- **The tables of rules `146` and `18` differ only at `111`**: on a configuration with no three
adjacent set cells the two steps are equal. -/
theorem finRule_f146_eq_f18_of_noThreeAdjacentOnes (s : FiniteConfiguration)
    (h : NoThreeAdjacentOnes s) :
    finRule f146 hq146 s = finRule f18 agreesOffAdjacent_f18.1 s := by
  ext i
  simp only [finRule_apply, f146, f18]
  have hi := h i
  generalize s (i - 1) = a at hi ⊢
  generalize s i = b at hi ⊢
  generalize s (i + 1) = c at hi ⊢
  revert a b c
  decide

/-- **Rule `146` from a configuration with no three adjacent set cells is rule `18`**: the orbits
agree at every step, since after the first step both are images of rule `18`. -/
theorem iterate_f146_eq_f18_of_noThreeAdjacentOnes (s : FiniteConfiguration)
    (h : NoThreeAdjacentOnes s) (t : ℕ) :
    (finRule f146 hq146)^[t] s = (finRule f18 agreesOffAdjacent_f18.1)^[t] s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        finRule_f146_eq_f18_of_noThreeAdjacentOnes s h]
      exact ih _ (noThreeAdjacentOnes_finRule_f18 s)

/-- **The seeds `1101` and `1011` meet the seed `1111` after one step of rule `18`**: all three
go to the state whose set cells are exactly `-1` and `4`. -/
theorem finRule_f18_listSeed_merge :
    finRule f18 agreesOffAdjacent_f18.1 (listSeed [1, 1, 0, 1]) =
        finRule f18 agreesOffAdjacent_f18.1 (listSeed [1, 1, 1, 1]) ∧
      finRule f18 agreesOffAdjacent_f18.1 (listSeed [1, 0, 1, 1]) =
        finRule f18 agreesOffAdjacent_f18.1 (listSeed [1, 1, 1, 1]) := by
  constructor
  · ext i
    simp only [finRule_apply, f18, listSeed_one_one_zero_one_apply, listSeed_one_one_one_one_apply]
    split_ifs <;> first | (exfalso; omega) | decide
  · ext i
    simp only [finRule_apply, f18, listSeed_one_zero_one_one_apply, listSeed_one_one_one_one_apply]
    split_ifs <;> first | (exfalso; omega) | decide

/-- **A tail transfer**: eventual periodicity of a column passes to a column agreeing with it from
a step on. -/
private theorem eventuallyPeriodic_of_eq_from {f g : ℕ → ZMod 2} (k : ℕ)
    (hfg : ∀ t, k ≤ t → f t = g t) (hf : DrivenColumns.EventuallyPeriodic f) :
    DrivenColumns.EventuallyPeriodic g := by
  obtain ⟨P, N, hP, hper⟩ := hf
  refine ⟨P, max N k, hP, fun u hu => ?_⟩
  rw [← hfg u (le_trans (le_max_right _ _) hu),
    ← hfg (u + P) (le_trans (le_max_right _ _) (Nat.le_add_right_of_le hu))]
  exact hper u (le_trans (le_max_left _ _) hu)

/-- **Rule `18`: the columns of the seeds `1101` and `1011` at their leftmost cell are not
eventually periodic** ([RuleSpace] §4): from step `1` on each agrees with the column from `1111`,
which is not eventually periodic. -/
theorem not_eventuallyPeriodic_observedColumn_f18_odd_weight :
    ∀ L ∈ ([[1, 1, 0, 1], [1, 0, 1, 1]] : List (List (ZMod 2))),
      ¬ DrivenColumns.EventuallyPeriodic
        (observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed L) 0) := by
  intro L hL hep
  have key : ∀ t, 1 ≤ t →
      observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed L) 0 t =
        observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed [1, 1, 1, 1]) 0 t := by
    intro t ht
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' ht
    simp only [observedColumn, Function.iterate_succ_apply]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · rw [finRule_f18_listSeed_merge.1]
    · rw [finRule_f18_listSeed_merge.2]
  exact not_eventuallyPeriodic_observedColumn_f18_one_one_one_one
    (eventuallyPeriodic_of_eq_from 1 key hep)

/-- **Rule `146`: the columns of the seeds `11`, `1001`, `1101` and `1011` at their leftmost cell
are not eventually periodic** ([RuleSpace] §4): none of the four seeds holds three adjacent ones,
so the column is rule `18`'s from the same seed. -/
theorem not_eventuallyPeriodic_observedColumn_f146 :
    ∀ L ∈ ([[1, 1], [1, 0, 0, 1], [1, 1, 0, 1], [1, 0, 1, 1]] : List (List (ZMod 2))),
      ¬ DrivenColumns.EventuallyPeriodic
        (observedColumn (finRule f146 hq146) (listSeed L) 0) := by
  intro L hL
  have hno : NoThreeAdjacentOnes (listSeed L) := by
    intro i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl
    · simp only [listSeed_eleven_apply]
      split_ifs <;> first | (exfalso; omega) | decide
    · simp only [listSeed_one_zero_zero_one_apply]
      split_ifs <;> first | (exfalso; omega) | decide
    · simp only [listSeed_one_one_zero_one_apply]
      split_ifs <;> first | (exfalso; omega) | decide
    · simp only [listSeed_one_zero_one_one_apply]
      split_ifs <;> first | (exfalso; omega) | decide
  have heq : observedColumn (finRule f146 hq146) (listSeed L) 0 =
      observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed L) 0 := by
    funext t
    simp only [observedColumn]
    rw [iterate_f146_eq_f18_of_noThreeAdjacentOnes _ hno]
  rw [heq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact not_eventuallyPeriodic_observedColumn_f18_of_f126 _ (by simp)
  · exact not_eventuallyPeriodic_observedColumn_f18_of_f126 _ (by simp)
  · exact not_eventuallyPeriodic_observedColumn_f18_odd_weight _ (by simp)
  · exact not_eventuallyPeriodic_observedColumn_f18_odd_weight _ (by simp)

end ECA

/-- info:
'ECA.noThreeAdjacentOnes_finRule_f18' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.noThreeAdjacentOnes_finRule_f18

/-- info:
'ECA.finRule_f146_eq_f18_of_noThreeAdjacentOnes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f146_eq_f18_of_noThreeAdjacentOnes

/-- info:
'ECA.iterate_f146_eq_f18_of_noThreeAdjacentOnes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.iterate_f146_eq_f18_of_noThreeAdjacentOnes

/-- info:
'ECA.finRule_f18_listSeed_merge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f18_listSeed_merge

/-- info:
'ECA.not_eventuallyPeriodic_observedColumn_f18_odd_weight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_f18_odd_weight

/-- info:
'ECA.not_eventuallyPeriodic_observedColumn_f146' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_f146
