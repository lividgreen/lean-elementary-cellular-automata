module

public import ECA.DefectCounts
public import ECA.Doubling
import all ECA.DefectCounts

/-!
# The odd-run count never increases in one step of rule `126`
([RuleSpace] §5)

[RuleSpace] §5 Proposition 5.25 shows that a rule agreeing with rule `90` at equal adjacent cells
reproduces every nonzero doubled pattern, and `ECA.DefectCounts` shows that such a rule whose
odd-run count never increases in one step reproduces nothing else. This module shows the
monotonicity at rule `126`, and with it the converse there.

* `finRule_f126_apply_boundary` — the image of a state under rule `126` is the boundary
  set of the state dilated by one cell.
* `FiniteConfiguration.dilate` — a state `B` and the state `i ↦ B (i - 1) + B i + B (i - 1) B i`,
  whose set cells are those of `B` and their right neighbours.
* `FiniteConfiguration.kinkCount_boundary_dilate_le` — dilating a state does not increase the kink
  count of its boundary.
* `oddRunCountMono_f126` — rule `126` never increases the odd-run count.
* `not_oddRunCountMono_f94`, `not_oddRunCountMono_f122` — the monotonicity fails at rules `94` and
  `122`, the other rules agreeing with rule `90` at equal adjacent cells.
* `reproduces_iff_dbl_f126` — **at rule `126` the patterns reproduced are exactly the nonzero
  translates of doubled patterns** ([RuleSpace] §5 Proposition 5.25), and
  `LocalRule.DoubledAgree.reproduces_iff_dbl_nonvacuous` meets the hypotheses of the iff theorem.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The image of rule `126` is a dilation of the boundary -/

/-- **The dilation of a state**: the state `i ↦ B (i - 1) + B i + B (i - 1) B i`, whose set cells
are the set cells of `B` and their right neighbours. -/
noncomputable def FiniteConfiguration.dilate (B : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.onFinset (B.support ∪ B.support.image (· + 1))
    (fun i => B (i - 1) + B i + B (i - 1) * B i) (by
    intro i hi
    by_cases h : B i = 0
    · have h1 : B (i - 1) ≠ 0 := by
        intro h1
        apply hi
        rw [h, h1]
        simp
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i - 1, Finsupp.mem_support_iff.mpr h1, by ring⟩)
    · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))

/-- The dilation of a state at a cell. -/
theorem FiniteConfiguration.dilate_apply (B : FiniteConfiguration) (i : ℤ) :
    dilate B i = B (i - 1) + B i + B (i - 1) * B i := by
  simp [dilate, Finsupp.onFinset_apply]

/-- **The image of rule `126` is the boundary set dilated by one cell**: rule `126` sets a cell
exactly when its three cells are not all equal, that is, when there is a boundary at the cell to the
left or at the cell. -/
theorem finRule_f126_apply_boundary (s : FiniteConfiguration) (i : ℤ) :
    finRule f126 hq126 s i =
      boundary s (i - 1) + boundary s i + boundary s (i - 1) * boundary s i := by
  rw [finRule_apply, boundary_apply, boundary_apply, show i - 1 + 1 = i by ring]
  generalize s (i - 1) = a
  generalize s i = b
  generalize s (i + 1) = c
  revert a b c
  unfold f126 wolframRule
  decide

/-! ## Dilation does not increase the kink count of the boundary -/

/-- The cells of the boundary of a dilation: `m` is one exactly when the dilation differs at `m`
and `m + 1`. -/
private theorem boundary_dilate_ne_zero_iff (B : FiniteConfiguration) (m : ℤ) :
    boundary (dilate B) m ≠ 0 ↔
      ¬ ((B (m - 1) ≠ 0 ∨ B m ≠ 0) ↔ (B m ≠ 0 ∨ B (m + 1) ≠ 0)) := by
  rw [boundary_apply, dilate_apply, dilate_apply, show m + 1 - 1 = m by ring]
  generalize B (m - 1) = a
  generalize B m = b
  generalize B (m + 1) = c
  revert a b c
  decide

/-- Induction on the integers from a base point. -/
private theorem intInd {a : ℤ} {Q : ℤ → Prop} (h0 : Q a) (hs : ∀ n, a ≤ n → Q n → Q (n + 1))
    (n : ℤ) (hn : a ≤ n) : Q n := by
  obtain ⟨k, rfl⟩ := Int.le.dest hn
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have := hs (a + k) (by omega) (ih (by omega))
    simpa [add_assoc] using this

/-- The combinatorial heart: between two consecutive boundaries of a dilation at odd distance,
either the set cells have a gap around them (the pair of set cells enclosing them has odd
distance), or two adjacent set cells lie strictly inside. -/
private theorem dilate_kink_cases (P : ℤ → Prop) {j j' : ℤ} (hjj : j < j') (hodd : Odd (j' - j))
    (hj : ¬ ((P (j - 1) ∨ P j) ↔ (P j ∨ P (j + 1))))
    (hj' : ¬ ((P (j' - 1) ∨ P j') ↔ (P j' ∨ P (j' + 1))))
    (hmid : ∀ m, j < m → m < j' → ((P (m - 1) ∨ P m) ↔ (P m ∨ P (m + 1)))) :
    ((P (j - 1) ∧ ¬ P j ∧ P (j' + 1)) ∧ ∀ t, P t → t ≤ j - 1 ∨ j' + 1 ≤ t) ∨
    (¬ P j ∧ ∃ m, j + 1 ≤ m ∧ m + 1 ≤ j' - 1 ∧ P m ∧ P (m + 1)) := by
  obtain ⟨k, hk⟩ := hodd
  -- the run indicator `P m ∨ P (m + 1)` is constant on `j .. j' - 1`
  have hconst : ∀ m : ℤ, j ≤ m → m ≤ j' - 1 → ((P j ∨ P (j + 1)) ↔ (P m ∨ P (m + 1))) := by
    intro m hm
    refine intInd (Q := fun m => m ≤ j' - 1 → ((P j ∨ P (j + 1)) ↔ (P m ∨ P (m + 1))))
      (fun _ => Iff.rfl) (fun n hn ih hle => ?_) m hm
    have h1 := hmid (n + 1) (by omega) (by omega)
    rw [show n + 1 - 1 = n by ring] at h1
    exact (ih (by omega)).trans h1
  have hQ' : ∀ m : ℤ, j ≤ m → m ≤ j' - 1 → ((P j ∨ P (j + 1)) ↔ (P (j' - 1) ∨ P j')) := by
    intro m hm hm'
    have := hconst (j' - 1) (by omega) le_rfl
    rwa [show j' - 1 + 1 = j' by ring] at this
  by_cases hc : P j ∨ P (j + 1)
  · -- the dilation is set on `j + 1 .. j'`
    have hR : ∀ m : ℤ, j ≤ m → m ≤ j' - 1 → (P m ∨ P (m + 1)) :=
      fun m h1 h2 => (hconst m h1 h2).mp hc
    have hq : ¬ (P (j - 1) ∨ P j) := fun h => hj ⟨fun _ => hc, fun _ => h⟩
    have hPj : ¬ P j := fun h => hq (Or.inr h)
    have hPj1 : P (j + 1) := hc.resolve_left hPj
    have hQc : P (j' - 1) ∨ P j' := (hQ' j le_rfl (by omega)).mp hc
    have hq' : ¬ (P j' ∨ P (j' + 1)) := fun h => hj' ⟨fun _ => h, fun _ => hQc⟩
    have hPj' : P (j' - 1) := hQc.resolve_right fun h => hq' (Or.inl h)
    refine Or.inr ⟨hPj, ?_⟩
    by_contra hno
    push Not at hno
    have key : ∀ x : ℤ, j + 1 ≤ x → x ≤ j' - 1 → (P x ↔ (x - (j + 1)) % 2 = 0) := by
      intro x hx
      refine intInd (Q := fun x => x ≤ j' - 1 → (P x ↔ (x - (j + 1)) % 2 = 0))
        (fun _ => ⟨fun _ => by omega, fun _ => hPj1⟩) (fun n hn ih hle => ?_) x hx
      have ih' := ih (by omega)
      by_cases hev : (n - (j + 1)) % 2 = 0
      · have hPn := ih'.mpr hev
        have : ¬ P (n + 1) := fun h => hno n hn (by omega) hPn h
        exact ⟨fun h => absurd h this, fun h => by omega⟩
      · have hPn : ¬ P n := fun h => hev (ih'.mp h)
        have hr := hR n (by omega) (by omega)
        exact ⟨fun _ => by omega, fun _ => hr.resolve_left hPn⟩
    have h1 := (key (j' - 1) (by
      by_contra hlt
      have : j' - 1 = j := by omega
      rw [this] at hPj'
      exact hPj hPj') le_rfl).mp hPj'
    omega
  · -- the dilation is clear on `j + 1 .. j'`
    have hR : ∀ m : ℤ, j ≤ m → m ≤ j' - 1 → ¬ (P m ∨ P (m + 1)) :=
      fun m h1 h2 h => hc ((hconst m h1 h2).mpr h)
    have hq : P (j - 1) ∨ P j := by
      by_contra h
      exact hj ⟨fun q => (h q).elim, fun r => (hc r).elim⟩
    have hPj : ¬ P j := fun h => hc (Or.inl h)
    have hQc : ¬ (P (j' - 1) ∨ P j') := fun h => hc ((hQ' j le_rfl (by omega)).mpr h)
    have hq' : P j' ∨ P (j' + 1) := by
      by_contra h
      exact hj' ⟨fun q => (hQc q).elim, fun r => (h r).elim⟩
    have hPj' : ¬ P j' := fun h => hQc (Or.inr h)
    refine Or.inl ⟨⟨hq.resolve_right hPj, hPj, hq'.resolve_left hPj'⟩, fun t ht => ?_⟩
    by_contra hno
    push Not at hno
    by_cases htj : t = j'
    · exact hPj' (htj ▸ ht)
    · by_cases htj0 : t = j
      · exact hPj (htj0 ▸ ht)
      · exact hR t (by omega) (by omega) (Or.inl ht)

/-- **Dilating a state does not increase the kink count of its boundary**: a kink of the boundary
of the dilation, a pair of consecutive boundaries at odd distance, is sent to a kink of the state,
either the pair of set cells enclosing a clear stretch or the first pair of adjacent set cells
inside a run of the dilation. -/
theorem FiniteConfiguration.kinkCount_boundary_dilate_le (B : FiniteConfiguration) :
    kinkCount (boundary (dilate B)) ≤ kinkCount B := by
  classical
  have hex : ∀ j : ℤ, j ∈ (boundary (dilate B)).support →
      (∃ j' ∈ (boundary (dilate B)).support, j < j' ∧ Odd (j' - j) ∧
        ∀ t ∈ (boundary (dilate B)).support, t ≤ j ∨ j' ≤ t) →
      ∃ m : ℤ, (m ∈ B.support ∧ ∃ n ∈ B.support, m < n ∧ Odd (n - m) ∧
          ∀ t ∈ B.support, t ≤ m ∨ n ≤ t) ∧
        ((m = j - 1 ∧ B j = 0) ∨ (B m ≠ 0 ∧ B (m + 1) ≠ 0 ∧ j + 1 ≤ m ∧ ∃ j' : ℤ, j < j' ∧
          m + 1 < j' ∧ ∀ t ∈ (boundary (dilate B)).support, t ≤ j ∨ j' ≤ t)) := by
    intro j hjT ⟨j', hj'T, hjj, hodd, hnext⟩
    have hj := (boundary_dilate_ne_zero_iff B j).mp (Finsupp.mem_support_iff.mp hjT)
    have hj' := (boundary_dilate_ne_zero_iff B j').mp (Finsupp.mem_support_iff.mp hj'T)
    have hmid : ∀ m, j < m → m < j' →
        ((B (m - 1) ≠ 0 ∨ B m ≠ 0) ↔ (B m ≠ 0 ∨ B (m + 1) ≠ 0)) := by
      intro m h1 h2
      by_contra hne
      have hm : m ∈ (boundary (dilate B)).support :=
        Finsupp.mem_support_iff.mpr ((boundary_dilate_ne_zero_iff B m).mpr hne)
      rcases hnext m hm with h | h <;> omega
    rcases dilate_kink_cases (fun x => B x ≠ 0) hjj hodd hj hj' hmid with
      ⟨⟨h1, h2, h3⟩, h4⟩ | ⟨h1, m, hm1, hm2, hm3, hm4⟩
    · refine ⟨j - 1, ⟨Finsupp.mem_support_iff.mpr h1, j' + 1, Finsupp.mem_support_iff.mpr h3,
        by omega, ?_, fun t ht => h4 t (Finsupp.mem_support_iff.mp ht)⟩,
        Or.inl ⟨rfl, not_not.mp h2⟩⟩
      rw [show j' + 1 - (j - 1) = (j' - j) + 2 by ring]
      exact hodd.add_even even_two
    · refine ⟨m, ⟨Finsupp.mem_support_iff.mpr hm3, m + 1, Finsupp.mem_support_iff.mpr hm4,
        by omega, by simp, fun t _ => by omega⟩, Or.inr ⟨hm3, hm4, hm1, j', hjj, by omega, hnext⟩⟩
  choose! f hfC hfspec using hex
  unfold kinkCount
  refine Finset.card_le_card_of_injOn f (fun j hj => ?_) (fun j hj k hk he => ?_)
  · obtain ⟨hjT, hex'⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr (hfC j hjT hex')
  · obtain ⟨hjT, hex1⟩ := Finset.mem_filter.mp hj
    obtain ⟨hkT, hex2⟩ := Finset.mem_filter.mp hk
    have s1 := (hfC j hjT hex1).2
    have s2 := (hfC k hkT hex2).2
    have hspecj := hfspec j hjT hex1
    have hspeck := hfspec k hkT hex2
    rw [he] at hspecj
    rcases hspecj with ⟨e1, e2⟩ | ⟨a1, a2, a3, j1, a4, a5, a6⟩ <;>
      rcases hspeck with ⟨e3, e4⟩ | ⟨b1, b2, b3, k1, b4, b5, b6⟩
    · omega
    · exfalso
      apply b2
      rw [show f k + 1 = j by omega]
      exact e2
    · exfalso
      apply a2
      rw [show f k + 1 = k by omega]
      exact e4
    · rcases lt_trichotomy j k with hlt | heq | hgt
      · exfalso
        have := a6 k hkT
        omega
      · exact heq
      · exfalso
        have := b6 j hjT
        omega

/-! ## Rule `126` -/

/-- **Rule `126` never increases the odd-run count**: the image of a state is the dilation of its
boundary, and dilating does not increase the kink count of the boundary. -/
theorem oddRunCountMono_f126 : OddRunCountMono f126 hq126 := by
  intro s
  have e : finRule f126 hq126 s = dilate (boundary s) := by
    ext i
    rw [finRule_f126_apply_boundary, dilate_apply]
  unfold oddRunCount
  rw [e]
  exact kinkCount_boundary_dilate_le (boundary s)

/-! ## The monotonicity fails at rules `94` and `122` -/

/-- The state with set cells exactly `S`. -/
private noncomputable abbrev stateOfCells (S : Finset ℤ) : FiniteConfiguration :=
  ∑ i ∈ S, Finsupp.single i (1 : ZMod 2)

private theorem stateOfCells_apply (S : Finset ℤ) (j : ℤ) :
    stateOfCells S j = if j ∈ S then 1 else 0 := by
  simp [stateOfCells, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Closes the cell-by-cell description of a small state's boundary. -/
local macro "cells_iff" : tactic =>
  `(tactic| (split_ifs <;> (try simp only [Finset.mem_insert, Finset.mem_singleton]) <;>
    first | omega | (constructor <;> intro h <;>
      first | omega | exact absurd h (by decide) | decide)))

/-- **Rule `94` creates odd runs**: the state `11011`, one odd run (the two runs are of even
length and the gap is odd), steps to `111 0 111`, three odd runs. -/
theorem not_oddRunCountMono_f94 : ¬ OddRunCountMono f94 hq94 := by
  intro h
  have himg : finRule f94 hq94 (stateOfCells {0, 1, 3, 4}) = stateOfCells {-1, 0, 1, 3, 4, 5} := by
    ext j
    rw [finRule_apply]
    simp only [stateOfCells_apply, Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> first | omega | (unfold f94 wolframRule; decide)
  have h1 : oddRunCount (stateOfCells {0, 1, 3, 4}) = 1 := by
    rw [oddRunCount_of_boundary (S := {-1, 1, 2, 4}) fun i => by
      simp only [stateOfCells_apply, Finset.mem_insert, Finset.mem_singleton]; cells_iff]
    decide
  have h2 : oddRunCount (stateOfCells {-1, 0, 1, 3, 4, 5}) = 3 := by
    rw [oddRunCount_of_boundary (S := {-2, 1, 2, 5}) fun i => by
      simp only [stateOfCells_apply, Finset.mem_insert, Finset.mem_singleton]; cells_iff]
    decide
  have := h (stateOfCells {0, 1, 3, 4})
  rw [himg, h1, h2] at this
  omega

/-- **Rule `122` creates odd runs**: the single set cell, one odd run, steps to two set cells at
distance two, three odd runs. -/
theorem not_oddRunCountMono_f122 : ¬ OddRunCountMono f122 hq122 := by
  intro h
  have himg : finRule f122 hq122 (stateOfCells {0}) = stateOfCells {-1, 1} := by
    ext j
    rw [finRule_apply]
    simp only [stateOfCells_apply, Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> first | omega | (unfold f122 wolframRule; decide)
  have h1 : oddRunCount (stateOfCells {0}) = 1 := by
    rw [oddRunCount_of_boundary (S := {-1, 0}) fun i => by
      simp only [stateOfCells_apply, Finset.mem_insert, Finset.mem_singleton]; cells_iff]
    decide
  have h2 : oddRunCount (stateOfCells {-1, 1}) = 3 := by
    rw [oddRunCount_of_boundary (S := {-2, -1, 0, 1}) fun i => by
      simp only [stateOfCells_apply, Finset.mem_insert, Finset.mem_singleton]; cells_iff]
    decide
  have := h (stateOfCells {0})
  rw [himg, h1, h2] at this
  omega

/-! ## The patterns reproduced -/

/-- **At rule `126` the patterns reproduced are exactly the nonzero translates of doubled
patterns** ([RuleSpace] §5 Proposition 5.25). -/
theorem reproduces_iff_dbl_f126 (p : FiniteConfiguration) :
    Reproduces (finRule f126 hq126) p ↔ p ≠ 0 ∧ ∃ x c, p = translate c (dbl x) :=
  LocalRule.DoubledAgree.reproduces_iff_dbl f126 hq126 doubledAgree_f126 oddRunCountMono_f126
    oddRunCountCopies p

/-- The hypotheses of `LocalRule.DoubledAgree.reproduces_iff_dbl` are met at once, at rule
`126`. -/
theorem LocalRule.DoubledAgree.reproduces_iff_dbl_nonvacuous :
    ∃ (f : LocalRule) (hq : f 0 0 0 = 0), DoubledAgree f ∧ OddRunCountMono f hq ∧
      OddRunCountCopies :=
  ⟨f126, hq126, doubledAgree_f126, oddRunCountMono_f126, oddRunCountCopies⟩

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_f126_apply_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f126_apply_boundary

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.dilate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.dilate_apply

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.kinkCount_boundary_dilate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.kinkCount_boundary_dilate_le

set_option linter.style.longLine false in
/-- info: 'ECA.oddRunCountMono_f126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.oddRunCountMono_f126

set_option linter.style.longLine false in
/-- info: 'ECA.not_oddRunCountMono_f94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_oddRunCountMono_f94

set_option linter.style.longLine false in
/-- info: 'ECA.not_oddRunCountMono_f122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_oddRunCountMono_f122

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_dbl_f126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_dbl_f126

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.DoubledAgree.reproduces_iff_dbl_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.DoubledAgree.reproduces_iff_dbl_nonvacuous

end ECA
