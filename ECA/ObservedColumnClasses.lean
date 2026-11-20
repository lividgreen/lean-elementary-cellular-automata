module

public import ECA.ObservedColumn
public import ECA.ReproductionBracket
public import ECA.Rule150Rays
public import ErgodicTheory.DrivenColumns

/-!
# Three classes of observed columns: a frozen left edge, an unread neighbour, a mirror seed
([RuleSpace] §4 Proposition 4.2)

The observed column of a radius-one rule from a finite seed (`observedColumn`) is eventually
periodic wherever [RuleSpace] §4 Proposition 4.2's driven-column engine
(`DrivenColumns.eventuallyPeriodic_of_driven`) has a periodic input to start from. This module
gives three classes of rule and seed that supply one.

* A left edge that does not move (`h001`: a clear cell with a clear left neighbour stays clear;
  `h010`, `h011`: a set cell with a clear left neighbour stays set): the leftmost set cell of the
  seed stays set at every time (`observedColumn_min_eq_one_of_frozenLeftEdge`), so its column is
  constant (`eventuallyPeriodic_observedColumn_min_of_frozenLeftEdge`).
  `observedColumn_min_frozenLeftEdge_guard` is the rule `90`, which fails `h010`, with the
  conclusion failing at the seed's own cell;
  `observedColumn_min_eq_one_of_frozenLeftEdge_nonvacuous` meets the hypotheses at once.
* A rule that does not read one neighbour: every observed column from every finite seed is
  eventually periodic (`eventuallyPeriodic_observedColumn_of_left_unread`,
  `eventuallyPeriodic_observedColumn_of_right_unread`), by constancy past the support on the
  unread side and the driven-column engine one cell at a time on the other; the two rules `102`
  and `60` are the instances (`eventuallyPeriodic_observedColumn_f102`,
  `eventuallyPeriodic_observedColumn_f60`).
* A mirror-symmetric seed at a mirror-symmetric rule (`finRule_iterate_mirror`): the symmetry is
  kept at every time, so at the centre the two neighbours agree; rule `90` reads clear from time
  one on (`observedColumn_f90_eq_zero_of_mirror`) and rule `150` keeps the centre's value
  (`observedColumn_f150_eq_of_mirror`), so both columns are eventually periodic
  (`eventuallyPeriodic_observedColumn_f90_of_mirror`,
  `eventuallyPeriodic_observedColumn_f150_of_mirror`). The converse, that a seed not mirror
  symmetric about a cell has a column there that is not eventually periodic, is
  `ECA.MirrorColumns` ([RuleSpace] §4 Proposition 4.8).
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## A left edge that does not move -/

private theorem zmod_two_eq_zero_or_one_aux (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

/-- **The invariant of a frozen left edge**: if every cell left of `m` is clear and `m` is set, the
same holds at every time, at a rule that leaves a clear cell with a clear left neighbour clear and a
set cell with a clear left neighbour set. -/
private theorem frozenLeftEdge_iterate_aux (f : LocalRule) (hq : f 0 0 0 = 0)
    (h001 : f 0 0 1 = 0) (h010 : f 0 1 0 = 1) (h011 : f 0 1 1 = 1)
    (s₀ : FiniteConfiguration) {m : ℤ} (hlt : ∀ j, j < m → s₀ j = 0) (hm : s₀ m = 1) (t : ℕ) :
    (∀ j, j < m → ((finRule f hq)^[t] s₀) j = 0) ∧ ((finRule f hq)^[t] s₀) m = 1 := by
  induction t with
  | zero => exact ⟨hlt, hm⟩
  | succ t ih =>
    obtain ⟨hl, hc⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [finRule_apply]
      rcases lt_or_eq_of_le (show j + 1 ≤ m by omega) with h | h
      · rw [hl (j - 1) (by omega), hl j hj, hl (j + 1) h, hq]
      · rw [hl (j - 1) (by omega), hl j hj, h, hc, h001]
    · rw [finRule_apply, hc, hl (m - 1) (by omega)]
      rcases zmod_two_eq_zero_or_one_aux (((finRule f hq)^[t] s₀) (m + 1)) with h | h <;> rw [h]
      · exact h010
      · exact h011

/-- **A left edge that does not move**: at a rule where a clear cell with a clear left neighbour
stays clear and a set cell with a clear left neighbour stays set, the leftmost set cell of a
nonzero seed reads `1` at every time. -/
theorem observedColumn_min_eq_one_of_frozenLeftEdge (f : LocalRule) (hq : f 0 0 0 = 0)
    (h001 : f 0 0 1 = 0) (h010 : f 0 1 0 = 1) (h011 : f 0 1 1 = 1)
    (s₀ : FiniteConfiguration) (hs : s₀.support.Nonempty) (t : ℕ) :
    observedColumn (finRule f hq) s₀ (s₀.support.min' hs) t = 1 := by
  have hm : s₀ (s₀.support.min' hs) = 1 := by
    have h := Finsupp.mem_support_iff.mp (s₀.support.min'_mem hs)
    rcases zmod_two_eq_zero_or_one_aux (s₀ (s₀.support.min' hs)) with h' | h'
    · exact absurd h' h
    · exact h'
  have hlt : ∀ j, j < s₀.support.min' hs → s₀ j = 0 := by
    intro j hj
    by_contra hc
    have := Finset.min'_le s₀.support j (Finsupp.mem_support_iff.mpr hc)
    omega
  exact (frozenLeftEdge_iterate_aux f hq h001 h010 h011 s₀ hlt hm t).2

/-- **The column of a frozen left edge is eventually periodic**: it is constantly `1`. -/
theorem eventuallyPeriodic_observedColumn_min_of_frozenLeftEdge (f : LocalRule)
    (hq : f 0 0 0 = 0) (h001 : f 0 0 1 = 0) (h010 : f 0 1 0 = 1) (h011 : f 0 1 1 = 1)
    (s₀ : FiniteConfiguration) (hs : s₀.support.Nonempty) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) s₀ (s₀.support.min' hs)) :=
  ⟨1, 0, one_pos, fun u _ => by
    rw [observedColumn_min_eq_one_of_frozenLeftEdge f hq h001 h010 h011 s₀ hs (u + 1),
      observedColumn_min_eq_one_of_frozenLeftEdge f hq h001 h010 h011 s₀ hs u]⟩

/-- The joint-satisfiability witness for the frozen left edge: rule `60` (`a + b` on a cell and its
left neighbour) meets `h001`, `h010` and `h011` at once, and at the single seed the leftmost set
cell, the seed's own cell, reads `1` at every time. -/
theorem observedColumn_min_eq_one_of_frozenLeftEdge_nonvacuous :
    f60 0 0 1 = 0 ∧ f60 0 1 0 = 1 ∧ f60 0 1 1 = 1 ∧
      ∃ hs : (Finsupp.single (0 : ℤ) (1 : ZMod 2)).support.Nonempty,
        ∀ t, observedColumn (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
          ((Finsupp.single (0 : ℤ) (1 : ZMod 2)).support.min' hs) t = 1 :=
  ⟨by decide, by decide, by decide, ⟨0, by simp⟩, fun t =>
    observedColumn_min_eq_one_of_frozenLeftEdge f60 hq60 (by decide) (by decide) (by decide) _ _ t⟩

/-- **Guard: the hypothesis `h010` is load-bearing.** Rule `90` fails `h010` (a set cell with clear
neighbours on both sides clears) and at the single seed the seed's own cell, the leftmost set cell,
reads `0` at time `1`. -/
theorem observedColumn_min_frozenLeftEdge_guard :
    observedColumn (finRule f90 hq90) (Finsupp.single 0 1) 0 1 = 0 := by
  rw [observedColumn_f90_single]
  simp

/-! ## A rule that does not read one neighbour -/

private theorem zero_beyond_support_above_aux (s₀ : FiniteConfiguration) :
    ∃ M : ℤ, ∀ k : ℤ, M < k → s₀ k = 0 := by
  obtain ⟨M, hM⟩ := s₀.support.bddAbove
  refine ⟨M, fun k hk => ?_⟩
  by_contra hc
  have := hM (Finsupp.mem_support_iff.mpr hc)
  omega

private theorem zero_beyond_support_below_aux (s₀ : FiniteConfiguration) :
    ∃ M : ℤ, ∀ k : ℤ, k < M → s₀ k = 0 := by
  obtain ⟨M, hM⟩ := s₀.support.bddBelow
  refine ⟨M, fun k hk => ?_⟩
  by_contra hc
  have := hM (Finsupp.mem_support_iff.mpr hc)
  omega

/-- A rule that does not read its left neighbour keeps every cell right of a bound clear when the
seed is clear there. -/
private theorem iterate_eq_zero_of_left_unread_aux (f : LocalRule) (hq : f 0 0 0 = 0)
    (hf : ∀ l c r, f l c r = f 0 c r) (s₀ : FiniteConfiguration) {M : ℤ}
    (hM : ∀ k, M < k → s₀ k = 0) (t : ℕ) :
    ∀ j, M < j → ((finRule f hq)^[t] s₀) j = 0 := by
  induction t with
  | zero => exact fun j hj => hM j hj
  | succ t ih =>
    intro j hj
    rw [Function.iterate_succ_apply', finRule_apply, hf, ih j hj, ih (j + 1) (by omega), hq]

/-- A rule that does not read its right neighbour keeps every cell left of a bound clear when the
seed is clear there. -/
private theorem iterate_eq_zero_of_right_unread_aux (f : LocalRule) (hq : f 0 0 0 = 0)
    (hf : ∀ l c r, f l c r = f l c 0) (s₀ : FiniteConfiguration) {M : ℤ}
    (hM : ∀ k, k < M → s₀ k = 0) (t : ℕ) :
    ∀ j, j < M → ((finRule f hq)^[t] s₀) j = 0 := by
  induction t with
  | zero => exact fun j hj => hM j hj
  | succ t ih =>
    intro j hj
    rw [Function.iterate_succ_apply', finRule_apply, hf, ih j hj, ih (j - 1) (by omega), hq]

/-- Eventual periodicity of the column at `i`, by induction on the distance of `i` below the bound,
at a rule that does not read its left neighbour. -/
private theorem eventuallyPeriodic_observedColumn_left_unread_aux (f : LocalRule)
    (hq : f 0 0 0 = 0) (hf : ∀ l c r, f l c r = f 0 c r) (s₀ : FiniteConfiguration) {M : ℤ}
    (hM : ∀ k, M < k → s₀ k = 0) (n : ℕ) :
    ∀ i : ℤ, M < i + n →
      DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) s₀ i) := by
  induction n with
  | zero =>
    intro i hi
    have hz : ∀ t, observedColumn (finRule f hq) s₀ i t = 0 := fun t =>
      iterate_eq_zero_of_left_unread_aux f hq hf s₀ hM t i (by simpa using hi)
    exact ⟨1, 0, one_pos, fun u _ => by rw [hz (u + 1), hz u]⟩
  | succ n ih =>
    intro i hi
    have h1 := ih (i + 1) (by omega)
    refine DrivenColumns.eventuallyPeriodic_of_driven (fun a u => f 0 a u) h1 ⟨0, fun t _ => ?_⟩
    change ((finRule f hq)^[t + 1] s₀) i =
      f 0 (((finRule f hq)^[t] s₀) i) (((finRule f hq)^[t] s₀) (i + 1))
    rw [Function.iterate_succ_apply', finRule_apply, hf]

/-- Eventual periodicity of the column at `i`, by induction on the distance of `i` above the bound,
at a rule that does not read its right neighbour. -/
private theorem eventuallyPeriodic_observedColumn_right_unread_aux (f : LocalRule)
    (hq : f 0 0 0 = 0) (hf : ∀ l c r, f l c r = f l c 0) (s₀ : FiniteConfiguration) {M : ℤ}
    (hM : ∀ k, k < M → s₀ k = 0) (n : ℕ) :
    ∀ i : ℤ, i - n < M →
      DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) s₀ i) := by
  induction n with
  | zero =>
    intro i hi
    have hz : ∀ t, observedColumn (finRule f hq) s₀ i t = 0 := fun t =>
      iterate_eq_zero_of_right_unread_aux f hq hf s₀ hM t i (by simpa using hi)
    exact ⟨1, 0, one_pos, fun u _ => by rw [hz (u + 1), hz u]⟩
  | succ n ih =>
    intro i hi
    have h1 := ih (i - 1) (by omega)
    refine DrivenColumns.eventuallyPeriodic_of_driven (fun a u => f u a 0) h1 ⟨0, fun t _ => ?_⟩
    change ((finRule f hq)^[t + 1] s₀) i =
      f (((finRule f hq)^[t] s₀) (i - 1)) (((finRule f hq)^[t] s₀) i) 0
    rw [Function.iterate_succ_apply', finRule_apply, hf]

/-- **A rule that does not read its left neighbour has every observed column eventually periodic**
([RuleSpace] §4 Proposition 4.2): right of the seed's support every cell is clear at every time, so
that column is constant, and the column at a cell is driven by the column at the cell to its right
through `a ↦ f 0 a u`, which `DrivenColumns.eventuallyPeriodic_of_driven` carries one cell to the
left at a time. It holds for every finite seed and every cell, the zero seed included. -/
theorem eventuallyPeriodic_observedColumn_of_left_unread (f : LocalRule) (hq : f 0 0 0 = 0)
    (hf : ∀ l c r, f l c r = f 0 c r) (s₀ : FiniteConfiguration) (i : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) s₀ i) := by
  obtain ⟨M, hM⟩ := zero_beyond_support_above_aux s₀
  exact eventuallyPeriodic_observedColumn_left_unread_aux f hq hf s₀ hM ((M - i).toNat + 1) i
    (by omega)

/-- **A rule that does not read its right neighbour has every observed column eventually
periodic** ([RuleSpace] §4 Proposition 4.2): the mirror argument of
`eventuallyPeriodic_observedColumn_of_left_unread`, from the cells left of the support, proved in
full. -/
theorem eventuallyPeriodic_observedColumn_of_right_unread (f : LocalRule) (hq : f 0 0 0 = 0)
    (hf : ∀ l c r, f l c r = f l c 0) (s₀ : FiniteConfiguration) (i : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) s₀ i) := by
  obtain ⟨M, hM⟩ := zero_beyond_support_below_aux s₀
  exact eventuallyPeriodic_observedColumn_right_unread_aux f hq hf s₀ hM ((i - M).toNat + 1) i
    (by omega)

/-- **Rule `102` instance**: `b + c` does not read the left neighbour, so every observed column from
every finite seed is eventually periodic. -/
theorem eventuallyPeriodic_observedColumn_f102 (s₀ : FiniteConfiguration) (i : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f102 hq102) s₀ i) :=
  eventuallyPeriodic_observedColumn_of_left_unread f102 hq102 (fun _ _ _ => rfl) s₀ i

/-- **Rule `60` instance**: `a + b` does not read the right neighbour, so every observed column from
every finite seed is eventually periodic. -/
theorem eventuallyPeriodic_observedColumn_f60 (s₀ : FiniteConfiguration) (i : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f60 hq60) s₀ i) :=
  eventuallyPeriodic_observedColumn_of_right_unread f60 hq60 (fun _ _ _ => rfl) s₀ i

/-! ## A mirror-symmetric seed at a mirror-symmetric rule -/

/-- **Mirror symmetry is kept by a mirror-symmetric rule**: if the seed reads the same at `c + i`
and `c - i` for every `i`, so does every iterate. -/
theorem finRule_iterate_mirror (f : LocalRule) (hq : f 0 0 0 = 0)
    (hsym : ∀ l c r, f l c r = f r c l) (s₀ : FiniteConfiguration) (c : ℤ)
    (hs : ∀ i, s₀ (c + i) = s₀ (c - i)) (t : ℕ) (i : ℤ) :
    ((finRule f hq)^[t] s₀) (c + i) = ((finRule f hq)^[t] s₀) (c - i) := by
  induction t generalizing i with
  | zero => exact hs i
  | succ t ih =>
    rw [Function.iterate_succ_apply', finRule_apply, finRule_apply]
    have e1 := ih (i - 1)
    have e2 := ih (i + 1)
    have e3 := ih i
    rw [show c + (i - 1) = c + i - 1 by ring, show c - (i - 1) = c - i + 1 by ring] at e1
    rw [show c + (i + 1) = c + i + 1 by ring, show c - (i + 1) = c - i - 1 by ring] at e2
    rw [e1, e2, e3]
    exact hsym _ _ _

/-- **The centre of a mirror-symmetric seed at rule `90` reads clear from time one on**: the two
neighbours of the centre agree at every time, and rule `90` sums them. -/
theorem observedColumn_f90_eq_zero_of_mirror (s₀ : FiniteConfiguration) (c : ℤ)
    (hs : ∀ i, s₀ (c + i) = s₀ (c - i)) (t : ℕ) :
    observedColumn (finRule f90 hq90) s₀ c (t + 1) = 0 := by
  have hsym : ∀ l c r, f90 l c r = f90 r c l := by decide
  have hm := finRule_iterate_mirror f90 hq90 hsym s₀ c hs t 1
  have hzero : ∀ x : ZMod 2, x + x = 0 := by decide
  change ((finRule f90 hq90)^[t + 1] s₀) c = 0
  rw [Function.iterate_succ_apply', finRule_apply]
  change ((finRule f90 hq90)^[t] s₀) (c - 1) + ((finRule f90 hq90)^[t] s₀) (c + 1) = 0
  rw [hm]
  exact hzero _

/-- **The centre of a mirror-symmetric seed at rule `150` keeps its value**: the two neighbours of
the centre agree at every time, and rule `150` adds them to the centre. -/
theorem observedColumn_f150_eq_of_mirror (s₀ : FiniteConfiguration) (c : ℤ)
    (hs : ∀ i, s₀ (c + i) = s₀ (c - i)) (t : ℕ) :
    observedColumn (finRule f150 hq150) s₀ c t = s₀ c := by
  have hsym : ∀ l c r, f150 l c r = f150 r c l := by decide
  have hxyx : ∀ x y : ZMod 2, x + y + x = y := by decide
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := finRule_iterate_mirror f150 hq150 hsym s₀ c hs t 1
    have ih' : ((finRule f150 hq150)^[t] s₀) c = s₀ c := ih
    change ((finRule f150 hq150)^[t + 1] s₀) c = s₀ c
    rw [Function.iterate_succ_apply', finRule_apply]
    change ((finRule f150 hq150)^[t] s₀) (c - 1) + ((finRule f150 hq150)^[t] s₀) c +
      ((finRule f150 hq150)^[t] s₀) (c + 1) = s₀ c
    rw [hm, ih']
    exact hxyx _ _

/-- **Rule `90` from a mirror-symmetric seed: the centre column is eventually periodic**, clear
from time one on. -/
theorem eventuallyPeriodic_observedColumn_f90_of_mirror (s₀ : FiniteConfiguration) (c : ℤ)
    (hs : ∀ i, s₀ (c + i) = s₀ (c - i)) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f90 hq90) s₀ c) :=
  ⟨1, 1, one_pos, fun u hu => by
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    rw [observedColumn_f90_eq_zero_of_mirror s₀ c hs (v + 1),
      observedColumn_f90_eq_zero_of_mirror s₀ c hs v]⟩

/-- **Rule `150` from a mirror-symmetric seed: the centre column is eventually periodic**, constant
at the seed's value. -/
theorem eventuallyPeriodic_observedColumn_f150_of_mirror (s₀ : FiniteConfiguration) (c : ℤ)
    (hs : ∀ i, s₀ (c + i) = s₀ (c - i)) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f150 hq150) s₀ c) :=
  ⟨1, 0, one_pos, fun u _ => by
    rw [observedColumn_f150_eq_of_mirror s₀ c hs (u + 1),
      observedColumn_f150_eq_of_mirror s₀ c hs u]⟩

/-- The joint-satisfiability witness for `finRule_iterate_mirror`: rule `90` is mirror symmetric,
the single seed is mirror symmetric about its own cell, and the iterate is not the zero
configuration: after one step the cell `1` reads `1`. -/
theorem finRule_iterate_mirror_nonvacuous :
    (∀ l c r, f90 l c r = f90 r c l) ∧
      (∀ i : ℤ, (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (0 + i) =
        (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (0 - i)) ∧
      ((finRule f90 hq90)^[1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (0 + 1) = 1 := by
  refine ⟨by decide, fun i => ?_, ?_⟩
  · simp only [Finsupp.single_apply, zero_add, zero_sub, eq_comm (a := (0 : ℤ)), neg_eq_zero]
  · simp [finRule_apply, f90]

end ECA

/-! ## Axiom audit -/

set_option linter.style.longLine false in
/-- info: 'ECA.observedColumn_min_eq_one_of_frozenLeftEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedColumn_min_eq_one_of_frozenLeftEdge

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_min_of_frozenLeftEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_min_of_frozenLeftEdge

set_option linter.style.longLine false in
/-- info: 'ECA.observedColumn_min_eq_one_of_frozenLeftEdge_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedColumn_min_eq_one_of_frozenLeftEdge_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.observedColumn_min_frozenLeftEdge_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedColumn_min_frozenLeftEdge_guard

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_of_left_unread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_of_left_unread

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_of_right_unread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_of_right_unread

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_f102' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_f102

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_f60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_f60

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_iterate_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_iterate_mirror

set_option linter.style.longLine false in
/-- info: 'ECA.observedColumn_f90_eq_zero_of_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedColumn_f90_eq_zero_of_mirror

set_option linter.style.longLine false in
/-- info: 'ECA.observedColumn_f150_eq_of_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedColumn_f150_eq_of_mirror

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_f90_of_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_f90_of_mirror

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_f150_of_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_f150_of_mirror

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_iterate_mirror_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_iterate_mirror_nonvacuous
