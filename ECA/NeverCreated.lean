module

public import ECA.DefectCounts
public import ECA.Doubling
public import ECA.ObservedColumn
import all ECA.DefectCounts

/-!
# A word never created in place, and the patterns it keeps a rule from reproducing
([RuleSpace] §5)

[RuleSpace] §5 Proposition 5.27(i) excludes the reproduction of a pattern by a count that one step
never increases and that copies carry. This module gives such a count for a rule that never creates
a word in place: the number of occurrences of a word `w` whose end letters are set.

* `FiniteConfiguration.Reads` / `FiniteConfiguration.occurrences` / `FiniteConfiguration.occCount`
  — a state reads `w` at a cell, the cells where it does, and their number.
* `LocalRule.NeverCreatedInPlace` — every occurrence of `w` in the image of a state sits over an
  occurrence of `w` in the state, at the same cell.
* `occCount_copies` — `k` copies of a pattern carry at least `k` times its occurrences of `w`, at
  every gap.
* `LocalRule.NeverCreatedInPlace.not_reproduces` — **the exclusion**: a rule that never creates `w`
  in place reproduces no pattern that reads `w`.
* `neverCreatedInPlace_f22_10101` — rule `22` never creates the word `10101` in place, of the 128
  windows of seven cells exactly `0101010` having an image that reads `10101` at its middle five
  cells; hence `not_reproduces_f22_of_reads_10101`: rule `22` reproduces no pattern reading `10101`,
  among them `p110101` (`not_reproduces_f22_110101`), whose orbit never meets a state of one parity
  (`not_oneParity_iterate_f22_110101`), so that [RuleSpace] §5 Proposition 5.40 does not decide it.
  `neverCreatedInPlace_f22_10101_load_bearing` shows the property fails at rule `90`, where the
  pattern `p10001` steps to a state reading `10101` twice.
* `FiniteConfiguration.diam_finRule_eq_add_two` / `FiniteConfiguration.diam_iterate_finRule` — at a
  rule with both taps the diameter of a nonzero state grows by two a step;
  `diam_finRule_eq_add_two_load_bearing` shows neither tap can be dropped.
* `FiniteConfiguration.OneParity.odd_diam` / `not_oneParity_iterate_of_even_diam` — a nonzero state
  of one parity has odd diameter, so no iterate of a nonzero state of even diameter is of one
  parity at a rule with both taps.

The word's end letters being set is what lets copies carry the count: an occurrence stays inside
the hull of its copy, where the other copies vanish.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## Occurrences of a word -/

/-- **A state reads a word at a cell**: the cells `i, i + 1, …, i + w.length - 1` of `s` carry the
letters of `w`. -/
def FiniteConfiguration.Reads (s : FiniteConfiguration) (w : List (ZMod 2)) (i : ℤ) : Prop :=
  ∀ k : ℕ, k < w.length → s (i + k) = w.getD k 0

/-- Reading a word at a cell is decidable, the cells read being finitely many. -/
instance FiniteConfiguration.decidableReads (s : FiniteConfiguration) (w : List (ZMod 2))
    (i : ℤ) : Decidable (s.Reads w i) := by
  unfold FiniteConfiguration.Reads
  infer_instance

/-- **The occurrences of a word in a state**: the set cells at which the state reads the word. For a
word whose first letter is set these are all the cells where it is read. -/
def FiniteConfiguration.occurrences (s : FiniteConfiguration) (w : List (ZMod 2)) : Finset ℤ :=
  s.support.filter fun i => s.Reads w i

/-- **The number of occurrences of a word in a state**. -/
def FiniteConfiguration.occCount (s : FiniteConfiguration) (w : List (ZMod 2)) : ℕ :=
  (s.occurrences w).card

/-- A cell is an occurrence when it is set and the state reads the word there. -/
theorem FiniteConfiguration.mem_occurrences {s : FiniteConfiguration} {w : List (ZMod 2)} {i : ℤ} :
    i ∈ s.occurrences w ↔ s i ≠ 0 ∧ s.Reads w i := by
  simp [FiniteConfiguration.occurrences]

/-- **A rule never creates a word in place** when every occurrence of the word in the image of a
state sits over an occurrence of it in the state, at the same cell. -/
def LocalRule.NeverCreatedInPlace (f : LocalRule) (hq : f 0 0 0 = 0) (w : List (ZMod 2)) : Prop :=
  ∀ (s : FiniteConfiguration) (i : ℤ), (finRule f hq s).Reads w i → s.Reads w i

private theorem head_getD {w : List (ZMod 2)} (hw : w.head? = some 1) :
    0 < w.length ∧ w.getD 0 0 = 1 := by
  cases w with
  | nil => simp at hw
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hw
    subst hw
    simp

private theorem last_getD {w : List (ZMod 2)} (hl : w.getLast? = some 1) :
    0 < w.length ∧ w.getD (w.length - 1) 0 = 1 := by
  rw [List.getLast?_eq_getElem?] at hl
  have hpos : 0 < w.length := by
    by_contra h
    have : w.length = 0 := by omega
    simp [this] at hl
  refine ⟨hpos, ?_⟩
  simp [List.getD_eq_getElem?_getD, hl]

/-- A state reading a word whose first letter is set has a set cell where it reads. -/
private theorem ne_zero_of_reads {s : FiniteConfiguration} {w : List (ZMod 2)} {i : ℤ}
    (hw : w.head? = some 1) (h : s.Reads w i) : s i ≠ 0 := by
  obtain ⟨hpos, h1⟩ := head_getD hw
  have := h 0 hpos
  rw [h1] at this
  simp only [Nat.cast_zero, add_zero] at this
  rw [this]
  exact one_ne_zero

/-- **The occurrences of the image sit among those of the state**: a rule that never creates a
word whose first letter is set in place has its image's occurrences inside the state's. -/
theorem LocalRule.NeverCreatedInPlace.occurrences_subset {f : LocalRule} {hq : f 0 0 0 = 0}
    {w : List (ZMod 2)} (hw : w.head? = some 1) (h : NeverCreatedInPlace f hq w)
    (s : FiniteConfiguration) : (finRule f hq s).occurrences w ⊆ s.occurrences w := by
  intro i hi
  rw [mem_occurrences] at hi ⊢
  have hr := h s i hi.2
  exact ⟨ne_zero_of_reads hw hr, hr⟩

/-- **One step never increases the number of occurrences** of a word whose first letter is set that
the rule never creates in place. -/
theorem LocalRule.NeverCreatedInPlace.occCount_finRule_le {f : LocalRule} {hq : f 0 0 0 = 0}
    {w : List (ZMod 2)} (hw : w.head? = some 1) (h : NeverCreatedInPlace f hq w)
    (s : FiniteConfiguration) : (finRule f hq s).occCount w ≤ s.occCount w :=
  Finset.card_le_card (h.occurrences_subset hw s)

/-! ## Copies carry the count -/

/-- **`k` copies of a pattern carry at least `k` times its occurrences of a word whose end letters
are set**, at every gap: an occurrence in the pattern lies in the hull of the pattern, between two
set cells, where the other copies vanish, so its translate by each copy's offset is an occurrence
of the sum, and distinct copies give distinct cells. -/
theorem occCount_copies {w : List (ZMod 2)} (hh : w.head? = some 1) (hl : w.getLast? = some 1)
    {p s : FiniteConfiguration} {k G : ℕ} (h : Copies p s k G) :
    k * p.occCount w ≤ s.occCount w := by
  obtain ⟨c, hc, rfl⟩ := h
  by_cases hp : p = 0
  · subst hp
    simp [FiniteConfiguration.occCount, FiniteConfiguration.occurrences]
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmM := Finset.min'_le_max' p.support hpne
  have hd : (diam p : ℤ) = p.support.max' hpne - p.support.min' hpne + 1 := by
    unfold diam
    rw [dite_eq_left hpne]
    omega
  obtain ⟨hpos, hlast⟩ := last_getD hl
  -- an occurrence of `p` has its cells inside the hull of `p`
  have hull : ∀ i, p.Reads w i →
      p.support.min' hpne ≤ i ∧ i + ((w.length : ℤ) - 1) ≤ p.support.max' hpne := by
    intro i hi
    have h0 := ne_zero_of_reads hh hi
    have h1 : p (i + ((w.length - 1 : ℕ) : ℤ)) ≠ 0 := by
      rw [hi _ (by omega), hlast]
      exact one_ne_zero
    refine ⟨Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr h0), ?_⟩
    have := Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr h1)
    push_cast [Nat.cast_sub hpos] at this
    omega
  unfold FiniteConfiguration.occCount
  have hcard : k * (p.occurrences w).card = (Finset.range k ×ˢ p.occurrences w).card := by
    rw [Finset.card_product, Finset.card_range]
  rw [hcard]
  refine Finset.card_le_card_of_injOn (fun x => x.2 + c x.1) (fun x hx => ?_)
    (fun x hx y hy he => ?_)
  · obtain ⟨hj, hi⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
    have hj' := Finset.mem_range.mp hj
    obtain ⟨_, hr⟩ := mem_occurrences.mp hi
    obtain ⟨hb1, hb2⟩ := hull _ hr
    have hread : (Finset.sum (Finset.range k) fun j => translate (c j) p).Reads w
        (x.2 + c x.1) := by
      intro k' hk'
      have e := copies_apply hpne hc (g := 0) (Nat.zero_le _) hj' (x := x.2 + k')
        (by simp only [Nat.cast_zero, sub_zero]; omega)
        (by simp only [Nat.cast_zero, add_zero]; omega)
      rw [show x.2 + c x.1 + (k' : ℤ) = x.2 + k' + c x.1 by ring, e]
      exact hr k' hk'
    rw [Finset.mem_coe]
    exact mem_occurrences.mpr ⟨ne_zero_of_reads hh hread, hread⟩
  · obtain ⟨hj, hi⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
    obtain ⟨hj2, hi2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hy)
    have hj' := Finset.mem_range.mp hj
    have hj2' := Finset.mem_range.mp hj2
    obtain ⟨hb1, hb2⟩ := hull _ (mem_occurrences.mp hi).2
    obtain ⟨hb3, hb4⟩ := hull _ (mem_occurrences.mp hi2).2
    simp only at he
    have hq1 : x.1 = y.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := copies_ord hc hlt hj2'
        omega
      · have := copies_ord hc hgt hj'
        omega
    have : x.2 = y.2 := by rw [hq1] at he; omega
    exact Prod.ext hq1 this

/-! ## The exclusion -/

/-- **A rule that never creates a word in place reproduces no pattern reading it**
([RuleSpace] §5 Proposition 5.27(i) with the number of occurrences as the count): a word whose end
letters are set, never created in place by the rule, has an occurrence count that one step never
increases and that copies carry, so a pattern with an occurrence is not reproduced. -/
theorem LocalRule.NeverCreatedInPlace.not_reproduces {f : LocalRule} {hq : f 0 0 0 = 0}
    {w : List (ZMod 2)} (hh : w.head? = some 1) (hl : w.getLast? = some 1)
    (h : NeverCreatedInPlace f hq w) {p : FiniteConfiguration} (hp : 1 ≤ p.occCount w) :
    ¬ Reproduces (finRule f hq) p :=
  not_reproduces_of_count_mono (finRule f hq) (fun s => s.occCount w)
    (fun s => h.occCount_finRule_le hh s) (fun _ _ _ _ _ hc => occCount_copies hh hl hc) hp

/-! ## Rule `22` never creates the word `10101` in place -/

/-- A state reads a word of five letters at a cell exactly when its five cells there are the
letters. -/
private theorem reads_five {s : FiniteConfiguration} {a b c d e : ZMod 2} {i : ℤ} :
    s.Reads [a, b, c, d, e] i ↔
      s i = a ∧ s (i + 1) = b ∧ s (i + 2) = c ∧ s (i + 3) = d ∧ s (i + 4) = e := by
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp),
      by simpa using h 2 (by simp), by simpa using h 3 (by simp), by simpa using h 4 (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [h0, h1, h2, h3, h4]

set_option synthInstance.maxSize 256 in
-- the `Decidable` instance for a universal over seven cells and a seven-fold conclusion needs the
-- larger synthesis size.
/-- **The finite statement**: of the 128 windows of seven cells, the only one whose image under
rule `22` reads `10101` at its middle five cells is `0101010`. -/
private theorem f22_window (a0 a1 a2 a3 a4 a5 a6 : ZMod 2) (h0 : f22 a0 a1 a2 = 1)
    (h1 : f22 a1 a2 a3 = 0) (h2 : f22 a2 a3 a4 = 1) (h3 : f22 a3 a4 a5 = 0)
    (h4 : f22 a4 a5 a6 = 1) :
    a0 = 0 ∧ a1 = 1 ∧ a2 = 0 ∧ a3 = 1 ∧ a4 = 0 ∧ a5 = 1 ∧ a6 = 0 := by
  revert a0 a1 a2 a3 a4 a5 a6
  decide

/-- **Rule `22` never creates the word `10101` in place**: of the 128 windows of seven cells exactly
`0101010` has an image reading `10101` at its middle five cells, so every occurrence of `10101` in
the image sits over an occurrence in the state at the same cell. -/
theorem neverCreatedInPlace_f22_10101 : NeverCreatedInPlace f22 hq22 [1, 0, 1, 0, 1] := by
  intro s i h
  rw [reads_five] at h ⊢
  obtain ⟨e0, e1, e2, e3, e4⟩ := h
  simp only [finRule_apply] at e0 e1 e2 e3 e4
  have := f22_window (s (i - 1)) (s i) (s (i + 1)) (s (i + 2)) (s (i + 3)) (s (i + 4)) (s (i + 5))
    e0 (by convert e1 using 3 <;> ring_nf) (by convert e2 using 3 <;> ring_nf)
    (by convert e3 using 3 <;> ring_nf) (by convert e4 using 3 <;> ring_nf)
  exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1⟩

/-- **Rule `22` reproduces no pattern that reads `10101`**
([RuleSpace] §5 Proposition 5.27(i)), the word being never created in place. -/
theorem not_reproduces_f22_of_reads_10101 (p : FiniteConfiguration) (i : ℤ)
    (h : p.Reads [1, 0, 1, 0, 1] i) : ¬ Reproduces (finRule f22 hq22) p := by
  refine neverCreatedInPlace_f22_10101.not_reproduces rfl rfl ?_
  exact Finset.card_pos.mpr ⟨i, mem_occurrences.mpr ⟨ne_zero_of_reads rfl h, h⟩⟩

/-- **The pattern `110101`**: the set cells `0`, `1`, `3` and `5`, of diameter `6`. It reads `10101`
at the cell `1`. -/
noncomputable def p110101 : FiniteConfiguration :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1 + Finsupp.single 5 1

private theorem p110101_apply (x : ℤ) :
    p110101 x = if x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 5 then 1 else 0 := by
  simp only [p110101, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : x = 1
  · simp [h1]
  by_cases h3 : x = 3
  · simp [h3]
  by_cases h5 : x = 5
  · simp [h5]
  simp [h0, h1, h3, h5, Ne.symm h0, Ne.symm h1, Ne.symm h3, Ne.symm h5]

/-- The pattern `110101` is nonzero. -/
private theorem p110101_ne_zero : p110101 ≠ 0 := by
  intro h
  have := congrArg (fun s => s 0) h
  simp [p110101_apply] at this

/-- The pattern `110101` has diameter `6`. -/
theorem diam_p110101 : diam p110101 = 6 := by
  have hne : p110101.support.Nonempty := Finsupp.support_nonempty_iff.mpr p110101_ne_zero
  have hmem : ∀ x, x ∈ p110101.support ↔ x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 5 := by
    intro x
    rw [Finsupp.mem_support_iff, p110101_apply]
    split_ifs with h <;> simp [h]
  have hmin : p110101.support.min' hne = 0 := by
    rw [Finset.min'_eq_iff]
    refine ⟨(hmem 0).mpr (by simp), fun b hb => ?_⟩
    rcases (hmem b).mp hb with h | h | h | h <;> omega
  have hmax : p110101.support.max' hne = 5 := by
    rw [Finset.max'_eq_iff]
    refine ⟨(hmem 5).mpr (by simp), fun b hb => ?_⟩
    rcases (hmem b).mp hb with h | h | h | h <;> omega
  unfold diam
  rw [dite_eq_left hne, hmin, hmax]
  rfl

/-- The pattern `110101` reads `10101` at the cell `1`. -/
private theorem reads_p110101 : p110101.Reads [1, 0, 1, 0, 1] 1 := by
  rw [reads_five]
  simp [p110101_apply]

/-- **Rule `22` does not reproduce the pattern `110101`**, which reads `10101` at its cell `1`. -/
theorem not_reproduces_f22_110101 : ¬ Reproduces (finRule f22 hq22) p110101 :=
  not_reproduces_f22_of_reads_10101 p110101 1 reads_p110101

/-! ## The exclusion's hypotheses are met at once, and the property fails at rule `90` -/

/-- A state with a read of a word whose first letter is set has at least one occurrence of it. -/
private theorem one_le_occCount_of_reads {s : FiniteConfiguration} {w : List (ZMod 2)} {i : ℤ}
    (hw : w.head? = some 1) (h : s.Reads w i) : 1 ≤ s.occCount w :=
  Finset.card_pos.mpr ⟨i, mem_occurrences.mpr ⟨ne_zero_of_reads hw h, h⟩⟩

/-- **The exclusion has a fixed instance meeting its four hypotheses**: rule `22`, the word `10101`
and the pattern `110101`, which reads it. -/
theorem LocalRule.NeverCreatedInPlace.not_reproduces_nonvacuous :
    ∃ p : FiniteConfiguration, ([1, 0, 1, 0, 1] : List (ZMod 2)).head? = some 1 ∧
      ([1, 0, 1, 0, 1] : List (ZMod 2)).getLast? = some 1 ∧
      NeverCreatedInPlace f22 hq22 [1, 0, 1, 0, 1] ∧ 1 ≤ p.occCount [1, 0, 1, 0, 1] ∧
      ¬ Reproduces (finRule f22 hq22) p :=
  ⟨p110101, rfl, rfl, neverCreatedInPlace_f22_10101, one_le_occCount_of_reads rfl reads_p110101,
    not_reproduces_f22_110101⟩

/-- **The pattern `10001`**: the set cells `0` and `4`. It reads `10101` nowhere. -/
noncomputable def p10001 : FiniteConfiguration := Finsupp.single 0 1 + Finsupp.single 4 1

private theorem p10001_apply (x : ℤ) : p10001 x = if x = 0 ∨ x = 4 then 1 else 0 := by
  simp only [p10001, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h4 : x = 4
  · simp [h4]
  simp [h0, h4, Ne.symm h0, Ne.symm h4]

/-- One step of rule `90` on `10001` sets the cells `-1`, `1`, `3` and `5`. -/
private theorem finRule_f90_p10001_apply (x : ℤ) :
    finRule f90 hq90 p10001 x = if x = -1 ∨ x = 1 ∨ x = 3 ∨ x = 5 then 1 else 0 := by
  rw [finRule_apply, p10001_apply, p10001_apply, p10001_apply]
  simp only [f90]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The occurrences of `10101` in a state given by the set cells satisfying a predicate: the cells
where the predicate holds, fails, holds, fails and holds again. -/
private theorem mem_occurrences_of_apply {q : FiniteConfiguration} {P : ℤ → Prop}
    [DecidablePred P] (hq : ∀ x, q x = if P x then 1 else 0) {i : ℤ} :
    i ∈ q.occurrences [1, 0, 1, 0, 1] ↔
      P i ∧ ¬ P (i + 1) ∧ P (i + 2) ∧ ¬ P (i + 3) ∧ P (i + 4) := by
  rw [mem_occurrences, reads_five]
  simp only [hq, ne_eq]
  by_cases h0 : P i <;> by_cases h1 : P (i + 1) <;> by_cases h2 : P (i + 2) <;>
    by_cases h3 : P (i + 3) <;> by_cases h4 : P (i + 4) <;> simp [h0, h1, h2, h3, h4]

/-- **The property is load-bearing in the rule**: at rule `90` the word `10101` is created in place.
One step takes the pattern `10001`, which reads it nowhere, to `1010101` on the cells `-1 … 5`,
which reads it at the cells `-1` and `1`. -/
theorem neverCreatedInPlace_f22_10101_load_bearing :
    ¬ NeverCreatedInPlace f90 hq90 [1, 0, 1, 0, 1] ∧
      (finRule f90 hq90 p10001).occCount [1, 0, 1, 0, 1] = 2 ∧
      p10001.occCount [1, 0, 1, 0, 1] = 0 := by
  have h2 : (finRule f90 hq90 p10001).occCount [1, 0, 1, 0, 1] = 2 := by
    have : (finRule f90 hq90 p10001).occurrences [1, 0, 1, 0, 1] = {-1, 1} := by
      ext i
      rw [mem_occurrences_of_apply finRule_f90_p10001_apply]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [FiniteConfiguration.occCount, this]
    decide
  have h0 : p10001.occCount [1, 0, 1, 0, 1] = 0 := by
    have : p10001.occurrences [1, 0, 1, 0, 1] = ∅ := by
      ext i
      rw [mem_occurrences_of_apply p10001_apply]
      simp only [Finset.notMem_empty, iff_false]
      omega
    rw [FiniteConfiguration.occCount, this]
    rfl
  refine ⟨fun h => ?_, h2, h0⟩
  have := h.occCount_finRule_le rfl p10001
  omega

/-! ## The ends of a rule with both taps -/

section BothTaps

variable {f : LocalRule} {hq : f 0 0 0 = 0}

/-- **A rule with both taps widens a nonzero state by two cells**: with `f 0 0 1 = 1` the leftmost
set cell of the image is one cell left of the state's, and with `f 1 0 0 = 1` the rightmost is one
cell right of it. -/
theorem FiniteConfiguration.diam_finRule_eq_add_two (h1 : f 0 0 1 = 1) (h2 : f 1 0 0 = 1)
    {s : FiniteConfiguration} (hs : s ≠ 0) : diam (finRule f hq s) = diam s + 2 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hne' : (finRule f hq s).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (finRule_ne_zero_of_leftTap (hq := hq) h1 hs)
  have hmM := Finset.min'_le_max' s.support hne
  unfold diam
  rw [dite_eq_left hne, dite_eq_left hne', finRule_min'_of_leftTap (hq := hq) h1 hne hne',
    finRule_max'_of_rightTap (hq := hq) h2 hne hne']
  omega

/-- The iterates of a nonzero state stay nonzero at a rule with the left tap. -/
private theorem iterate_ne_zero_of_leftTap (h1 : f 0 0 1 = 1) {s : FiniteConfiguration}
    (hs : s ≠ 0) (t : ℕ) : (finRule f hq)^[t] s ≠ 0 := by
  induction t with
  | zero => simpa using hs
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact finRule_ne_zero_of_leftTap (hq := hq) h1 ih

/-- **At a rule with both taps the diameter of a nonzero state grows by two a step**. -/
theorem FiniteConfiguration.diam_iterate_finRule (h1 : f 0 0 1 = 1) (h2 : f 1 0 0 = 1)
    {s : FiniteConfiguration} (hs : s ≠ 0) (t : ℕ) :
    diam ((finRule f hq)^[t] s) = diam s + 2 * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', diam_finRule_eq_add_two (hq := hq) h1 h2
      (iterate_ne_zero_of_leftTap h1 hs t), ih]
    ring

/-- **A nonzero state of one parity has odd diameter**: its leftmost and rightmost set cells differ
by an even amount. -/
theorem FiniteConfiguration.OneParity.odd_diam {s : FiniteConfiguration} (hs : s ≠ 0)
    (h : OneParity s) : Odd (diam s) := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hmM := Finset.min'_le_max' s.support hne
  have he := h _ _ (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hne))
    (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hne))
  unfold diam
  rw [dite_eq_left hne]
  rw [Int.even_iff] at he
  rw [Nat.odd_iff]
  omega

/-- **No iterate of a nonzero state of even diameter is of one parity** at a rule with both taps:
the diameter stays even, and a nonzero state of one parity has odd diameter. -/
theorem not_oneParity_iterate_of_even_diam (h1 : f 0 0 1 = 1) (h2 : f 1 0 0 = 1)
    {s : FiniteConfiguration} (hs : s ≠ 0) (he : Even (diam s)) (t : ℕ) :
    ¬ OneParity ((finRule f hq)^[t] s) := by
  intro h
  have hodd := h.odd_diam (iterate_ne_zero_of_leftTap h1 hs t)
  rw [diam_iterate_finRule (hq := hq) h1 h2 hs t] at hodd
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff] at hodd
  omega

end BothTaps

/-- **The instance at rule `22`**, whose two taps `f22 0 0 1 = 1` and `f22 1 0 0 = 1` are set. -/
theorem not_oneParity_iterate_f22_of_even_diam {s : FiniteConfiguration} (hs : s ≠ 0)
    (he : Even (diam s)) (t : ℕ) : ¬ OneParity ((finRule f22 hq22)^[t] s) :=
  not_oneParity_iterate_of_even_diam (by decide) (by decide) hs he t

/-- **No iterate of `110101` is of one parity at rule `22`**: its diameter `6` is even. Together
with `not_reproduces_f22_110101` this is a pattern that rule `22` does not reproduce and that
[RuleSpace] §5 Proposition 5.40's one-parity cases do not reach. -/
theorem not_oneParity_iterate_f22_110101 (t : ℕ) :
    ¬ OneParity ((finRule f22 hq22)^[t] p110101) :=
  not_oneParity_iterate_f22_of_even_diam p110101_ne_zero (by rw [diam_p110101]; decide) t

/-- **The two taps are load-bearing in the diameter's growth**: a quiescent rule with neither tap
(rule `4`), with the right tap alone (rule `16`) and with the left tap alone (rule `2`) do not widen
the single set cell by two, each image being no wider than the state. -/
theorem diam_finRule_eq_add_two_load_bearing :
    ∃ s : FiniteConfiguration, s ≠ 0 ∧
      (∃ hq : wolframRule 4 0 0 0 = 0, wolframRule 4 0 0 1 = 0 ∧ wolframRule 4 1 0 0 = 0 ∧
        diam (finRule (wolframRule 4) hq s) ≠ diam s + 2) ∧
      (∃ hq : wolframRule 16 0 0 0 = 0, wolframRule 16 0 0 1 = 0 ∧ wolframRule 16 1 0 0 = 1 ∧
        diam (finRule (wolframRule 16) hq s) ≠ diam s + 2) ∧
      (∃ hq : wolframRule 2 0 0 0 = 0, wolframRule 2 0 0 1 = 1 ∧ wolframRule 2 1 0 0 = 0 ∧
        diam (finRule (wolframRule 2) hq s) ≠ diam s + 2) := by
  refine ⟨Finsupp.single 0 1, by simp, ⟨by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, by decide, ?_⟩, ⟨by decide, by decide, by decide, ?_⟩⟩
  · have := diam_finRule_le_of_noTap (f := wolframRule 4) (hq := by decide) (by decide)
      (by decide) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
    omega
  · have := diam_finRule_le_of_rightTap_leftDies (f := wolframRule 16) (hq := by decide)
      (by decide) (by decide) (by decide) (by decide) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
    omega
  · have := diam_finRule_le_of_leftTap_rightDies (f := wolframRule 2) (hq := by decide)
      (by decide) (by decide) (by decide) (by decide) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
    omega

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.mem_occurrences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.mem_occurrences

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.NeverCreatedInPlace.occurrences_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.NeverCreatedInPlace.occurrences_subset

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.NeverCreatedInPlace.occCount_finRule_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.NeverCreatedInPlace.occCount_finRule_le

/-- info: 'ECA.occCount_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.occCount_copies

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.NeverCreatedInPlace.not_reproduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.NeverCreatedInPlace.not_reproduces

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.NeverCreatedInPlace.not_reproduces_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.NeverCreatedInPlace.not_reproduces_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.neverCreatedInPlace_f22_10101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.neverCreatedInPlace_f22_10101

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_f22_of_reads_10101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_f22_of_reads_10101

/-- info: 'ECA.diam_p110101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.diam_p110101

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_f22_110101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_f22_110101

set_option linter.style.longLine false in
/-- info: 'ECA.neverCreatedInPlace_f22_10101_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.neverCreatedInPlace_f22_10101_load_bearing

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.diam_finRule_eq_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.diam_finRule_eq_add_two

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.diam_iterate_finRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.diam_iterate_finRule

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.OneParity.odd_diam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.OneParity.odd_diam

set_option linter.style.longLine false in
/-- info: 'ECA.not_oneParity_iterate_of_even_diam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_oneParity_iterate_of_even_diam

set_option linter.style.longLine false in
/-- info: 'ECA.not_oneParity_iterate_f22_of_even_diam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_oneParity_iterate_f22_of_even_diam

set_option linter.style.longLine false in
/-- info: 'ECA.not_oneParity_iterate_f22_110101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_oneParity_iterate_f22_110101

set_option linter.style.longLine false in
/-- info: 'ECA.diam_finRule_eq_add_two_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.diam_finRule_eq_add_two_load_bearing
