module

public import ECA.DefectCounts
public import ECA.ParityEmulation
public import ECA.ReproductionBracket
public import ECA.PermutiveWidth
public import ECA.ObservedColumn
public import ErgodicTheory.Rule18Kinks
import all ECA.DefectCounts

/-!
# The kink count never increases at six rules that agree with rule `90` off adjacent cells
([RuleSpace] §5)

[RuleSpace] §5 Proposition 5.25 shows that a rule agreeing with rule `90` off adjacent cells
reproduces every nonzero pattern whose set cells differ by even amounts, and `ECA.DefectCounts`
shows that such a rule whose kink count never increases in one step reproduces nothing else. This
module shows the monotonicity at the six of the eight rules of the class that do not send both
neighbourhoods `011` and `110` to one, and with it the converse at those six.

* `FiniteConfiguration.kinkCount_eq_kinks` — the kink count of a finitely supported state is the
  number of kinks of its configuration, as counted by `Rule18Kinks.kinks`.
* `LocalRule.AgreesOffAdjacent.kinkCountMono` — a rule that agrees with rule `90` off adjacent cells
  and sends at most one of `011` and `110` to one never increases the kink count, by
  `Rule18Kinks.kinks_step_le_of_agree`; rule `18` is Sabrié and Törmä's proposition
  (`Rule18Kinks.kinks_step_rule18_le`).
* `kinkCountMono_f18`, `kinkCountMono_f26`, `kinkCountMono_f82`, `kinkCountMono_f146`,
  `kinkCountMono_f154`, `kinkCountMono_f210` — the six rules of the class meeting the condition
  (`card_agreesOffAdjacent_atMostOne`).
* `not_kinkCountMono_f218`, `not_kinkCountMono_f90` — the exclusion is load-bearing: rule `218`
  sends both neighbourhoods to one and rule `90` is the linear rule, and each creates kinks.
* `LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity_of_atMostOne` and
  `reproduces_iff_oneParity_f18`, `_f26`, `_f82`, `_f146`, `_f154`, `_f210` — **at these rules
  the patterns reproduced are exactly the nonzero ones of one parity**
  ([RuleSpace] §5 Proposition 5.25), and
  `LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity_nonvacuous` meets the
  hypotheses of the iff theorem at rule `18`.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The kink count as the kinks of a configuration -/

/-- **The kink count of a state is the number of kinks of its configuration** (Sabrié and Törmä
2023, after Kůrka 2003). -/
theorem FiniteConfiguration.kinkCount_eq_kinks (s : FiniteConfiguration) :
    kinkCount s = Rule18Kinks.kinks ⇑s := by
  unfold kinkCount Rule18Kinks.kinks
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Rule18Kinks.kinkSet, Finset.coe_filter, Set.mem_ofPred_eq, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨hi, j, hj, hij, hodd, hmin⟩
    refine ⟨hi, j, hij, hj, hodd, fun m h1 h2 => ?_⟩
    by_contra hm
    rcases hmin m hm with h | h <;> omega
  · rintro ⟨hi, j, hij, hj, hodd, hbet⟩
    refine ⟨hi, j, hj, hij, hodd, fun m hm => ?_⟩
    by_contra hcon
    push Not at hcon
    exact hm (hbet m hcon.1 hcon.2)

/-- **A rule agreeing with rule `90` off adjacent cells that sends at most one of the neighbourhoods
`011` and `110` to one never increases the kink count** ([RuleSpace] §5 Proposition 5.25):
`Rule18Kinks.kinks_step_le_of_agree` through the kink count of a state. -/
theorem LocalRule.AgreesOffAdjacent.kinkCountMono (f : LocalRule) (h : AgreesOffAdjacent f)
    (hone : ¬ (f 0 1 1 = 1 ∧ f 1 1 0 = 1)) : KinkCountMono f h.1 := by
  intro s
  rw [kinkCount_eq_kinks, kinkCount_eq_kinks]
  have e := coe_finRule_iterate f h.1 1 s
  rw [Function.iterate_one, Function.iterate_one] at e
  rw [e]
  exact Rule18Kinks.kinks_step_le_of_agree f h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hone ⇑s
    (s.support.finite_toSet.subset fun i hi => Finsupp.mem_support_iff.mpr hi)

/-- Six of the eight rules agreeing with rule `90` off adjacent cells do not send both `011` and
`110` to one. -/
theorem card_agreesOffAdjacent_atMostOne :
    Fintype.card {f : LocalRule // AgreesOffAdjacent f ∧ ¬ (f 0 1 1 = 1 ∧ f 1 1 0 = 1)} = 6 := by
  decide

/-! ## The six rules -/

/-- **Rule `18` never increases the kink count**: its content is Sabrié and Törmä's proposition
(`Rule18Kinks.kinks_step_rule18_le`). -/
theorem kinkCountMono_f18 : KinkCountMono f18 hq18 :=
  agreesOffAdjacent_f18.kinkCountMono f18 (by unfold f18; decide)

private theorem agreesOffAdjacent_f26 : AgreesOffAdjacent f26 := by
  unfold AgreesOffAdjacent f26; decide

private theorem agreesOffAdjacent_f82 : AgreesOffAdjacent f82 := by
  unfold AgreesOffAdjacent f82; decide

private theorem agreesOffAdjacent_f146 : AgreesOffAdjacent f146 := by
  unfold AgreesOffAdjacent f146; decide

private theorem agreesOffAdjacent_f154 : AgreesOffAdjacent f154 := by
  unfold AgreesOffAdjacent f154; decide

private theorem agreesOffAdjacent_f210 : AgreesOffAdjacent f210 := by
  unfold AgreesOffAdjacent f210; decide

/-- Rule `26` never increases the kink count. -/
theorem kinkCountMono_f26 : KinkCountMono f26 hq26 :=
  agreesOffAdjacent_f26.kinkCountMono f26 (by unfold f26; decide)

/-- Rule `82` never increases the kink count. -/
theorem kinkCountMono_f82 : KinkCountMono f82 hq82 :=
  agreesOffAdjacent_f82.kinkCountMono f82 (by unfold f82; decide)

/-- Rule `146` never increases the kink count. -/
theorem kinkCountMono_f146 : KinkCountMono f146 hq146 :=
  agreesOffAdjacent_f146.kinkCountMono f146 (by unfold f146; decide)

/-- Rule `154` never increases the kink count. -/
theorem kinkCountMono_f154 : KinkCountMono f154 hq154 :=
  agreesOffAdjacent_f154.kinkCountMono f154 (by unfold f154; decide)

/-- Rule `210` never increases the kink count. -/
theorem kinkCountMono_f210 : KinkCountMono f210 hq210 :=
  agreesOffAdjacent_f210.kinkCountMono f210 (by unfold f210; decide)

/-! ## The exclusion is load-bearing -/

/-- The state with set cells exactly `S`. -/
private noncomputable abbrev cellsState (S : Finset ℤ) : FiniteConfiguration :=
  ∑ i ∈ S, Finsupp.single i (1 : ZMod 2)

private theorem cellsState_apply (S : Finset ℤ) (j : ℤ) :
    cellsState S j = if j ∈ S then 1 else 0 := by
  simp [cellsState, Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem kinkCount_cellsState (S : Finset ℤ) : kinkCount (cellsState S) =
    (S.filter fun i => ∃ j ∈ S, i < j ∧ Odd (j - i) ∧ ∀ m ∈ S, m ≤ i ∨ j ≤ m).card :=
  kinkCount_of_support (support_of_cells fun i => by rw [cellsState_apply]; split_ifs <;> simp_all)

/-- **Rule `218` creates kinks**: both `011` and `110` go to one, and the state of two adjacent set
cells, one kink, steps to four, three kinks. So the exclusion of the iff theorem is load-bearing. -/
theorem not_kinkCountMono_f218 : ¬ KinkCountMono f218 hq218 := by
  intro h
  have himg : finRule f218 hq218 (cellsState {0, 1}) = cellsState {-1, 0, 1, 2} := by
    ext j
    rw [finRule_apply]
    simp only [cellsState_apply, Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> first | omega | decide
  have := h (cellsState {0, 1})
  rw [himg, kinkCount_cellsState, kinkCount_cellsState] at this
  revert this
  decide

/-- **Rule `90` creates kinks**: the state `1101`, one kink, steps to a state with set cells
`-1, 0, 1, 4`, three kinks. -/
theorem not_kinkCountMono_f90 : ¬ KinkCountMono f90 hq90 := by
  intro h
  have himg : finRule f90 hq90 (cellsState {0, 1, 3}) = cellsState {-1, 0, 1, 4} := by
    ext j
    rw [finRule_apply]
    simp only [cellsState_apply, Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> first | omega | decide
  have := h (cellsState {0, 1, 3})
  rw [himg, kinkCount_cellsState, kinkCount_cellsState] at this
  revert this
  decide

/-! ## The patterns reproduced -/

/-- **The patterns reproduced are exactly the nonzero ones of one parity**, at every rule agreeing
with rule `90` off adjacent cells that sends at most one of `011` and `110` to one
([RuleSpace] §5 Proposition 5.25). -/
theorem LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity_of_atMostOne (f : LocalRule)
    (h : AgreesOffAdjacent f) (hone : ¬ (f 0 1 1 = 1 ∧ f 1 1 0 = 1)) (p : FiniteConfiguration) :
    Reproduces (finRule f h.1) p ↔ p ≠ 0 ∧ OneParity p :=
  LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity f h (h.kinkCountMono f hone)
    kinkCountCopies p

/-- At rule `18` the patterns reproduced are exactly the nonzero ones of one parity. -/
theorem reproduces_iff_oneParity_f18 (p : FiniteConfiguration) :
    Reproduces (finRule f18 hq18) p ↔ p ≠ 0 ∧ OneParity p :=
  LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity f18 agreesOffAdjacent_f18
    kinkCountMono_f18 kinkCountCopies p

/-- At rule `26` the patterns reproduced are exactly the nonzero ones of one parity. -/
theorem reproduces_iff_oneParity_f26 (p : FiniteConfiguration) :
    Reproduces (finRule f26 hq26) p ↔ p ≠ 0 ∧ OneParity p :=
  LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity f26 agreesOffAdjacent_f26
    kinkCountMono_f26 kinkCountCopies p

/-- At rule `82` the patterns reproduced are exactly the nonzero ones of one parity. -/
theorem reproduces_iff_oneParity_f82 (p : FiniteConfiguration) :
    Reproduces (finRule f82 hq82) p ↔ p ≠ 0 ∧ OneParity p :=
  LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity f82 agreesOffAdjacent_f82
    kinkCountMono_f82 kinkCountCopies p

/-- At rule `146` the patterns reproduced are exactly the nonzero ones of one parity. -/
theorem reproduces_iff_oneParity_f146 (p : FiniteConfiguration) :
    Reproduces (finRule f146 hq146) p ↔ p ≠ 0 ∧ OneParity p :=
  LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity f146 agreesOffAdjacent_f146
    kinkCountMono_f146 kinkCountCopies p

/-- At rule `154` the patterns reproduced are exactly the nonzero ones of one parity. -/
theorem reproduces_iff_oneParity_f154 (p : FiniteConfiguration) :
    Reproduces (finRule f154 hq154) p ↔ p ≠ 0 ∧ OneParity p :=
  LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity f154 agreesOffAdjacent_f154
    kinkCountMono_f154 kinkCountCopies p

/-- At rule `210` the patterns reproduced are exactly the nonzero ones of one parity. -/
theorem reproduces_iff_oneParity_f210 (p : FiniteConfiguration) :
    Reproduces (finRule f210 hq210) p ↔ p ≠ 0 ∧ OneParity p :=
  LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity f210 agreesOffAdjacent_f210
    kinkCountMono_f210 kinkCountCopies p

/-- The hypotheses of `LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity` are met at once, at
rule `18`. -/
theorem LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity_nonvacuous :
    ∃ (f : LocalRule) (h : AgreesOffAdjacent f), KinkCountMono f h.1 ∧ KinkCountCopies :=
  ⟨f18, agreesOffAdjacent_f18, kinkCountMono_f18, kinkCountCopies⟩


set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.kinkCount_eq_kinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.kinkCount_eq_kinks

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.AgreesOffAdjacent.kinkCountMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.kinkCountMono

set_option linter.style.longLine false in
/-- info: 'ECA.card_agreesOffAdjacent_atMostOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_agreesOffAdjacent_atMostOne

set_option linter.style.longLine false in
/-- info: 'ECA.kinkCountMono_f18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.kinkCountMono_f18

set_option linter.style.longLine false in
/-- info: 'ECA.kinkCountMono_f26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.kinkCountMono_f26

set_option linter.style.longLine false in
/-- info: 'ECA.kinkCountMono_f82' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.kinkCountMono_f82

set_option linter.style.longLine false in
/-- info: 'ECA.kinkCountMono_f146' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.kinkCountMono_f146

set_option linter.style.longLine false in
/-- info: 'ECA.kinkCountMono_f154' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.kinkCountMono_f154

set_option linter.style.longLine false in
/-- info: 'ECA.kinkCountMono_f210' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.kinkCountMono_f210

set_option linter.style.longLine false in
/-- info: 'ECA.not_kinkCountMono_f218' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_kinkCountMono_f218

set_option linter.style.longLine false in
/-- info: 'ECA.not_kinkCountMono_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_kinkCountMono_f90

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity_of_atMostOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity_of_atMostOne

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_oneParity_f18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_oneParity_f18

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_oneParity_f26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_oneParity_f26

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_oneParity_f82' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_oneParity_f82

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_oneParity_f146' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_oneParity_f146

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_oneParity_f154' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_oneParity_f154

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_oneParity_f210' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_oneParity_f210

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity_nonvacuous

end ECA
