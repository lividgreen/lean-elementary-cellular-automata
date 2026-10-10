/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.MergeQuotient
public import CellularAutomata.WolframNumber

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit for the `CellularAutomata` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- The growing kernel (`CellularAutomata/MergeQuotient.lean`): the merge quotient manufactures a
-- reading with an injective law from any update alone, with no hypothesis, and every
-- injective-law staged-square reading factors through it (universality).
/-- info: 'GrowingCore.mergeLaw_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingCore.mergeLaw_injective

/-- info: 'GrowingCore.stagedSquare_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingCore.stagedSquare_merge

/-- info: 'GrowingCore.merges_invariant_of_stagedSquare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingCore.merges_invariant_of_stagedSquare

/-- info: 'GrowingCore.exists_mergeMk_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingCore.exists_mergeMk_injective

/-- info: 'GrowingCore.advances_mergeStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingCore.advances_mergeStage

/-- info: 'GrowingCore.mergeStage_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingCore.mergeStage_injOn

-- The Wolfram numeral and the accretion census (`CellularAutomata/WolframNumber.lean`).
/-- info: 'WolframNumber.eca_eq_tableOfNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_eq_tableOfNat

/-- info: 'WolframNumber.eca_eq_wolframTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_eq_wolframTable

/-- info: 'WolframNumber.bitNat_le_one' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.bitNat_le_one

/-- info: 'WolframNumber.eca_mirrorNum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_mirrorNum_apply

/-- info: 'WolframNumber.eca_mirrorNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_mirrorNum

/-- info: 'WolframNumber.eca_complementNum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_complementNum_apply

/-- info: 'WolframNumber.eca_complementNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_complementNum

/-- info: 'WolframNumber.card_additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.card_additive

/-- info: 'WolframNumber.eca_94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_94

/-- info: 'WolframNumber.eca_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_122

/-- info: 'WolframNumber.eca_126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_126

/-- info: 'WolframNumber.eca_22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_22

/-- info: 'WolframNumber.eca_18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_18

/-- info: 'WolframNumber.eca_90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_90

/-- info: 'WolframNumber.eca_150' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_150

/-- info: 'WolframNumber.eca_202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_202

/-- info: 'WolframNumber.eca_106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_106

/-- info: 'WolframNumber.eca_166' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_166

/-- info: 'WolframNumber.eca_38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_38

/-- info: 'WolframNumber.eca_46' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_46

/-- info: 'WolframNumber.eca_66' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_66

/-- info: 'WolframNumber.eca_174' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_174

/-- info: 'WolframNumber.eca_226' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_226

/-- info: 'WolframNumber.eca_194' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_194

/-- info: 'WolframNumber.eca_98' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_98

/-- info: 'WolframNumber.eca_26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_26

/-- info: 'WolframNumber.eca_60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_60

/-- info: 'WolframNumber.eca_82' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_82

/-- info: 'WolframNumber.eca_102' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_102

/-- info: 'WolframNumber.eca_146' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_146

/-- info: 'WolframNumber.eca_218' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_218

/-- info: 'WolframNumber.eca_120' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_120

/-- info: 'WolframNumber.eca_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_14

/-- info: 'WolframNumber.eca_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_6

/-- info: 'WolframNumber.eca_142' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_142

/-- info: 'WolframNumber.eca_134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_134

/-- info: 'WolframNumber.eca_74' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_74

/-- info: 'WolframNumber.eca_30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_30

/-- info: 'WolframNumber.eca_210' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_210

/-- info: 'WolframNumber.eca_86' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_86

/-- info: 'WolframNumber.eca_154' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_154

/-- info: 'WolframNumber.eca_170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_170

/-- info: 'WolframNumber.eca_240' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.eca_240

/-- info: 'WolframNumber.f120_eq_mirrorTable_f106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.f120_eq_mirrorTable_f106

/-- info: 'WolframNumber.growingWidth_lightCone_eq_zero_of_diamBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.growingWidth_lightCone_eq_zero_of_diamBounded

/-- info: 'WolframNumber.accretion_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.accretion_census

/-- info: 'WolframNumber.accretion_census_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WolframNumber.accretion_census_nonvacuous

