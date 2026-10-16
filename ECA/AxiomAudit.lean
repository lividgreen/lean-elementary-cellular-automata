module

public import ECA.WolframNumber
public import ECA.WolframSymmetries
public import ECA.Surjectivity

/-!
# Axiom audit for the `ECA` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- The Wolfram numeral and the growth census (`ECA/WolframNumber.lean`).
/-- info: 'ECA.LocalRule.ofWolfram_eq_ruleOfNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_eq_ruleOfNat

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_eq_wolframRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_eq_wolframRule

/-- info: 'ECA.bitNat_le_one' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.bitNat_le_one

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_mirrorNum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_mirrorNum_apply

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_mirrorNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_mirrorNum

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_complementNum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_complementNum_apply

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_complementNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_complementNum

/-- info: 'ECA.card_additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_additive

/-- info: 'ECA.LocalRule.ofWolfram_94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_94

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_122

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_126

/-- info: 'ECA.LocalRule.ofWolfram_22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_22

/-- info: 'ECA.LocalRule.ofWolfram_18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_18

/-- info: 'ECA.LocalRule.ofWolfram_90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_90

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_150' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_150

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_202

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_106

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_166' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_166

/-- info: 'ECA.LocalRule.ofWolfram_38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_38

/-- info: 'ECA.LocalRule.ofWolfram_46' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_46

/-- info: 'ECA.LocalRule.ofWolfram_66' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_66

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_174' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_174

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_226' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_226

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_194' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_194

/-- info: 'ECA.LocalRule.ofWolfram_98' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_98

/-- info: 'ECA.LocalRule.ofWolfram_26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_26

/-- info: 'ECA.LocalRule.ofWolfram_60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_60

/-- info: 'ECA.LocalRule.ofWolfram_82' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_82

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_102' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_102

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_146' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_146

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_218' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_218

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_120' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_120

/-- info: 'ECA.LocalRule.ofWolfram_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_14

/-- info: 'ECA.LocalRule.ofWolfram_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_6

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_142' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_142

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_134

/-- info: 'ECA.LocalRule.ofWolfram_74' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_74

/-- info: 'ECA.LocalRule.ofWolfram_30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_30

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_210' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_210

/-- info: 'ECA.LocalRule.ofWolfram_86' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_86

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_154' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_154

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_170

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ofWolfram_240' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ofWolfram_240

set_option linter.style.longLine false in
/-- info: 'ECA.f120_eq_mirrorRule_f106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f120_eq_mirrorRule_f106

set_option linter.style.longLine false in
/-- info: 'ECA.growingWidth_lightCone_eq_zero_of_diamBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingWidth_lightCone_eq_zero_of_diamBounded

/-- info: 'ECA.growth_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growth_census

set_option linter.style.longLine false in
/-- info: 'ECA.growth_census_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growth_census_nonvacuous

-- The symmetries of the elementary rules (`ECA/WolframSymmetries.lean`).
/-- info: 'ECA.card_classes_ofWolfram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_classes_ofWolfram

/-- info: 'ECA.iterate_lineRule_mirrorRule_reflect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.iterate_lineRule_mirrorRule_reflect

set_option linter.style.longLine false in
/-- info: 'ECA.iterate_lineRule_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.iterate_lineRule_complement

set_option linter.style.longLine false in
/-- info: 'ECA.iterate_lineRule_ofWolfram_mirrorNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.iterate_lineRule_ofWolfram_mirrorNum

set_option linter.style.longLine false in
/-- info: 'ECA.iterate_lineRule_ofWolfram_complementNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.iterate_lineRule_ofWolfram_complementNum

/-- info: 'ECA.quiescent_complementNum_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.quiescent_complementNum_iff

set_option linter.style.longLine false in
/-- info: 'ECA.card_quiescent_complementNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_quiescent_complementNum

/-- info: 'ECA.card_leftPermutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_leftPermutive

/-- info: 'ECA.card_rightPermutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_rightPermutive

/-- info: 'ECA.permutive_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.permutive_both

set_option linter.style.longLine false in
/-- info: 'ECA.card_permutiveEnd_ofWolfram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_permutiveEnd_ofWolfram

set_option linter.style.longLine false in
/-- info: 'ECA.rightPermutive_mirrorNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rightPermutive_mirrorNum

set_option linter.style.longLine false in
/-- info: 'ECA.card_permutiveEnd_eq_card_numbers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_permutiveEnd_eq_card_numbers

set_option linter.style.longLine false in
/-- info: 'ECA.bijective_lineRule_ofWolfram_204' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.bijective_lineRule_ofWolfram_204

set_option linter.style.longLine false in
/-- info: 'ECA.bijective_lineRule_ofWolfram_170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.bijective_lineRule_ofWolfram_170

set_option linter.style.longLine false in
/-- info: 'ECA.bijective_lineRule_ofWolfram_240' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.bijective_lineRule_ofWolfram_240

set_option linter.style.longLine false in
/-- info: 'ECA.bijective_lineRule_ofWolfram_51' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.bijective_lineRule_ofWolfram_51

set_option linter.style.longLine false in
/-- info: 'ECA.bijective_lineRule_ofWolfram_85' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.bijective_lineRule_ofWolfram_85

set_option linter.style.longLine false in
/-- info: 'ECA.bijective_lineRule_ofWolfram_15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.bijective_lineRule_ofWolfram_15

set_option linter.style.longLine false in
/-- info: 'ECA.growingWidth_lightCone_ofWolfram_204_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingWidth_lightCone_ofWolfram_204_eq_zero

set_option linter.style.longLine false in
/-- info: 'ECA.not_surjective_of_hasNoPreimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_surjective_of_hasNoPreimage

set_option linter.style.longLine false in
/-- info: 'ECA.not_surjective_lineRule_ofWolfram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_surjective_lineRule_ofWolfram

set_option linter.style.longLine false in
/-- info: 'ECA.not_injective_of_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_injective_of_collision

set_option linter.style.longLine false in
/-- info: 'ECA.injective_lineRule_ofWolfram_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.injective_lineRule_ofWolfram_iff

set_option linter.style.longLine false in
/-- info: 'ECA.bijective_lineRule_ofWolfram_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.bijective_lineRule_ofWolfram_iff

set_option linter.style.longLine false in
/-- info: 'ECA.card_support_finRule_ofWolfram_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_support_finRule_ofWolfram_iff
