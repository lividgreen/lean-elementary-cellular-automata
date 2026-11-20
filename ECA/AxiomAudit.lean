module

public import ECA.WolframNumber
public import ECA.WolframSymmetries
public import ECA.Surjectivity
public import ECA.BlockCode
public import ECA.CheckerboardFront
public import ECA.ForcingTables
public import ECA.HolePairs
public import ECA.WalledTables
public import ECA.EndsDetermine
public import ECA.ConservedReadings

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

-- The sliding block code of rule `222`'s holes (`ECA/HolePairs.lean`).
set_option linter.style.longLine false in
/-- info: 'ECA.holePairs_finRule_f222' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.holePairs_finRule_f222

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.holePairs_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.holePairs_translate

-- The sliding block codes a step conserves (`ECA/BlockCode.lean`).
set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_finRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_finRule

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_finRule_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_finRule_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_finRule_f206' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_finRule_f206

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_finRule_f220' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_finRule_f220

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_finRule_f202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_finRule_f202

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_finRule_f216' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_finRule_f216

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_finRule_f50' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_finRule_f50

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_finRule_f178' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_finRule_f178

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_finRule_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_finRule_carry

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_finRule_carry_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_finRule_carry_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.slipPhases_finRule_f50' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.slipPhases_finRule_f50

set_option linter.style.longLine false in
/-- info: 'ECA.slipPhases_finRule_f178' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.slipPhases_finRule_f178

set_option linter.style.longLine false in
/-- info: 'ECA.swap_slipPhases_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.swap_slipPhases_ne

set_option linter.style.longLine false in
/-- info: 'ECA.growingPart_f50_eq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingPart_f50_eq_ne_zero

set_option linter.style.longLine false in
/-- info: 'ECA.growingPart_f178_eq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingPart_f178_eq_ne_zero

set_option linter.style.longLine false in
/-- info: 'ECA.growingPart_f206_eq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingPart_f206_eq_ne_zero

set_option linter.style.longLine false in
/-- info: 'ECA.growingPart_f220_eq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingPart_f220_eq_ne_zero

set_option linter.style.longLine false in
/-- info: 'ECA.mem_growingPart_f202_of_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.mem_growingPart_f202_of_pair

set_option linter.style.longLine false in
/-- info: 'ECA.mem_growingPart_f216_of_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.mem_growingPart_f216_of_pair

set_option linter.style.longLine false in
/-- info: 'ECA.mem_growingPart_f202_of_pair_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.mem_growingPart_f202_of_pair_nonvacuous

-- Forcing tables conserve no sliding block code but zero (`ECA/ForcingTables.lean`).
set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_leftForcing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_leftForcing

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_rightForcing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_rightForcing

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_leftForcing_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_leftForcing_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_forcing_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_forcing_load_bearing

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f242' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f242

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f246' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f246

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f248' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f248

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f250' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f250

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f252' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f252

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f254

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f186' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f186

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f190' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f190

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f234' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f234

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f238' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f238

-- A checkerboard front conserves no sliding block code but zero (`ECA/CheckerboardFront.lean`).
set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_checkerboardFrontLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_checkerboardFrontLeft

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_checkerboardFrontRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_checkerboardFrontRight

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f114' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f114

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_f58' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_f58

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_checkerboardFrontLeft_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_checkerboardFrontLeft_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_checkerboard_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_checkerboard_load_bearing

-- A wall of two set cells: six tables carry no sliding block code with an injective law
-- (`ECA/WalledTables.lean`).
set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_walled_merges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_walled_merges

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_walled_merges_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_walled_merges_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f234' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f234

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f238' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f238

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f248' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f248

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f250' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f250

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f252' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f252

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f254

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_walled_injective_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_walled_injective_load_bearing

-- Tables `188` and `230` carry no sliding block code with an injective law, given the ends
-- statement.
set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f188' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f188

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f230' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f230

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_window_merges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_window_merges

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.blockCode_eq_zero_of_window_merges_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.blockCode_eq_zero_of_window_merges_nonvacuous

-- The ends statement at rule `188`, and tables `188` and `230` carrying no sliding block code with
-- an injective law, with its witnesses.
set_option linter.style.longLine false in
/-- info: 'ECA.endsDetermine_f188' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.endsDetermine_f188

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f188'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f188'

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f230'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f230'

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f188_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f188_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_eq_zero_of_injective_law_f230_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_eq_zero_of_injective_law_f230_nonvacuous

-- Table `206` fixing every reading of a conserved code under an injective law, with its witness.
set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_finRule_eq_of_injective_law_f206' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_finRule_eq_of_injective_law_f206

set_option linter.style.longLine false in
/-- info: 'ECA.law_apply_blockCode_eq_of_injective_law_f206' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.law_apply_blockCode_eq_of_injective_law_f206

set_option linter.style.longLine false in
/-- info: 'ECA.blockCode_finRule_eq_of_injective_law_f206_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.blockCode_finRule_eq_of_injective_law_f206_nonvacuous
