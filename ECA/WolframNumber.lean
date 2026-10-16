module

public import ECA.ReproductionBracket
public import ECA.BlockCount
public import ECA.Growth
public import ECA.EndRegionClosure

/-!
# The Wolfram number of a radius-one rule, and the growth census over it
([RuleSpace] §2 and §3 Proposition 3.1)

`LocalRule.ofWolfram n` is the radius-one rule of Wolfram number `n < 256` (Wolfram 1983): its
value at `(a, b, c)` is bit `4 a + 2 b + c` of `n`, the convention of `ruleOfNat` and
`wolframRule` (`LocalRule.ofWolfram_eq_ruleOfNat`, `LocalRule.ofWolfram_eq_wolframRule`).
`mirrorNum` and `complementNum` are the numbers of the mirror rule and of the complement conjugate
(`LocalRule.ofWolfram_mirrorNum`, `LocalRule.ofWolfram_complementNum`); `LocalRule.Quiescent` and
`LocalRule.Additive` are decidable at every `LocalRule.ofWolfram n`, and exactly `8` numbers are
additive (`card_additive`). Each hand-written rule of the library is `LocalRule.ofWolfram n` at its
number (`LocalRule.ofWolfram_30`, `LocalRule.ofWolfram_90`, …).

* `Growing n` — the endpoint classes of [RuleSpace] §3, with rules `106` and `120`.
* `growth_census` — **the census**: at a quiescent number, the light cone's growing width is
  unbounded when `Growing n` and identically zero otherwise, and of the `128` quiescent numbers
  `54` grow and `74` do not. `growth_census_nonvacuous` meets both hypothesis pairs at
  numbers `90` and `170`.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

open Nonautonomous

/-- **The Wolfram numeral** ([RuleSpace] §2): the radius-one rule whose value at `(a, b, c)` is
bit `4 a + 2 b + c` of `n`. -/
def LocalRule.ofWolfram (n : Fin 256) : LocalRule :=
  fun a b c => if (n : ℕ).testBit (4 * a.val + 2 * b.val + c.val) then 1 else 0

/-- `LocalRule.ofWolfram n` is `ruleOfNat n`: the same bit convention. -/
theorem LocalRule.ofWolfram_eq_ruleOfNat (n : Fin 256) : LocalRule.ofWolfram n = ruleOfNat n := rfl

/-- `LocalRule.ofWolfram n` is `wolframRule n`: the bit test and the digit formula agree. -/
theorem LocalRule.ofWolfram_eq_wolframRule (n : Fin 256) : LocalRule.ofWolfram n = wolframRule n :=
    by
  funext a b c
  unfold LocalRule.ofWolfram wolframRule
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : (n : ℕ) / 2 ^ (4 * a.val + 2 * b.val + c.val) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize (n : ℕ) / 2 ^ (4 * a.val + 2 * b.val + c.val) % 2 = r at h ⊢
  interval_cases r <;> simp

/-- The `0`-or-`1` value of bit `j` of the number `n`, the building block of `mirrorNum` and
`complementNum`. -/
def bitNat (n : Fin 256) (j : ℕ) : ℕ := (n.val.testBit j).toNat

/-- A bit is `0` or `1`. -/
theorem bitNat_le_one (n : Fin 256) (j : ℕ) : bitNat n j ≤ 1 := Bool.toNat_le _

/-- **The number of the mirror rule**: bit `4 a + 2 b + c` of the result is bit `4 c + 2 b + a`
of `n`, so bits `1 ↔ 4` and `3 ↔ 6` swap. -/
def mirrorNum (n : Fin 256) : Fin 256 :=
  ⟨bitNat n 0 + 2 * bitNat n 4 + 4 * bitNat n 2 + 8 * bitNat n 6 + 16 * bitNat n 1
    + 32 * bitNat n 5 + 64 * bitNat n 3 + 128 * bitNat n 7, by
    have := bitNat_le_one n 0; have := bitNat_le_one n 1; have := bitNat_le_one n 2
    have := bitNat_le_one n 3; have := bitNat_le_one n 4; have := bitNat_le_one n 5
    have := bitNat_le_one n 6; have := bitNat_le_one n 7
    omega⟩

/-- **The number of the complement conjugate**: bit `i` of the result is the complement of bit
`7 - i` of `n`. -/
def complementNum (n : Fin 256) : Fin 256 :=
  ⟨(1 - bitNat n 7) + 2 * (1 - bitNat n 6) + 4 * (1 - bitNat n 5) + 8 * (1 - bitNat n 4)
    + 16 * (1 - bitNat n 3) + 32 * (1 - bitNat n 2) + 64 * (1 - bitNat n 1)
    + 128 * (1 - bitNat n 0), by omega⟩

/-- `LocalRule.ofWolfram_mirrorNum` at every rule and argument, by decision. -/
theorem LocalRule.ofWolfram_mirrorNum_apply : ∀ (n : Fin 256) (a b c : ZMod 2),
    LocalRule.ofWolfram (mirrorNum n) a b c = mirrorRule (LocalRule.ofWolfram n) a b c := by
  decide +kernel

/-- **The mirror**: the number `mirrorNum n` is the rule of `n` read right to left. -/
theorem LocalRule.ofWolfram_mirrorNum (n : Fin 256) : LocalRule.ofWolfram (mirrorNum n) = mirrorRule
    (LocalRule.ofWolfram n) := by
  funext a b c
  exact LocalRule.ofWolfram_mirrorNum_apply n a b c

/-- `LocalRule.ofWolfram_complementNum` at every rule and argument, by decision. -/
theorem LocalRule.ofWolfram_complementNum_apply : ∀ (n : Fin 256) (a b c : ZMod 2),
    LocalRule.ofWolfram (complementNum n) a b c
      = 1 + LocalRule.ofWolfram n (1 + a) (1 + b) (1 + c) := by
  decide +kernel

/-- **The complement conjugate**: `complementNum n` is the rule
`a b c ↦ 1 + LocalRule.ofWolfram n (1 + a) (1 + b) (1 + c)`. -/
theorem LocalRule.ofWolfram_complementNum (n : Fin 256) :
    LocalRule.ofWolfram (complementNum n) = fun a b c => 1 + LocalRule.ofWolfram n (1 + a) (1 + b)
      (1 + c) := by
  funext a b c
  exact LocalRule.ofWolfram_complementNum_apply n a b c

/-- A rule is **quiescent** when the all-zero neighbourhood is sent to `0`. -/
def LocalRule.Quiescent (f : LocalRule) : Prop := f 0 0 0 = 0

namespace LocalRule
instance (f : LocalRule) : Decidable (Quiescent f) := by
  unfold Quiescent; infer_instance
end LocalRule

/-- A rule is **additive** when it is a homomorphism of `(ZMod 2)³` to `ZMod 2`. -/
def LocalRule.Additive (f : LocalRule) : Prop :=
  ∀ a b c a' b' c' : ZMod 2, f (a + a') (b + b') (c + c') = f a b c + f a' b' c'

namespace LocalRule
instance (f : LocalRule) : Decidable (Additive f) := by
  unfold Additive; infer_instance
end LocalRule

/-- **Eight Wolfram numbers are additive**. -/
theorem card_additive : (Finset.univ.filter fun n : Fin 256 => Additive (LocalRule.ofWolfram
    n)).card = 8 := by
  decide +kernel

/-! ## The named rules -/

/-- Wolfram number `94` is the rule `f94`. -/
theorem LocalRule.ofWolfram_94 : LocalRule.ofWolfram 94 = f94 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `122` is the rule `f122`. -/
theorem LocalRule.ofWolfram_122 : LocalRule.ofWolfram 122 = f122 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `126` is the rule `f126`. -/
theorem LocalRule.ofWolfram_126 : LocalRule.ofWolfram 126 = f126 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `22` is the rule `f22`. -/
theorem LocalRule.ofWolfram_22 : LocalRule.ofWolfram 22 = f22 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `18` is the rule `f18`. -/
theorem LocalRule.ofWolfram_18 : LocalRule.ofWolfram 18 = f18 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `90` is the rule `f90`. -/
theorem LocalRule.ofWolfram_90 : LocalRule.ofWolfram 90 = f90 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `150` is the rule `f150`. -/
theorem LocalRule.ofWolfram_150 : LocalRule.ofWolfram 150 = f150 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `202` is the rule `f202`. -/
theorem LocalRule.ofWolfram_202 : LocalRule.ofWolfram 202 = f202 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `106` is the rule `f106`. -/
theorem LocalRule.ofWolfram_106 : LocalRule.ofWolfram 106 = f106 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `166` is the rule `f166`. -/
theorem LocalRule.ofWolfram_166 : LocalRule.ofWolfram 166 = f166 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `38` is the rule `f38`. -/
theorem LocalRule.ofWolfram_38 : LocalRule.ofWolfram 38 = f38 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `46` is the rule `f46`. -/
theorem LocalRule.ofWolfram_46 : LocalRule.ofWolfram 46 = f46 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `66` is the rule `f66`. -/
theorem LocalRule.ofWolfram_66 : LocalRule.ofWolfram 66 = f66 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `174` is the rule `f174`. -/
theorem LocalRule.ofWolfram_174 : LocalRule.ofWolfram 174 = f174 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `226` is the rule `f226`. -/
theorem LocalRule.ofWolfram_226 : LocalRule.ofWolfram 226 = f226 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `194` is the rule `f194`. -/
theorem LocalRule.ofWolfram_194 : LocalRule.ofWolfram 194 = f194 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `98` is the rule `f98`. -/
theorem LocalRule.ofWolfram_98 : LocalRule.ofWolfram 98 = f98 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `26` is the rule `f26`. -/
theorem LocalRule.ofWolfram_26 : LocalRule.ofWolfram 26 = f26 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `60` is the rule `f60`. -/
theorem LocalRule.ofWolfram_60 : LocalRule.ofWolfram 60 = f60 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `82` is the rule `f82`. -/
theorem LocalRule.ofWolfram_82 : LocalRule.ofWolfram 82 = f82 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `102` is the rule `f102`. -/
theorem LocalRule.ofWolfram_102 : LocalRule.ofWolfram 102 = f102 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `146` is the rule `f146`. -/
theorem LocalRule.ofWolfram_146 : LocalRule.ofWolfram 146 = f146 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `218` is the rule `f218`. -/
theorem LocalRule.ofWolfram_218 : LocalRule.ofWolfram 218 = f218 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `120` is the rule `f120`. -/
theorem LocalRule.ofWolfram_120 : LocalRule.ofWolfram 120 = f120 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `14` is the rule `f14`. -/
theorem LocalRule.ofWolfram_14 : LocalRule.ofWolfram 14 = f14 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `6` is the rule `f6`. -/
theorem LocalRule.ofWolfram_6 : LocalRule.ofWolfram 6 = f6 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `142` is the rule `f142`. -/
theorem LocalRule.ofWolfram_142 : LocalRule.ofWolfram 142 = f142 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `134` is the rule `f134`. -/
theorem LocalRule.ofWolfram_134 : LocalRule.ofWolfram 134 = f134 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `74` is the rule `f74`. -/
theorem LocalRule.ofWolfram_74 : LocalRule.ofWolfram 74 = f74 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `30` is the rule `f30`. -/
theorem LocalRule.ofWolfram_30 : LocalRule.ofWolfram 30 = f30 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `210` is the rule `f210`. -/
theorem LocalRule.ofWolfram_210 : LocalRule.ofWolfram 210 = f210 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `86` is the rule `f86`. -/
theorem LocalRule.ofWolfram_86 : LocalRule.ofWolfram 86 = f86 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `154` is the rule `f154`. -/
theorem LocalRule.ofWolfram_154 : LocalRule.ofWolfram 154 = f154 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `170` is the rule `f170`. -/
theorem LocalRule.ofWolfram_170 : LocalRule.ofWolfram 170 = f170 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `240` is the rule `f240`. -/
theorem LocalRule.ofWolfram_240 : LocalRule.ofWolfram 240 = f240 := by
  funext a b c
  revert a b c
  decide

/-! ## The census -/

/-- **Growing** ([RuleSpace] §3 Proposition 3.1): the endpoint classes `LocalRule.GrowsByEndpoints`,
together with rules `106` and `120`. -/
def Growing (n : Fin 256) : Prop :=
  GrowsByEndpoints (LocalRule.ofWolfram n) ∨ LocalRule.ofWolfram n = f106 ∨ LocalRule.ofWolfram n =
    f120

instance (n : Fin 256) : Decidable (Growing n) := by
  unfold Growing; infer_instance

/-- Rule `120` is the mirror of rule `106`. -/
theorem f120_eq_mirrorRule_f106 :
    f120 = mirrorRule f106 := by
  funext a b c
  revert a b c
  decide

/-- **Bounded diameter forces a zero growing width**: no state of a map with `DiamBounded` has an
orbit of unbounded diameter, so the growing part is empty. -/
theorem growingWidth_lightCone_eq_zero_of_diamBounded
    {U : FiniteConfiguration → FiniteConfiguration} (h : DiamBounded U) (n t : ℕ) :
    growingWidth U diam (lightCone n) t = 0 := by
  have hE : GrowingPart U diam = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro s hs
    obtain ⟨c, hc⟩ := h s
    obtain ⟨k, hk⟩ := hs c
    exact absurd (hc k) (not_le.2 hk)
  unfold growingWidth
  apply nonpos_iff_eq_zero.mp
  refine (Nonautonomous.width_le_encard_mergeFiber U _ t).trans ?_
  have hst : Nonautonomous.mergeFiber U (fun t => lightCone n t ∩ GrowingPart U diam) t = ∅ := by
    change Nonautonomous.mergeMk U '' (lightCone n t ∩ GrowingPart U diam) = ∅
    rw [hE, Set.inter_empty, Set.image_empty]
  rw [hst, Set.encard_empty]

/-- **The growth census** ([RuleSpace] §3 Proposition 3.1). (a) At a quiescent Wolfram number
`n` and every light-cone width `w`, the growing width is unbounded in `t` when `Growing n` and
identically zero otherwise. (b) Of the `128` quiescent numbers, `54` grow and `74` do not. -/
theorem growth_census :
    (∀ (n : Fin 256) (hq : LocalRule.ofWolfram n 0 0 0 = 0) (w : ℕ),
      (Growing n → ∀ N : ℕ, ∃ t,
        (N : ℕ∞) < growingWidth (finRule (LocalRule.ofWolfram n) hq) diam (lightCone w) t) ∧
      (¬ Growing n → ∀ t, growingWidth (finRule (LocalRule.ofWolfram n) hq) diam (lightCone w) t =
        0)) ∧
    (Finset.univ.filter fun n : Fin 256 => Quiescent (LocalRule.ofWolfram n)).card = 128 ∧
    (Finset.univ.filter fun n : Fin 256 => Quiescent (LocalRule.ofWolfram n) ∧ Growing n).card = 54
      ∧
    (Finset.univ.filter fun n : Fin 256 => Quiescent (LocalRule.ofWolfram n) ∧ ¬ Growing n).card =
      74 := by
  refine ⟨fun n hq w => ⟨fun h => ?_, fun h t => ?_⟩, ?_, ?_, ?_⟩
  · rcases h with h | h | h
    · exact LocalRule.GrowsByEndpoints.growingWidth_lightCone_unbounded (LocalRule.ofWolfram n) hq h
        w
    · have key : ∀ (g : LocalRule) (hg : g 0 0 0 = 0),
          g = f106 → ∀ N : ℕ, ∃ t,
            (N : ℕ∞) < growingWidth (finRule g hg) diam (lightCone w) t := by
        rintro g hg rfl
        exact growingWidth_lightCone_unbounded_f106 w
      exact key _ hq h
    · have key : ∀ (g : LocalRule) (hg : g 0 0 0 = 0),
          g = mirrorRule f106 → ∀ N : ℕ, ∃ t,
            (N : ℕ∞) < growingWidth (finRule g hg) diam (lightCone w) t := by
        rintro g hg rfl
        exact growingWidth_lightCone_unbounded_mirror_f106 w
      exact key _ hq (h.trans f120_eq_mirrorRule_f106)
  · exact growingWidth_lightCone_eq_zero_of_diamBounded
      (diamBounded_of_not_growing (LocalRule.ofWolfram n) hq h) w t
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- **`growth_census` is not vacuous**: both hypothesis pairs are met at fixed numbers, `90`
growing and quiescent, `170` quiescent and not growing, with the conclusions in force. -/
theorem growth_census_nonvacuous :
    ∃ (hq90 : LocalRule.ofWolfram 90 0 0 0 = 0) (hq170 : LocalRule.ofWolfram 170 0 0 0 = 0),
      Growing 90 ∧ ¬ Growing 170 ∧
      (∀ w N : ℕ, ∃ t,
        (N : ℕ∞) < growingWidth (finRule (LocalRule.ofWolfram 90) hq90) diam (lightCone w) t) ∧
      (∀ w t, growingWidth (finRule (LocalRule.ofWolfram 170) hq170) diam (lightCone w) t = 0) := by
  have h90 : LocalRule.ofWolfram 90 0 0 0 = 0 := by decide
  have h170 : LocalRule.ofWolfram 170 0 0 0 = 0 := by decide
  have a90 : Growing 90 := by decide
  have a170 : ¬ Growing 170 := by decide
  exact ⟨h90, h170, a90, a170,
    fun w => ((growth_census.1 90 h90 w).1 a90),
    fun w => ((growth_census.1 170 h170 w).2 a170)⟩

end ECA
