/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.ReplicationBracket
public import CellularAutomata.BlockCount
public import CellularAutomata.Accretion
public import CellularAutomata.EndRegionClosure
-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The Wolfram number of a radius-one table, and the accretion census over it
([RuleSpace] §2 and §3 Proposition 3.1)

`eca n` is the radius-one table of Wolfram number `n < 256`: its value at `(a, b, c)` is bit
`4 a + 2 b + c` of `n`, the convention of `EndRegionClosure.tableOfNat` and `Doubling.wolframTable`
(`eca_eq_tableOfNat`, `eca_eq_wolframTable`). `mirrorNum` and `complementNum` are the numbers of the
mirror table and of the complement conjugate (`eca_mirrorNum`, `eca_complementNum`); `Quiescent` and
`Additive` are decidable at every `eca n`, and exactly `8` numbers are additive (`card_additive`).
Each hand-written table of the library is `eca n` at its number (`eca_30`, `eca_90`, …).

* `Accreting n` — the endpoint classes of [RuleSpace] §3, with tables `106` and `120`.
* `accretion_census` — **the census**: at a quiescent number, the light cone's growing width is
  unbounded when `Accreting n` and identically zero otherwise, and of the `128` quiescent numbers
  `54` accrete and `74` do not. `accretion_census_nonvacuous` meets both hypothesis pairs at
  numbers `90` and `170`.
-/

@[expose] public section

namespace WolframNumber

open EndpointClasses LightConeWidth ExtremeTapWidth GrowingWidth

/-- **The Wolfram numeral** ([RuleSpace] §2): the radius-one table whose value at `(a, b, c)` is
bit `4 a + 2 b + c` of `n`. -/
def eca (n : Fin 256) : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 :=
  fun a b c => if (n : ℕ).testBit (4 * a.val + 2 * b.val + c.val) then 1 else 0

/-- `eca n` is `tableOfNat n`: the same bit convention. -/
theorem eca_eq_tableOfNat (n : Fin 256) : eca n = EndRegionClosure.tableOfNat n := rfl

/-- `eca n` is `Doubling.wolframTable n`: the bit test and the digit formula agree. -/
theorem eca_eq_wolframTable (n : Fin 256) : eca n = Doubling.wolframTable n := by
  funext a b c
  unfold eca Doubling.wolframTable
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : (n : ℕ) / 2 ^ (4 * a.val + 2 * b.val + c.val) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize (n : ℕ) / 2 ^ (4 * a.val + 2 * b.val + c.val) % 2 = r at h ⊢
  interval_cases r <;> simp

/-- The `0`-or-`1` value of bit `j` of the number `n`, the building block of `mirrorNum` and
`complementNum`. -/
def bitNat (n : Fin 256) (j : ℕ) : ℕ := (n.val.testBit j).toNat

/-- A bit is `0` or `1`. -/
theorem bitNat_le_one (n : Fin 256) (j : ℕ) : bitNat n j ≤ 1 := Bool.toNat_le _

/-- **The number of the mirror table**: bit `4 a + 2 b + c` of the result is bit `4 c + 2 b + a`
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

/-- `eca_mirrorNum` at every table and argument, by decision. -/
theorem eca_mirrorNum_apply : ∀ (n : Fin 256) (a b c : ZMod 2),
    eca (mirrorNum n) a b c = OneTapWidth.mirrorTable (eca n) a b c := by
  decide +kernel

/-- **The mirror**: the number `mirrorNum n` is the table of `n` read right to left. -/
theorem eca_mirrorNum (n : Fin 256) : eca (mirrorNum n) = OneTapWidth.mirrorTable (eca n) := by
  funext a b c
  exact eca_mirrorNum_apply n a b c

/-- `eca_complementNum` at every table and argument, by decision. -/
theorem eca_complementNum_apply : ∀ (n : Fin 256) (a b c : ZMod 2),
    eca (complementNum n) a b c = 1 + eca n (1 + a) (1 + b) (1 + c) := by
  decide +kernel

/-- **The complement conjugate**: `complementNum n` is the table
`a b c ↦ 1 + eca n (1 + a) (1 + b) (1 + c)`. -/
theorem eca_complementNum (n : Fin 256) :
    eca (complementNum n) = fun a b c => 1 + eca n (1 + a) (1 + b) (1 + c) := by
  funext a b c
  exact eca_complementNum_apply n a b c

/-- A table is **quiescent** when the all-zero neighbourhood is sent to `0`. -/
def Quiescent (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop := f 0 0 0 = 0

instance (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Decidable (Quiescent f) := by
  unfold Quiescent; infer_instance

/-- A table is **additive** when it is a homomorphism of `(ZMod 2)³` to `ZMod 2`. -/
def Additive (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  ∀ a b c a' b' c' : ZMod 2, f (a + a') (b + b') (c + c') = f a b c + f a' b' c'

instance (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Decidable (Additive f) := by
  unfold Additive; infer_instance

/-- **Eight Wolfram numbers are additive**. -/
theorem card_additive : (Finset.univ.filter fun n : Fin 256 => Additive (eca n)).card = 8 := by
  decide +kernel

/-! ## The named tables -/

/-- Wolfram number `94` is the table `Doubling.f94`. -/
theorem eca_94 : eca 94 = Doubling.f94 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `122` is the table `Doubling.f122`. -/
theorem eca_122 : eca 122 = Doubling.f122 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `126` is the table `Doubling.f126`. -/
theorem eca_126 : eca 126 = Doubling.f126 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `22` is the table `Doubling.f22`. -/
theorem eca_22 : eca 22 = Doubling.f22 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `18` is the table `ParityEmulation.f18`. -/
theorem eca_18 : eca 18 = ParityEmulation.f18 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `90` is the table `EndpointClasses.f90`. -/
theorem eca_90 : eca 90 = EndpointClasses.f90 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `150` is the table `EndpointClasses.f150`. -/
theorem eca_150 : eca 150 = EndpointClasses.f150 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `202` is the table `EndpointClasses.f202`. -/
theorem eca_202 : eca 202 = EndpointClasses.f202 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `106` is the table `OneTapWidth.f106`. -/
theorem eca_106 : eca 106 = OneTapWidth.f106 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `166` is the table `OneTapWidth.f166`. -/
theorem eca_166 : eca 166 = OneTapWidth.f166 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `38` is the table `OneTapWidth.f38`. -/
theorem eca_38 : eca 38 = OneTapWidth.f38 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `46` is the table `OneTapWidth.f46`. -/
theorem eca_46 : eca 46 = OneTapWidth.f46 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `66` is the table `OneTapWidth.f66`. -/
theorem eca_66 : eca 66 = OneTapWidth.f66 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `174` is the table `OneTapWidth.f174`. -/
theorem eca_174 : eca 174 = OneTapWidth.f174 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `226` is the table `OneTapWidth.f226`. -/
theorem eca_226 : eca 226 = OneTapWidth.f226 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `194` is the table `OneTapWidth.f194`. -/
theorem eca_194 : eca 194 = OneTapWidth.f194 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `98` is the table `OneTapWidth.f98`. -/
theorem eca_98 : eca 98 = OneTapWidth.f98 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `26` is the table `ReplicationBracket.f26`. -/
theorem eca_26 : eca 26 = ReplicationBracket.f26 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `60` is the table `ReplicationBracket.f60`. -/
theorem eca_60 : eca 60 = ReplicationBracket.f60 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `82` is the table `ReplicationBracket.f82`. -/
theorem eca_82 : eca 82 = ReplicationBracket.f82 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `102` is the table `ReplicationBracket.f102`. -/
theorem eca_102 : eca 102 = ReplicationBracket.f102 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `146` is the table `ReplicationBracket.f146`. -/
theorem eca_146 : eca 146 = ReplicationBracket.f146 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `218` is the table `ReplicationBracket.f218`. -/
theorem eca_218 : eca 218 = ReplicationBracket.f218 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `120` is the table `ReplicationBracket.f120`. -/
theorem eca_120 : eca 120 = ReplicationBracket.f120 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `14` is the table `BlockTrainWidth.f14`. -/
theorem eca_14 : eca 14 = BlockTrainWidth.f14 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `6` is the table `BlockTrainWidth.f6`. -/
theorem eca_6 : eca 6 = BlockTrainWidth.f6 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `142` is the table `BlockTrainWidth.f142`. -/
theorem eca_142 : eca 142 = BlockTrainWidth.f142 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `134` is the table `BlockTrainWidth.f134`. -/
theorem eca_134 : eca 134 = BlockTrainWidth.f134 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `74` is the table `BlockTrainWidth.f74`. -/
theorem eca_74 : eca 74 = BlockTrainWidth.f74 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `30` is the table `ExtremeTapWidth.f30`. -/
theorem eca_30 : eca 30 = ExtremeTapWidth.f30 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `210` is the table `ExtremeTapWidth.f210`. -/
theorem eca_210 : eca 210 = ExtremeTapWidth.f210 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `86` is the table `ExtremeTapWidth.f86`. -/
theorem eca_86 : eca 86 = ExtremeTapWidth.f86 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `154` is the table `ExtremeTapWidth.f154`. -/
theorem eca_154 : eca 154 = ExtremeTapWidth.f154 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `170` is the table `ExtremeTapWidth.f170`. -/
theorem eca_170 : eca 170 = ExtremeTapWidth.f170 := by
  funext a b c
  revert a b c
  decide

/-- Wolfram number `240` is the table `ExtremeTapWidth.f240`. -/
theorem eca_240 : eca 240 = ExtremeTapWidth.f240 := by
  funext a b c
  revert a b c
  decide

/-! ## The census -/

/-- **Accreting** ([RuleSpace] §3 Proposition 3.1): the endpoint classes `AccretesByEndpoints`,
together with tables `106` and `120`. -/
def Accreting (n : Fin 256) : Prop :=
  AccretesByEndpoints (eca n) ∨ eca n = OneTapWidth.f106 ∨ eca n = ReplicationBracket.f120

instance (n : Fin 256) : Decidable (Accreting n) := by
  unfold Accreting; infer_instance

/-- Table `120` is the mirror of table `106`. -/
theorem f120_eq_mirrorTable_f106 :
    ReplicationBracket.f120 = OneTapWidth.mirrorTable OneTapWidth.f106 := by
  funext a b c
  revert a b c
  decide

/-- **Bounded diameter forces a zero growing width**: no state of a map with `DiamBounded` has an
orbit of unbounded diameter, so the growing part is empty. -/
theorem growingWidth_lightCone_eq_zero_of_diamBounded
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} (h : ReplicationBracket.DiamBounded U) (n t : ℕ) :
    growingWidth U diam (lightCone n) t = 0 := by
  have hE : GrowingPart U diam = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro s hs
    obtain ⟨c, hc⟩ := h s
    obtain ⟨k, hk⟩ := hs c
    exact absurd (hc k) (not_le.2 hk)
  unfold growingWidth
  apply nonpos_iff_eq_zero.mp
  refine (MemoryWidth.memWidth_le_encard_mergeStage U _ t).trans ?_
  have hst : GrowingCore.mergeStage U (fun t => lightCone n t ∩ GrowingPart U diam) t = ∅ := by
    change GrowingCore.mergeMk U '' (lightCone n t ∩ GrowingPart U diam) = ∅
    rw [hE, Set.inter_empty, Set.image_empty]
  rw [hst, Set.encard_empty]

/-- **The accretion census** ([RuleSpace] §3 Proposition 3.1). (a) At a quiescent Wolfram number
`n` and every light-cone width `w`, the growing width is unbounded in `t` when `Accreting n` and
identically zero otherwise. (b) Of the `128` quiescent numbers, `54` accrete and `74` do not. -/
theorem accretion_census :
    (∀ (n : Fin 256) (hq : eca n 0 0 0 = 0) (w : ℕ),
      (Accreting n → ∀ N : ℕ, ∃ t,
        (N : ℕ∞) < growingWidth (tableRule (eca n) hq) diam (lightCone w) t) ∧
      (¬ Accreting n → ∀ t, growingWidth (tableRule (eca n) hq) diam (lightCone w) t = 0)) ∧
    (Finset.univ.filter fun n : Fin 256 => Quiescent (eca n)).card = 128 ∧
    (Finset.univ.filter fun n : Fin 256 => Quiescent (eca n) ∧ Accreting n).card = 54 ∧
    (Finset.univ.filter fun n : Fin 256 => Quiescent (eca n) ∧ ¬ Accreting n).card = 74 := by
  refine ⟨fun n hq w => ⟨fun h => ?_, fun h t => ?_⟩, ?_, ?_, ?_⟩
  · rcases h with h | h | h
    · exact growingWidth_lightCone_unbounded_of_accretesByEndpoints (eca n) hq h w
    · have key : ∀ (g : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hg : g 0 0 0 = 0),
          g = OneTapWidth.f106 → ∀ N : ℕ, ∃ t,
            (N : ℕ∞) < growingWidth (tableRule g hg) diam (lightCone w) t := by
        rintro g hg rfl
        exact OneTapWidth.growingWidth_lightCone_unbounded_f106 w
      exact key _ hq h
    · have key : ∀ (g : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hg : g 0 0 0 = 0),
          g = OneTapWidth.mirrorTable OneTapWidth.f106 → ∀ N : ℕ, ∃ t,
            (N : ℕ∞) < growingWidth (tableRule g hg) diam (lightCone w) t := by
        rintro g hg rfl
        exact OneTapWidth.growingWidth_lightCone_unbounded_mirror_f106 w
      exact key _ hq (h.trans f120_eq_mirrorTable_f106)
  · exact growingWidth_lightCone_eq_zero_of_diamBounded
      (ReplicationBracket.diamBounded_of_not_accreting (eca n) hq h) w t
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- **`accretion_census` is not vacuous**: both hypothesis pairs are met at fixed numbers, `90`
accreting and quiescent, `170` quiescent and not accreting, with the conclusions in force. -/
theorem accretion_census_nonvacuous :
    ∃ (hq90 : eca 90 0 0 0 = 0) (hq170 : eca 170 0 0 0 = 0),
      Accreting 90 ∧ ¬ Accreting 170 ∧
      (∀ w N : ℕ, ∃ t,
        (N : ℕ∞) < growingWidth (tableRule (eca 90) hq90) diam (lightCone w) t) ∧
      (∀ w t, growingWidth (tableRule (eca 170) hq170) diam (lightCone w) t = 0) := by
  have h90 : eca 90 0 0 0 = 0 := by decide
  have h170 : eca 170 0 0 0 = 0 := by decide
  have a90 : Accreting 90 := by decide
  have a170 : ¬ Accreting 170 := by decide
  exact ⟨h90, h170, a90, a170,
    fun w => ((accretion_census.1 90 h90 w).1 a90),
    fun w => ((accretion_census.1 170 h170 w).2 a170)⟩

end WolframNumber
