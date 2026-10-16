module

public import ECA.WolframNumber
public import ECA.PersistentWordCount
public import ErgodicTheory.ElementaryRuleClasses
public import ErgodicTheory.NumberConservation
public import Mathlib.Data.Fintype.Pi

/-!
# The symmetries of the elementary rules, and the permutive and bijective numbers

The Wolfram numeral `LocalRule.ofWolfram` and the two number maps `mirrorNum`, `complementNum` of
`WolframNumber.lean` are the classical `ElementaryRuleClasses.elementaryRule`, `reflectNum` and
`complementNum` (`LocalRule.ofWolfram_eq_elementaryRule`, `mirrorNum_eq_reflectNum`,
`complementNum_eq_complementNum`), so the count of `88` classes of Li and Packard (1990) holds
here over `mirrorNum` and `complementNum` (`card_classes_ofWolfram`).

* The reflection and the complement conjugate the step of the line, at every local rule and every
  iterate (`LocalRule.lineRule_mirrorRule_reflect`, `iterate_lineRule_mirrorRule_reflect`,
  `LocalRule.lineRule_complement`, `iterate_lineRule_complement`), and so at
  `LocalRule.ofWolfram (mirrorNum n)` and `LocalRule.ofWolfram (complementNum n)`.
* Among the non-quiescent numbers exactly `64` have a quiescent complement conjugate, those with
  `LocalRule.ofWolfram n 1 1 1 = 1` (`card_quiescent_complementNum`).
* `16` numbers are left-permutive, `16` right-permutive, exactly `90`, `105`, `150`, `165` both,
  and `28` one or the other (`card_leftPermutive`, `card_rightPermutive`, `permutive_both`,
  `card_permutiveEnd_ofWolfram`, which is `card_permutiveEnd` by
  `card_permutiveEnd_eq_card_numbers`); `mirrorNum` carries the left-permutive to the
  right-permutive.
* The number of ones of a finitely supported configuration is kept exactly by the quiescent
  numbers `170`, `184`, `204`, `226` and `240` (`card_support_finRule_ofWolfram_iff`, which is
  `NumberConservation.conserves_iff` on the carrier `ℤ →₀ ZMod 2`).
* The six numbers `204`, `170`, `240`, `51`, `85`, `15` give bijections of the line, the identity,
  the two shifts and the three complemented ones (`lineRule_ofWolfram_204` and its five companions,
  `bijective_lineRule_ofWolfram_204` and its five companions).
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The numeral and the classical statement -/

/-- The numeral is the classical elementary rule of the same number. -/
theorem LocalRule.ofWolfram_eq_elementaryRule (n : Fin 256) : LocalRule.ofWolfram n =
    ElementaryRuleClasses.elementaryRule n :=
  rfl

/-- `mirrorNum` is the classical reflection of the numbers. -/
theorem mirrorNum_eq_reflectNum : mirrorNum = ElementaryRuleClasses.reflectNum := by
  funext n
  revert n
  decide +kernel

/-- `complementNum` is the classical complementation of the numbers. -/
theorem complementNum_eq_complementNum :
    complementNum = ElementaryRuleClasses.complementNum := by
  funext n
  revert n
  decide +kernel

/-- **The elementary rules fall into `88` classes** under `mirrorNum` and `complementNum`
(Li and Packard 1990): the classical count, read at the numbers of this library. -/
theorem card_classes_ofWolfram :
    (Finset.univ.filter fun n : Fin 256 =>
      n ≤ mirrorNum n ∧ n ≤ complementNum n ∧ n ≤ mirrorNum (complementNum n)).card = 88 := by
  rw [mirrorNum_eq_reflectNum, complementNum_eq_complementNum]
  exact ElementaryRuleClasses.card_classes

/-! ## The two conjugacies of the step -/

/-- **The reflection conjugates the step**: the mirror rule on the reversed line is the reversal
of the rule on the line. -/
theorem LocalRule.lineRule_mirrorRule_reflect (f : LocalRule) (x : Configuration) :
    lineRule (mirrorRule f) (fun i => x (-i)) = fun i => lineRule f x (-i) := by
  funext i
  unfold lineRule mirrorRule
  have h1 : -(i + 1) = -i - 1 := by ring
  have h2 : -(i - 1) = -i + 1 := by ring
  beta_reduce
  rw [h1, h2]

/-- The reflection conjugates every iterate of the step. -/
theorem iterate_lineRule_mirrorRule_reflect (f : LocalRule)
    (x : Configuration) (t : ℕ) :
    (lineRule (mirrorRule f))^[t] (fun i => x (-i)) = fun i => (lineRule f)^[t] x (-i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      lineRule_mirrorRule_reflect]

/-- **The complement conjugates the step**: the complement conjugate of the rule, on the
complemented configuration, is the complement of the rule on the configuration. -/
theorem LocalRule.lineRule_complement (f : LocalRule) (x : Configuration) :
    lineRule (fun a b c => 1 + f (1 + a) (1 + b) (1 + c)) (fun i => 1 + x i)
      = fun i => 1 + lineRule f x i := by
  have h : ∀ y : ZMod 2, 1 + (1 + y) = y := by decide
  funext i
  unfold lineRule
  beta_reduce
  rw [h, h, h]

/-- The complement conjugates every iterate of the step. -/
theorem iterate_lineRule_complement (f : LocalRule) (x : Configuration)
    (t : ℕ) :
    (lineRule (fun a b c => 1 + f (1 + a) (1 + b) (1 + c)))^[t] (fun i => 1 + x i)
      = fun i => 1 + (lineRule f)^[t] x i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, lineRule_complement]

/-- The reflection conjugacy at the number `mirrorNum n`. -/
theorem lineRule_ofWolfram_mirrorNum (n : Fin 256) (x : Configuration) :
    lineRule (LocalRule.ofWolfram (mirrorNum n)) (fun i => x (-i)) = fun i => lineRule
      (LocalRule.ofWolfram n) x (-i) := by
  rw [LocalRule.ofWolfram_mirrorNum, lineRule_mirrorRule_reflect]

/-- The reflection conjugacy at the number `mirrorNum n`, at every iterate. -/
theorem iterate_lineRule_ofWolfram_mirrorNum (n : Fin 256) (x : Configuration) (t : ℕ) :
    (lineRule (LocalRule.ofWolfram (mirrorNum n)))^[t] (fun i => x (-i))
      = fun i => (lineRule (LocalRule.ofWolfram n))^[t] x (-i) := by
  rw [LocalRule.ofWolfram_mirrorNum, iterate_lineRule_mirrorRule_reflect]

/-- The complement conjugacy at the number `complementNum n`. -/
theorem lineRule_ofWolfram_complementNum (n : Fin 256) (x : Configuration) :
    lineRule (LocalRule.ofWolfram (complementNum n)) (fun i => 1 + x i) = fun i => 1 + lineRule
      (LocalRule.ofWolfram n) x i := by
  rw [LocalRule.ofWolfram_complementNum, lineRule_complement]

/-- The complement conjugacy at the number `complementNum n`, at every iterate. -/
theorem iterate_lineRule_ofWolfram_complementNum (n : Fin 256) (x : Configuration) (t : ℕ) :
    (lineRule (LocalRule.ofWolfram (complementNum n)))^[t] (fun i => 1 + x i)
      = fun i => 1 + (lineRule (LocalRule.ofWolfram n))^[t] x i := by
  rw [LocalRule.ofWolfram_complementNum, iterate_lineRule_complement]

/-! ## Quiescence under complementation -/

/-- **Quiescent complement conjugates**: a non-quiescent number has a quiescent complement
conjugate exactly when `LocalRule.ofWolfram n 1 1 1 = 1`. -/
theorem quiescent_complementNum_iff (n : Fin 256) (hn : ¬ Quiescent (LocalRule.ofWolfram n)) :
    Quiescent (LocalRule.ofWolfram (complementNum n)) ↔ LocalRule.ofWolfram n 1 1 1 = 1 := by
  revert n
  decide +kernel

/-- **Sixty-four numbers** are not quiescent and have a quiescent complement conjugate. -/
theorem card_quiescent_complementNum :
    (Finset.univ.filter fun n : Fin 256 =>
      ¬ Quiescent (LocalRule.ofWolfram n) ∧ Quiescent (LocalRule.ofWolfram (complementNum n))).card
        = 64 := by
  decide +kernel

/-! ## Permutive numbers -/

/-- **Sixteen numbers are left-permutive.** -/
theorem card_leftPermutive :
    (Finset.univ.filter fun n : Fin 256 => LeftPermutive (LocalRule.ofWolfram n)).card = 16 := by
  decide +kernel

/-- **Sixteen numbers are right-permutive.** -/
theorem card_rightPermutive :
    (Finset.univ.filter fun n : Fin 256 => RightPermutive (LocalRule.ofWolfram n)).card = 16 := by
  decide +kernel

/-- **Exactly four numbers are permutive at both ends**: `90`, `105`, `150` and `165`. -/
theorem permutive_both :
    (Finset.univ.filter fun n : Fin 256 => LeftPermutive (LocalRule.ofWolfram n) ∧ RightPermutive
      (LocalRule.ofWolfram n))
      = {90, 105, 150, 165} := by
  decide +kernel

/-- **Twenty-eight numbers are permutive at one end or the other.** -/
theorem card_permutiveEnd_ofWolfram :
    (Finset.univ.filter fun n : Fin 256 => LeftPermutive (LocalRule.ofWolfram n) ∨ RightPermutive
      (LocalRule.ofWolfram n)).card
      = 28 := by
  decide +kernel

/-- The mirror carries a left-permutive number to a right-permutive one. -/
theorem rightPermutive_mirrorNum (n : Fin 256) (h : LeftPermutive (LocalRule.ofWolfram n)) :
    RightPermutive (LocalRule.ofWolfram (mirrorNum n)) := by
  revert n
  decide +kernel

/-- The number read back from a rule: the sum of its values at the eight neighbourhoods, each
weighted by the power of two of its position, reduced modulo `256`. -/
private def LocalRule.decodeNum (f : LocalRule) : Fin 256 :=
  ⟨(∑ a : ZMod 2, ∑ b : ZMod 2, ∑ c : ZMod 2,
      2 ^ (4 * a.val + 2 * b.val + c.val) * (f a b c).val) % 256, Nat.mod_lt _ (by norm_num)⟩

private theorem decodeNum_ofWolfram (n : Fin 256) : decodeNum (LocalRule.ofWolfram n) = n := by
  revert n
  decide +kernel

/-- **Different numbers are different rules.** -/
theorem LocalRule.ofWolfram_injective : Function.Injective LocalRule.ofWolfram :=
  Function.LeftInverse.injective decodeNum_ofWolfram

/-- **The numeral is a bijection onto the `256` radius-one rules.** -/
theorem LocalRule.ofWolfram_bijective : Function.Bijective LocalRule.ofWolfram := by
  refine (Fintype.bijective_iff_injective_and_card LocalRule.ofWolfram).2
    ⟨LocalRule.ofWolfram_injective, ?_⟩
  simp [ZMod.card]

/-- **The count over the rules is the count over the numbers**: the subtype of rules permutive at
an end has as many members as there are numbers whose rule is, so `card_permutiveEnd` and
`card_permutiveEnd_ofWolfram` are the one count. -/
theorem card_permutiveEnd_eq_card_numbers :
    Fintype.card {f : LocalRule // LeftPermutive f ∨ RightPermutive f}
      = (Finset.univ.filter fun n : Fin 256 =>
          LeftPermutive (LocalRule.ofWolfram n) ∨ RightPermutive (LocalRule.ofWolfram n)).card := by
  rw [Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun n _ => LocalRule.ofWolfram n) (fun n hn => by simpa using hn)
    (fun a _ b _ h => LocalRule.ofWolfram_injective h) (fun f hf => ?_)
  obtain ⟨n, rfl⟩ := LocalRule.ofWolfram_bijective.2 f
  exact ⟨n, by simpa using hf, rfl⟩

/-! ## The six bijective rules -/

/-- Wolfram number `204` is the identity rule `a b c ↦ b`. -/
theorem LocalRule.ofWolfram_204 (a b c : ZMod 2) : LocalRule.ofWolfram 204 a b c = b := by
  revert a b c
  decide

/-- Wolfram number `51` is the complement of the identity rule, `a b c ↦ 1 + b`. -/
theorem LocalRule.ofWolfram_51 (a b c : ZMod 2) : LocalRule.ofWolfram 51 a b c = 1 + b := by
  revert a b c
  decide

/-- Wolfram number `15` is the rule `a b c ↦ 1 + a`. -/
theorem LocalRule.ofWolfram_15 (a b c : ZMod 2) : LocalRule.ofWolfram 15 a b c = 1 + a := by
  revert a b c
  decide

/-- Wolfram number `85` is the rule `a b c ↦ 1 + c`. -/
theorem LocalRule.ofWolfram_85 (a b c : ZMod 2) : LocalRule.ofWolfram 85 a b c = 1 + c := by
  revert a b c
  decide

/-- **Rule `204` is the identity of the line.** -/
theorem lineRule_ofWolfram_204 : lineRule (LocalRule.ofWolfram 204) = id := by
  funext x i
  exact LocalRule.ofWolfram_204 _ _ _

/-- **Rule `170` is the left shift of the line**: `x ↦ (i ↦ x (i + 1))`. -/
theorem lineRule_ofWolfram_170 (x : Configuration) : lineRule (LocalRule.ofWolfram 170) x = fun i =>
  x
    (i + 1) := by
  funext i
  unfold lineRule
  rw [LocalRule.ofWolfram_170]
  rfl

/-- **Rule `240` is the right shift of the line**: `x ↦ (i ↦ x (i - 1))`. -/
theorem lineRule_ofWolfram_240 (x : Configuration) : lineRule (LocalRule.ofWolfram 240) x = fun i =>
  x
    (i - 1) := by
  funext i
  unfold lineRule
  rw [LocalRule.ofWolfram_240]
  rfl

/-- **Rule `51` is the identity followed by the complement.** -/
theorem lineRule_ofWolfram_51 (x : Configuration) : lineRule (LocalRule.ofWolfram 51) x = fun i => 1
  +
    x i := by
  funext i
  exact LocalRule.ofWolfram_51 _ _ _

/-- **Rule `85` is the left shift followed by the complement.** -/
theorem lineRule_ofWolfram_85 (x : Configuration) : lineRule (LocalRule.ofWolfram 85) x = fun i => 1
  +
    x (i + 1) := by
  funext i
  exact LocalRule.ofWolfram_85 _ _ _

/-- **Rule `15` is the right shift followed by the complement.** -/
theorem lineRule_ofWolfram_15 (x : Configuration) : lineRule (LocalRule.ofWolfram 15) x = fun i => 1
  +
    x (i - 1) := by
  funext i
  exact LocalRule.ofWolfram_15 _ _ _

private theorem one_add_one_add (y : ZMod 2) : 1 + (1 + y) = y := by
  revert y
  decide

/-- Rule `204` is a bijection of the line. -/
theorem bijective_lineRule_ofWolfram_204 :
    Function.Bijective (lineRule (LocalRule.ofWolfram 204)) := by
  rw [lineRule_ofWolfram_204]
  exact Function.bijective_id

/-- Rule `170` is a bijection of the line, with inverse the right shift. -/
theorem bijective_lineRule_ofWolfram_170 :
    Function.Bijective (lineRule (LocalRule.ofWolfram 170)) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y i => y (i - 1), fun x => ?_, fun y => ?_⟩
  · funext i; rw [lineRule_ofWolfram_170]; simp
  · funext i; rw [lineRule_ofWolfram_170]; simp

/-- Rule `240` is a bijection of the line, with inverse the left shift. -/
theorem bijective_lineRule_ofWolfram_240 :
    Function.Bijective (lineRule (LocalRule.ofWolfram 240)) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y i => y (i + 1), fun x => ?_, fun y => ?_⟩
  · funext i; rw [lineRule_ofWolfram_240]; simp
  · funext i; rw [lineRule_ofWolfram_240]; simp

/-- Rule `51` is a bijection of the line, its own inverse. -/
theorem bijective_lineRule_ofWolfram_51 : Function.Bijective (lineRule (LocalRule.ofWolfram 51)) :=
    by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y i => 1 + y i, fun x => ?_, fun y => ?_⟩
  · funext i; rw [lineRule_ofWolfram_51]; exact one_add_one_add _
  · funext i; rw [lineRule_ofWolfram_51]; exact one_add_one_add _

/-- Rule `85` is a bijection of the line, with inverse the complemented right shift. -/
theorem bijective_lineRule_ofWolfram_85 : Function.Bijective (lineRule (LocalRule.ofWolfram 85)) :=
    by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y i => 1 + y (i - 1), fun x => ?_, fun y => ?_⟩
  · funext i; rw [lineRule_ofWolfram_85]; simpa using one_add_one_add (x i)
  · funext i; rw [lineRule_ofWolfram_85]; simpa using one_add_one_add (y i)

/-- Rule `15` is a bijection of the line, with inverse the complemented left shift. -/
theorem bijective_lineRule_ofWolfram_15 : Function.Bijective (lineRule (LocalRule.ofWolfram 15)) :=
    by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y i => 1 + y (i + 1), fun x => ?_, fun y => ?_⟩
  · funext i; rw [lineRule_ofWolfram_15]; simpa using one_add_one_add (x i)
  · funext i; rw [lineRule_ofWolfram_15]; simpa using one_add_one_add (y i)

/-! ## The growing width at the two identity-like quiescent numbers -/

open Nonautonomous in
/-- Rule `204`, as a rule on the finitely supported configurations, is the identity. -/
theorem finRule_ofWolfram_204 (hq : LocalRule.ofWolfram 204 0 0 0 = 0) : finRule
    (LocalRule.ofWolfram 204) hq = id := by
  funext s
  ext i
  rw [finRule_apply, LocalRule.ofWolfram_204]
  rfl

/-- Rule `240`, as a rule on the finitely supported configurations, is `rule240`. -/
theorem finRule_ofWolfram_240 (hq : LocalRule.ofWolfram 240 0 0 0 = 0) : finRule
    (LocalRule.ofWolfram 240) hq = rule240 := by
  funext s
  ext i
  rw [finRule_apply]
  unfold rule240
  rw [finRule_apply, LocalRule.ofWolfram_240]

open Nonautonomous in
/-- **The growing width along the light cone is zero at rule `204`, at every time**, in the
form of `growth_census`; it is `growingWidth_lightCone_id_eq_zero` at `finRule_ofWolfram_204`. -/
theorem growingWidth_lightCone_ofWolfram_204_eq_zero (hq : LocalRule.ofWolfram 204 0 0 0 = 0) (n t :
ℕ) :
    growingWidth (finRule (LocalRule.ofWolfram 204) hq) diam (lightCone n) t = 0 := by
  rw [finRule_ofWolfram_204]
  exact growingWidth_lightCone_id_eq_zero n t

private theorem ones_coe (s : FiniteConfiguration) : NumberConservation.ones ⇑s = s.support.card :=
  by
  unfold NumberConservation.ones
  rw [Finsupp.fun_support_eq, Set.ncard_coe_finset]

private theorem coe_finRule_step (f : LocalRule) (hq : f 0 0 0 = 0)
    (s : FiniteConfiguration) : ⇑(finRule f hq s) = LocalRuleColumns.step f ⇑s :=
  funext fun i => finRule_apply f hq s i

/-- **Among the quiescent numbers, exactly `170`, `184`, `204`, `226` and `240` keep the number of
ones of every finitely supported configuration**, on the carrier `ℤ →₀ ZMod 2`; it is
`NumberConservation.conserves_iff` through `LocalRule.ofWolfram_eq_elementaryRule`. -/
theorem card_support_finRule_ofWolfram_iff (n : Fin 256) (hq : LocalRule.ofWolfram n 0 0 0 = 0) :
    (∀ s : FiniteConfiguration, (finRule (LocalRule.ofWolfram n) hq s).support.card =
      s.support.card)
      ↔ n ∈ ({170, 184, 204, 226, 240} : Finset (Fin 256)) := by
  rw [← NumberConservation.conserves_iff n (by rwa [LocalRule.ofWolfram_eq_elementaryRule] at hq)]
  simp only [LocalRule.ofWolfram_eq_elementaryRule] at hq ⊢
  constructor
  · intro h x hx
    have e := h (Finsupp.ofSupportFinite x hx)
    rw [← ones_coe, ← ones_coe, coe_finRule_step] at e
    exact e
  · intro h s
    have e := h ⇑s (by rw [Finsupp.fun_support_eq]; exact s.support.finite_toSet)
    rw [← coe_finRule_step (ElementaryRuleClasses.elementaryRule n) hq, ones_coe, ones_coe] at e
    exact e

end ECA
