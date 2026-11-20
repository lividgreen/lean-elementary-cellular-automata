module

public import Batteries.Tactic.OpenPrivate
public import ECA.Growth
import all ECA.EndpointClasses
import all ECA.Growth

/-!
# Translation classes of finite configurations, and the update a table rule induces on them
([RuleSpace] §2)

Two finite configurations are related when one is a translate of the other. A quiescent local rule
commutes with translation, so its global map descends to the quotient, the **translation classes**,
and the support diameter, which translation does not change, is a function of the class. Up to
translation there are finitely many configurations of each support diameter, so a class's forward
orbit under the induced update is infinite exactly when the diameter is unbounded along the orbit
of any representative: that is the growing part of the rule at the diameter
(`Nonautonomous.GrowingPart`).

## Main results

* `FiniteConfiguration.translationSetoid` / `TranslationClass` — the relation and its quotient.
* `LocalRule.classRule` / `LocalRule.classRule_mk` / `LocalRule.classRule_iterate_mk` — the update
  a table rule induces on the classes, and its iterates.
* `TranslationClass.diam` / `TranslationClass.diam_mk` / `TranslationClass.finite_diam_le` — the
  support diameter of a class, and the finitely many classes of diameter at most `D`.
* `LocalRule.finite_range_classRule_iff` — the orbit of a class under the induced update is finite
  exactly when its representative is outside the growing part at the diameter.
* `f204`, `classRule_f204_eq_id`, `classRule_f170_eq_id`, `classRule_f240_eq_id` — the identity
  table and the two shifts induce the identity on the classes.
* `diam_finRule_f90` and `diam_iterate_finRule_f90_single` — a nonzero state's image under rule
  `90` has support diameter two more, so the single cell's iterates have diameters `2 k + 1`.
-/

open private translate_zero translate_support diam_eq' translate_apply
  from ECA.EndpointClasses

open private translate_translate from ECA.Growth

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

open Nonautonomous

/-- **Being a translate of is an equivalence relation** on finite configurations: translation by
`0` is the identity and translations compose by adding the offsets. -/
theorem FiniteConfiguration.equivalence_translate :
    Equivalence (fun x y : FiniteConfiguration => ∃ k : ℤ, y = FiniteConfiguration.translate k x) :=
  { refl := fun x => ⟨0, (translate_zero x).symm⟩
    symm := by
      rintro x y ⟨k, rfl⟩
      exact ⟨-k, by rw [translate_translate, neg_add_cancel, translate_zero]⟩
    trans := by
      rintro x y z ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨b + a, by rw [translate_translate]⟩ }

/-- Two finite configurations are related when one is a translate of the other. -/
def FiniteConfiguration.translationSetoid : Setoid FiniteConfiguration :=
  ⟨_, FiniteConfiguration.equivalence_translate⟩

/-- The finite configurations up to translation. -/
abbrev TranslationClass := Quotient FiniteConfiguration.translationSetoid

/-- A table rule's update on the translation classes, through `LocalRule.finRule_translate`. -/
noncomputable def LocalRule.classRule (f : LocalRule) (hq : f 0 0 0 = 0) :
    TranslationClass → TranslationClass :=
  Quotient.map (finRule f hq) (by
    rintro x y ⟨k, rfl⟩
    exact ⟨k, finRule_translate f hq k x⟩)

/-- The update on the classes sends the class of `x` to the class of its image. -/
theorem LocalRule.classRule_mk (f : LocalRule) (hq : f 0 0 0 = 0) (x : FiniteConfiguration) :
    f.classRule hq ⟦x⟧ = ⟦finRule f hq x⟧ :=
  rfl

/-- The iterates of the update on the classes are the classes of the iterates of the global map. -/
theorem LocalRule.classRule_iterate_mk (f : LocalRule) (hq : f 0 0 0 = 0) (k : ℕ)
    (x : FiniteConfiguration) :
    (f.classRule hq)^[k] ⟦x⟧ = ⟦(finRule f hq)^[k] x⟧ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, classRule_mk, Function.iterate_succ_apply']

/-- The support diameter of a class, `FiniteConfiguration.diam` of any representative. -/
def TranslationClass.diam : TranslationClass → ℕ :=
  Quotient.lift FiniteConfiguration.diam (by
    rintro x y ⟨k, rfl⟩
    exact (diam_translate k x).symm)

/-- The diameter of the class of `x` is the diameter of `x`. -/
theorem TranslationClass.diam_mk (x : FiniteConfiguration) :
    TranslationClass.diam ⟦x⟧ = x.diam :=
  rfl

/-- A translate lies in the class of its source. -/
private theorem mk_translate (k : ℤ) (x : FiniteConfiguration) :
    (⟦translate k x⟧ : TranslationClass) = ⟦x⟧ :=
  (Quotient.sound (show ∃ j : ℤ, translate k x = translate j x from ⟨k, rfl⟩)).symm

/-- A configuration of diameter at most `D` has a translate supported in `[0, D)`. -/
private theorem exists_translate_support_subset {x : FiniteConfiguration} {D : ℕ}
    (hx : x.diam ≤ D) :
    ∃ y : FiniteConfiguration, y.support ⊆ Finset.Ico 0 (D : ℤ) ∧
      (⟦y⟧ : TranslationClass) = ⟦x⟧ := by
  by_cases hne : x.support.Nonempty
  · refine ⟨translate (-(x.support.min' hne)) x, ?_, ?_⟩
    · intro z hz
      rw [translate_support, Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have h1 := Finset.min'_le x.support w hw
      have h2 := Finset.le_max' x.support w hw
      rw [diam_eq' hne] at hx
      rw [Finset.mem_Ico]
      omega
    · exact mk_translate _ x
  · have hz : x = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hne)
    refine ⟨x, ?_, rfl⟩
    rw [hz]
    simp

/-- The finite configurations supported in `[0, D)` are finitely many. -/
private theorem finite_support_subset_Ico (D : ℕ) :
    {x : FiniteConfiguration | x.support ⊆ Finset.Ico 0 (D : ℤ)}.Finite := by
  refine Set.Finite.of_injOn
    (f := fun x (i : Finset.Ico 0 (D : ℤ)) => x i) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
    Set.finite_univ
  intro x hx y hy hxy
  ext i
  by_cases hi : i ∈ Finset.Ico 0 (D : ℤ)
  · exact congrFun hxy ⟨i, hi⟩
  · have h1 : x i = 0 := by
      by_contra h
      exact hi (hx (Finsupp.mem_support_iff.mpr h))
    have h2 : y i = 0 := by
      by_contra h
      exact hi (hy (Finsupp.mem_support_iff.mpr h))
    rw [h1, h2]

/-- **Up to translation there are finitely many configurations of each support diameter**: the
classes of diameter at most `D` form a finite set. -/
theorem TranslationClass.finite_diam_le (D : ℕ) :
    {c : TranslationClass | c.diam ≤ D}.Finite := by
  refine ((finite_support_subset_Ico D).image (fun y => (⟦y⟧ : TranslationClass))).subset ?_
  intro c hc
  induction c using Quotient.inductionOn with | _ x =>
  obtain ⟨y, hy, hyx⟩ := exists_translate_support_subset (x := x) hc
  exact ⟨y, hy, hyx⟩

/-- **The orbit of a class is finite exactly when its representative is outside the growing
part at the diameter**: along the orbit the diameter is bounded exactly when the orbit stays in the
finitely many classes of one diameter bound. -/
theorem LocalRule.finite_range_classRule_iff (f : LocalRule) (hq : f 0 0 0 = 0)
    (x : FiniteConfiguration) :
    (Set.range fun k => (f.classRule hq)^[k] ⟦x⟧).Finite ↔
      x ∉ Nonautonomous.GrowingPart (finRule f hq) FiniteConfiguration.diam := by
  constructor
  · intro hfin hx
    obtain ⟨N, hN⟩ := (hfin.image TranslationClass.diam).bddAbove
    obtain ⟨k, hk⟩ := hx N
    have h : TranslationClass.diam ((f.classRule hq)^[k] ⟦x⟧) ≤ N := hN ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [classRule_iterate_mk, TranslationClass.diam_mk] at h
    omega
  · intro hx
    simp only [GrowingPart, Set.mem_ofPred_eq, not_forall, not_exists, not_lt] at hx
    obtain ⟨N, hN⟩ := hx
    refine (TranslationClass.finite_diam_le N).subset ?_
    rintro _ ⟨k, rfl⟩
    change TranslationClass.diam ((f.classRule hq)^[k] ⟦x⟧) ≤ N
    rw [classRule_iterate_mk, TranslationClass.diam_mk]
    exact hN k

/-- The identity table, `204`. -/
def f204 : LocalRule := fun _a b _c => b

/-- **The identity table induces the identity on the classes**: `finRule f204` is the identity. -/
theorem classRule_f204_eq_id : f204.classRule (by decide) = id := by
  funext c
  induction c using Quotient.inductionOn with | _ x =>
  rw [LocalRule.classRule_mk]
  congr 1
  ext i
  rw [finRule_apply]
  rfl

/-- **The left shift induces the identity on the classes**: `finRule f170` translates by `-1`. -/
theorem classRule_f170_eq_id : f170.classRule hq170 = id := by
  funext c
  induction c using Quotient.inductionOn with | _ x =>
  rw [LocalRule.classRule_mk]
  have hx : finRule f170 hq170 x = translate (-1) x := by
    ext i
    have h := translate_apply (-1) (i + 1) x
    rw [show i + 1 + -1 = i by ring] at h
    rw [h, show finRule f170 hq170 x = rule170 x from rfl, rule170_apply]
  rw [hx, mk_translate]
  rfl

/-- **The right shift induces the identity on the classes**: `finRule f240` translates by `1`. -/
theorem classRule_f240_eq_id : f240.classRule hq240 = id := by
  funext c
  induction c using Quotient.inductionOn with | _ x =>
  rw [LocalRule.classRule_mk]
  have hx : finRule f240 hq240 x = translate 1 x := by
    ext i
    have h := translate_apply 1 (i - 1) x
    rw [show i - 1 + 1 = i by ring] at h
    rw [h, show finRule f240 hq240 x = rule240 x from rfl, rule240_apply]
  rw [hx, mk_translate]
  rfl

/-- **Rule `90` widens a nonzero state by two cells**: the leftmost cell moves left by one and the
rightmost right by one. -/
theorem diam_finRule_f90 {s : FiniteConfiguration} (hs : s ≠ 0) :
    (finRule f90 (by decide) s).diam = s.diam + 2 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hne' : (finRule f90 (by decide) s).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr
      (finRule_ne_zero_of_leftTap (f := f90) (hq := by decide) (by decide) hs)
  rw [diam_eq' hne', diam_eq' hne,
    finRule_min'_of_leftTap (f := f90) (hq := by decide) (by decide) hne hne',
    finRule_max'_of_rightTap (f := f90) (hq := by decide) (by decide) hne hne']
  have := Finset.min'_le_max' s.support hne
  omega

/-- **The single cell's iterates under rule `90` have diameters `2 k + 1`**. -/
theorem diam_iterate_finRule_f90_single (k : ℕ) :
    ((finRule f90 (by decide))^[k] (Finsupp.single (0 : ℤ) (1 : ZMod 2))).diam = 2 * k + 1 := by
  induction k with
  | zero => simp [diam]
  | succ k ih =>
    have hne : (finRule f90 (by decide))^[k] (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ≠ 0 := by
      intro h
      rw [h] at ih
      simp [diam] at ih
    rw [Function.iterate_succ_apply', diam_finRule_f90 hne, ih]
    ring

end ECA

/-! ## Axiom audit

The capstone above is `#print axioms`-clean on the standard triple, and the guard below makes that
build-enforced. -/

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.finite_range_classRule_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.finite_range_classRule_iff
