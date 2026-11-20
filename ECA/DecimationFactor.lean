module

public import ECA.Decimation
public import ECA.Growth

/-!
# Rule 90's decimation as a factor map whose image has unbounded growing width
([RuleSpace] §5 Proposition 5.7; the setting is [RuleSpace] §2 Definition 2.1 and
Definition 2.3)

The decimation of rule `90` (`decim`) is a factor map of the light-cone family of an `n`-cell
window, at time scale `2 ^ M`, onto the light-cone family of the `n'`-cell window when
`n = 2 ^ M * n'` (`imageFiber_decim_f90`), and its law is the rule itself. This file adds what the
two modules it joins do not say together: for `0 < M` the decimation is onto but **not injective**,
its factor map does not depend on the time, and the image's growing width is the growing width of
rule `90` along the smaller light cone, which is finite at every time and unbounded
(`growingWidth_lightCone_unbounded_f90`, from the linear lower bound
`linear_le_growingWidth_lightCone_f90_single`).

## Main results

* `not_injective_decim` — for `0 < M` the decimation is not injective: the single at cell `r + 1`
  and the zero state have the same decimation.
* `growingWidth_lightCone_unbounded_f90` — the growing width of rule `90` along the light cone of
  an `n`-cell window exceeds every bound.
* `finite_lightCone` / `growingWidth_lightCone_ne_top` — a light-cone window holds finitely many
  states, so the growing width is finite at every time and every rule.
* `growingWidth_lightCone_f90_ne_top` — that finiteness at rule `90`.
* `decim_f90_factor` — the decimation of rule `90` at `n = 2 ^ M * n'` and `0 < M` is onto, not
  injective, semiconjugate to the rule with a map that does not depend on the time, has the
  light-cone family of the smaller window as its image fibers, and the growing width along that
  family is unbounded.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

open Nonautonomous

/-- **The decimation is not injective for `0 < M`**: the single at cell `r + 1` is nonzero, and
its decimation vanishes, since no cell of the form `r + 2 ^ M * i` equals `r + 1` when `2 ^ M`
exceeds `1`; the zero state has the same decimation. -/
theorem not_injective_decim {M : ℕ} (hM : 0 < M) (r : ℤ) : ¬ Function.Injective (decim M r) := by
  intro hinj
  have hp : (2 : ℤ) ≤ 2 ^ M := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
  have h : decim M r (Finsupp.single (r + 1) (1 : ZMod 2)) = decim M r 0 := by
    ext i
    rw [decim_apply, decim_apply, Finsupp.single_apply]
    have hne : ¬ (r + 1 = r + 2 ^ M * i) := by
      intro h1
      have h2 : (1 : ℤ) = 2 ^ M * i := by linarith
      rcases lt_trichotomy i 0 with hi | hi | hi
      · nlinarith
      · subst hi; simp at h2
      · nlinarith
    simp [hne]
  have := hinj h
  simp at this

/-- **The growing width of rule `90` along a light cone is unbounded**: the single cell is in the
growing part of rule `90`, so the growing width along the light cone of any window exceeds every
bound at some time. -/
theorem growingWidth_lightCone_unbounded_f90 (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth (finRule f90 hq90) diam (lightCone n) t :=
  growingWidth_lightCone_unbounded_of_mem_growingPart single_mem_growingPart_f90 n

/-- A light-cone window holds finitely many states: the states supported on the finite interval
`[-t, n + t)` are determined by their values there, and a function on a finite set to `ZMod 2` has
finitely many values. -/
theorem finite_lightCone (n t : ℕ) : (lightCone n t).Finite := by
  let S : Finset ℤ := Finset.Ico (-(t : ℤ)) ((n : ℤ) + t)
  have himg : ((fun (s : FiniteConfiguration) (i : S) => s i) '' lightCone n t).Finite :=
    Set.toFinite _
  refine Set.Finite.of_finite_image himg ?_
  intro a ha b hb hab
  ext i
  by_cases hi : i ∈ S
  · exact congrFun hab ⟨i, hi⟩
  · have hia : a i = 0 := by
      by_contra h
      have := ha i (Finsupp.mem_support_iff.mpr h)
      exact hi (Finset.mem_Ico.mpr this)
    have hib : b i = 0 := by
      by_contra h
      have := hb i (Finsupp.mem_support_iff.mpr h)
      exact hi (Finset.mem_Ico.mpr this)
    rw [hia, hib]

/-- **The growing width along a light cone is finite at every time**, at every rule: it never
exceeds the width, which is at most the number of merge classes in the finite window. -/
theorem growingWidth_lightCone_ne_top {f : LocalRule} (hq : f 0 0 0 = 0) (n t : ℕ) :
    growingWidth (finRule f hq) diam (lightCone n) t ≠ ⊤ := by
  have h1 := growingWidth_le_width (U := finRule f hq) (size := diam) (Ω := lightCone n) (t := t)
  have h2 := width_le_encard_mergeFiber (finRule f hq) (lightCone n) t
  have hfin : (mergeFiber (finRule f hq) (lightCone n) t).Finite :=
    (finite_lightCone n t).image _
  exact ne_top_of_le_ne_top hfin.encard_lt_top.ne (h1.trans h2)

/-- **The growing width of rule `90` along a light cone is finite at every time.** -/
theorem growingWidth_lightCone_f90_ne_top (n t : ℕ) :
    growingWidth (finRule f90 hq90) diam (lightCone n) t ≠ ⊤ :=
  growingWidth_lightCone_ne_top hq90 n t

/-- **The decimation of rule `90` as a factor map with an image of unbounded growing width**:
for `0 < M` the decimation is onto and not injective, it is a semiconjugacy from the `2 ^ M`-fold
iterate along the dilated light cone of the `2 ^ M * n'`-cell window to rule `90`, with a map that
does not depend on the time, its image fibers are the light-cone family of the `n'`-cell window,
and the growing width of rule `90` along that family exceeds every bound. -/
theorem decim_f90_factor (n' M : ℕ) (hM : 0 < M) :
    Function.Surjective (decim M 0) ∧ ¬ Function.Injective (decim M 0) ∧
    Semiconj ((finRule f90 hq90)^[2 ^ M]) (finRule f90 hq90) (fun _ => decim M 0)
      (fun t => lightCone (2 ^ M * n') (2 ^ M * t)) ∧
    (∀ t, imageFiber (fun _ => decim M 0) (fun t => lightCone (2 ^ M * n') (2 ^ M * t)) t
      = lightCone n' t) ∧
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth (finRule f90 hq90) diam (lightCone n') t :=
  ⟨decim_surjective M 0, not_injective_decim hM 0, nonautonomousSemiconj_decim_f90 (2 ^ M * n') M 0,
    imageFiber_decim_f90 n' M, growingWidth_lightCone_unbounded_f90 n'⟩

end ECA

/-- info: 'ECA.not_injective_decim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_injective_decim

set_option linter.style.longLine false in
/-- info: 'ECA.growingWidth_lightCone_unbounded_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingWidth_lightCone_unbounded_f90

/-- info: 'ECA.finite_lightCone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finite_lightCone

set_option linter.style.longLine false in
/-- info: 'ECA.growingWidth_lightCone_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingWidth_lightCone_ne_top

set_option linter.style.longLine false in
/-- info: 'ECA.growingWidth_lightCone_f90_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingWidth_lightCone_f90_ne_top

/-- info: 'ECA.decim_f90_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_f90_factor
