module

public import ECA.BlockCode
public import ECA.Growth
public import ECA.LightConeWidth
public import Mathlib.Tactic.IntervalCases
public import Nonautonomous.MergeQuotient
import all ECA.BlockCode
import all ECA.EndpointClasses

/-!
# Tables `188` and `230`: no sliding block code with an injective law, from a statement on ends
([RuleSpace] §2 Proposition 2.6(ii) for the merge invariance)

Rule `188` is `f (l, c, r) = (l xor c) or (c and r)`: it sends `111`, `101`, `100`, `011` and `010`
to `1` and `110`, `001` and `000` to `0`. Its leftmost set cell stays set and stays leftmost
(`010` and `011` give `1`, `001` gives `0`) while its rightmost set cell moves out one cell a step
(`100` gives `1`), so the diameter of every nonzero finite configuration grows by one a step
(`mem_growingPart_f188`). Rule `230` is its mirror (`LocalRule.mirrorRule`).

The predicate `LocalRule.EndsDetermine f hq` says that two finite configurations whose supports lie
in `[a, b]`, with `a < b`, which are both set at `a` and at `b` and agree at `b - 1`, merge. A
sliding block code of window `L` read through a semiconjugacy with an injective law is constant on
merged states of a fiber (`Nonautonomous.Semiconj.merges_invariant`), so it takes the same value on
a family of states that all merge with one state and that read every window of `L` cells at the
cell `0`: the value at the zero window, which is zero
(`LocalRule.blockCode_eq_zero_of_window_merges`). At rule `188` the family `1 w 0 1`, set cells at
`-1` and `L + 1` with the window `w` on the cells `0` to `L - 1`, satisfies the hypotheses of the
predicate; at rule `230` the mirrored family `1 0 w 1`, set cells at `-2` and `L`, does, through
reflection. The predicate holds at rule `188` (`endsDetermine_f188`): after `b - a + 1` steps both
configurations are settled, with no two adjacent zero cells and no word `010` between the ends, and
a settled configuration steps by a left shift of everything but the cells at the right end, so two
settled states with the same ends and the same cell before the right end meet. The two exclusions
are conditional on the predicate, and unconditional through it.

## Main results

* `f188`, `f230` with `hq188`, `hq230` — the two rules by Wolfram's bit convention
  (`wolframRule`), quiescent.
* `LocalRule.EndsDetermine` — two finite configurations with the same ends and the same cell before
  the right end merge.
* `FiniteConfiguration.markedWindow` / `FiniteConfiguration.markedWindowLeft` — the states `1 w 0 1`
  and `1 0 w 1`.
* `mem_growingPart_f188` — at rule `188` every nonzero finite configuration is in the growing part
  under the support diameter.
* `LocalRule.blockCode_eq_zero_of_window_merges` — a sliding block code whose local rule sends the
  zero window to zero, read through a semiconjugacy with an injective law on positively invariant
  fibers holding a family of states that read every window and merge with the state of the zero
  window, is the zero code.
* `LocalRule.blockCode_eq_zero_of_window_merges_nonvacuous` — the hypotheses of that statement hold
  together, at table `188` with window `1` and the zero local rule.
* `blockCode_eq_zero_of_injective_law_f188` and `blockCode_eq_zero_of_injective_law_f230` — at each
  of the two tables, given `LocalRule.EndsDetermine` at rule `188`, a sliding block code of any
  window with an injective law, a semiconjugacy on the light cone of any window restricted to the
  growing part, is the zero code.
* `endsDetermine_f188` — at rule `188` two finite configurations with the same ends and the same
  cell before the right end merge.
* `blockCode_eq_zero_of_injective_law_f188'` and `blockCode_eq_zero_of_injective_law_f230'` — the
  same two statements with no hypothesis on the ends.
* `blockCode_eq_zero_of_injective_law_f188_nonvacuous` and
  `blockCode_eq_zero_of_injective_law_f230_nonvacuous` — the hypotheses of the two conditional
  statements hold together, at window `1`, the zero local rule and the identity as the law.
-/

@[expose] public section

namespace ECA

/-- Rule `188`: `(l xor c) or (c and r)`. -/
def f188 : LocalRule := wolframRule 188

/-- Rule `230`: the mirror of rule `188`. -/
def f230 : LocalRule := wolframRule 230

/-- Rule `188` is quiescent. -/
theorem hq188 : f188 0 0 0 = 0 := by decide

/-- Rule `230` is quiescent. -/
theorem hq230 : f230 0 0 0 = 0 := by decide

/-- Rule `230` is the mirror of rule `188`. -/
private theorem f230_eq_mirrorRule : f230 = LocalRule.mirrorRule f188 := by
  funext a b c
  revert a b c
  decide

namespace LocalRule

/-- **Two finite configurations with the same ends and the same cell before the right end
merge**: for all cells `a < b`, two finite configurations supported in `[a, b]`, both set at `a`
and at `b` and with the same value at `b - 1`, are identified by some number of steps. -/
def EndsDetermine (f : LocalRule) (hq : f 0 0 0 = 0) : Prop :=
  ∀ (a b : ℤ), a < b → ∀ s s' : FiniteConfiguration,
    (∀ i ∈ s.support, a ≤ i ∧ i ≤ b) → (∀ i ∈ s'.support, a ≤ i ∧ i ≤ b) →
    s a = 1 → s b = 1 → s' a = 1 → s' b = 1 → s (b - 1) = s' (b - 1) →
    Nonautonomous.Merges (finRule f hq) s s'

end LocalRule

namespace FiniteConfiguration

/-- **The marked window state `1 w 0 1`**: a set cell at each of `-1` and `L + 1`, the window `w`
on the cells `0` to `L - 1`, and zeros elsewhere, the cell `L` included. -/
noncomputable def markedWindow (L : ℕ) (w : Fin L → ZMod 2) : FiniteConfiguration :=
  Finsupp.onFinset (Finset.Icc (-1 : ℤ) ((L : ℤ) + 1))
    (fun i => if i = -1 ∨ i = (L : ℤ) + 1 then 1
      else if h : 0 ≤ i ∧ i < (L : ℤ) then w ⟨i.toNat, by omega⟩ else 0) (by
      intro i hi
      by_contra hcon
      rw [Finset.mem_Icc] at hcon
      apply hi
      have h1 : ¬ (i = -1 ∨ i = (L : ℤ) + 1) := by omega
      have h2 : ¬ (0 ≤ i ∧ i < (L : ℤ)) := by omega
      simp [h1, h2])

/-- **The mirrored marked window state `1 0 w 1`**: a set cell at each of `-2` and `L`, the cell
`-1` zero, the window `w` on the cells `0` to `L - 1`, and zeros elsewhere. -/
noncomputable def markedWindowLeft (L : ℕ) (w : Fin L → ZMod 2) : FiniteConfiguration :=
  Finsupp.onFinset (Finset.Icc (-2 : ℤ) (L : ℤ))
    (fun i => if i = -2 ∨ i = (L : ℤ) then 1
      else if h : 0 ≤ i ∧ i < (L : ℤ) then w ⟨i.toNat, by omega⟩ else 0) (by
      intro i hi
      by_contra hcon
      rw [Finset.mem_Icc] at hcon
      apply hi
      have h1 : ¬ (i = -2 ∨ i = (L : ℤ)) := by omega
      have h2 : ¬ (0 ≤ i ∧ i < (L : ℤ)) := by omega
      simp [h1, h2])

private theorem markedWindow_apply_end (L : ℕ) (w : Fin L → ZMod 2) (i : ℤ)
    (h : i = -1 ∨ i = (L : ℤ) + 1) : markedWindow L w i = 1 := by
  simp [markedWindow, Finsupp.onFinset_apply, h]

/-- The window of the marked window state is the window it was built from. -/
private theorem markedWindow_apply_window (L : ℕ) (w : Fin L → ZMod 2) (k : Fin L) :
    markedWindow L w (0 + (k : ℕ)) = w k := by
  have hk := k.2
  have h1 : ¬ ((0 : ℤ) + (k : ℕ) = -1 ∨ (0 : ℤ) + (k : ℕ) = (L : ℤ) + 1) := by omega
  have h2 : 0 ≤ (0 : ℤ) + (k : ℕ) ∧ (0 : ℤ) + (k : ℕ) < (L : ℤ) := by omega
  simp only [markedWindow, Finsupp.onFinset_apply]
  split_ifs
  congr 1
  ext
  simp

/-- The cell `L`, before the right end, of the marked window state is zero. -/
private theorem markedWindow_apply_before (L : ℕ) (w : Fin L → ZMod 2) :
    markedWindow L w (L : ℤ) = 0 := by
  have h1 : ¬ ((L : ℤ) = -1 ∨ (L : ℤ) = (L : ℤ) + 1) := by omega
  have h2 : ¬ (0 ≤ (L : ℤ) ∧ (L : ℤ) < (L : ℤ)) := by omega
  simp only [markedWindow, Finsupp.onFinset_apply, h1, h2, ↓reduceIte, ↓reduceDIte]

/-- The support of the marked window state lies between its ends. -/
private theorem markedWindow_support (L : ℕ) (w : Fin L → ZMod 2) :
    ∀ i ∈ (markedWindow L w).support, -1 ≤ i ∧ i ≤ (L : ℤ) + 1 := by
  intro i hi
  have hb := Finsupp.support_onFinset_subset hi
  rw [Finset.mem_Icc] at hb
  exact hb

private theorem markedWindowLeft_apply_end (L : ℕ) (w : Fin L → ZMod 2) (i : ℤ)
    (h : i = -2 ∨ i = (L : ℤ)) : markedWindowLeft L w i = 1 := by
  simp [markedWindowLeft, Finsupp.onFinset_apply, h]

/-- The window of the mirrored marked window state is the window it was built from. -/
private theorem markedWindowLeft_apply_window (L : ℕ) (w : Fin L → ZMod 2) (k : Fin L) :
    markedWindowLeft L w (0 + (k : ℕ)) = w k := by
  have hk := k.2
  have h1 : ¬ ((0 : ℤ) + (k : ℕ) = -2 ∨ (0 : ℤ) + (k : ℕ) = (L : ℤ)) := by omega
  have h2 : 0 ≤ (0 : ℤ) + (k : ℕ) ∧ (0 : ℤ) + (k : ℕ) < (L : ℤ) := by omega
  simp only [markedWindowLeft, Finsupp.onFinset_apply]
  split_ifs
  congr 1
  ext
  simp

/-- The cell `-1` of the mirrored marked window state is zero. -/
private theorem markedWindowLeft_apply_gap (L : ℕ) (w : Fin L → ZMod 2) :
    markedWindowLeft L w (-1) = 0 := by
  have h1 : ¬ ((-1 : ℤ) = -2 ∨ (-1 : ℤ) = (L : ℤ)) := by omega
  have h2 : ¬ (0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < (L : ℤ)) := by omega
  simp only [markedWindowLeft, Finsupp.onFinset_apply, h1, h2, ↓reduceIte, ↓reduceDIte]

/-- The support of the mirrored marked window state lies between its ends. -/
private theorem markedWindowLeft_support (L : ℕ) (w : Fin L → ZMod 2) :
    ∀ i ∈ (markedWindowLeft L w).support, -2 ≤ i ∧ i ≤ (L : ℤ) := by
  intro i hi
  have hb := Finsupp.support_onFinset_subset hi
  rw [Finset.mem_Icc] at hb
  exact hb

/-- A cell of a reflected finite configuration is the cell opposite it. -/
private theorem reflect_apply_cell (s : FiniteConfiguration) (x : ℤ) : reflect s x = s (-x) := by
  have h := Finsupp.mapDomain_apply_of_injective
    (neg_injective : Function.Injective (Neg.neg : ℤ → ℤ)) s (-x)
  rw [neg_neg] at h
  exact h

end FiniteConfiguration

namespace LocalRule

/-- **A sliding block code with an injective law is zero on a family of windows that merge**: if a
family of states, one for each window of `L` cells, reads that window at the cell `0`, merges with
the member of the zero window, and lies in positively invariant fibers to which a sliding block
code of that window, whose local rule sends the zero window to zero, is semiconjugate with an
injective law, the code is zero. The code takes one value on merged states of a fiber
([RuleSpace] §2 Proposition 2.6(ii), the universality of the merge quotient). -/
theorem blockCode_eq_zero_of_window_merges (f : LocalRule) (hq : f 0 0 0 = 0) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (c : (Fin L → ZMod 2) → FiniteConfiguration)
    (hwin : ∀ (w : Fin L → ZMod 2) (k : Fin L), c w (0 + (k : ℕ)) = w k)
    (hmerge : ∀ w, Nonautonomous.Merges (finRule f hq) (c w) (c 0))
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    {Ω : ℕ → Set FiniteConfiguration} (hadv : Nonautonomous.PositivelyInvariant (finRule f hq) Ω)
    (hsq : Nonautonomous.Semiconj (finRule f hq) F
      (fun _ => FiniteConfiguration.blockCode L g hg) Ω)
    (t : ℕ) (hmem : ∀ w, c w ∈ Ω t) :
    g = 0 := by
  funext w
  have h := Nonautonomous.Semiconj.merges_invariant hF hadv hsq t (c w) (hmem w) (c 0) (hmem 0)
    (hmerge w)
  have h0 := congrArg (fun y : FiniteConfiguration => y 0) h
  simp only [FiniteConfiguration.blockCode_apply] at h0
  have e1 : (fun k : Fin L => c w (0 + (k : ℕ))) = w := funext (hwin w)
  have e2 : (fun k : Fin L => c 0 (0 + (k : ℕ))) = 0 := funext (hwin 0)
  rw [e1, e2] at h0
  rw [h0, hg]
  rfl

end LocalRule

/-! ## The growing part at rule `188` -/

/-- **Every nonzero finite configuration is in the growing part of rule `188` under the support
diameter**: the leftmost set cell stays set and stays leftmost (`010` and `011` give `1`, `001`
gives `0`) while the rightmost moves out one cell a step (`100` gives `1`), so the diameter grows by
one a step. -/
theorem mem_growingPart_f188 {s : FiniteConfiguration} (hs : s ≠ 0) :
    s ∈ Nonautonomous.GrowingPart (LocalRule.finRule f188 hq188) FiniteConfiguration.diam := by
  have h1 : f188 1 0 0 = 1 := by decide
  have h2 : f188 0 0 1 = 0 := by decide
  have h3 : f188 0 1 0 = 1 := by decide
  have h4 : f188 0 1 1 = 1 := by decide
  have key : Nonautonomous.GrowingPart (LocalRule.finRule f188 hq188) FiniteConfiguration.diam =
      {s | s ≠ 0} := by
    refine growingPart_eq_ne_zero_of_moves (U := LocalRule.finRule f188 hq188) (a := 0) (b := 1)
      (fun {s} => ⟨fun h => ?_, fun h => finRule_eq_zero_of_eq_zero f188 hq188 h⟩)
      (fun {s} hne hne' => by
        rw [LocalRule.finRule_min'_of_leftHold (f := f188) (hq := hq188) h2 h3 h4 hne hne',
          sub_zero])
      (fun {s} hne hne' => LocalRule.finRule_max'_of_rightTap (f := f188) (hq := hq188)
        h1 hne hne')
      (by decide)
    by_contra hs
    exact LocalRule.finRule_ne_zero_of_rightTap (f := f188) (hq := hq188) h1 hs h
  rw [key]
  exact hs

/-! ## The exclusions -/

/-- Every marked window state lies in the light cone at `L + 2`. -/
private theorem markedWindow_mem_lightCone (n L : ℕ) (w : Fin L → ZMod 2) :
    FiniteConfiguration.markedWindow L w ∈ lightCone n (L + 2) := by
  intro i hi
  have hb := FiniteConfiguration.markedWindow_support L w i hi
  push_cast
  omega

/-- Every mirrored marked window state lies in the light cone at `L + 2`. -/
private theorem markedWindowLeft_mem_lightCone (n L : ℕ) (w : Fin L → ZMod 2) :
    FiniteConfiguration.markedWindowLeft L w ∈ lightCone n (L + 2) := by
  intro i hi
  have hb := FiniteConfiguration.markedWindowLeft_support L w i hi
  push_cast
  omega

/-- A marked window state is nonzero: it is set at `-1`. -/
private theorem markedWindow_ne_zero (L : ℕ) (w : Fin L → ZMod 2) :
    FiniteConfiguration.markedWindow L w ≠ 0 := by
  intro h
  have := FiniteConfiguration.markedWindow_apply_end L w (-1) (Or.inl rfl)
  rw [h] at this
  exact absurd this (by decide)

/-- Two marked window states with different windows merge, at a table whose ends determine. -/
private theorem merges_markedWindow {f : LocalRule} {hq : f 0 0 0 = 0}
    (hends : LocalRule.EndsDetermine f hq) (L : ℕ) (w : Fin L → ZMod 2) :
    Nonautonomous.Merges (LocalRule.finRule f hq) (FiniteConfiguration.markedWindow L w)
      (FiniteConfiguration.markedWindow L 0) :=
  hends (-1) ((L : ℤ) + 1) (by omega) _ _ (FiniteConfiguration.markedWindow_support L w)
    (FiniteConfiguration.markedWindow_support L 0)
    (FiniteConfiguration.markedWindow_apply_end L w _ (Or.inl rfl))
    (FiniteConfiguration.markedWindow_apply_end L w _ (Or.inr rfl))
    (FiniteConfiguration.markedWindow_apply_end L 0 _ (Or.inl rfl))
    (FiniteConfiguration.markedWindow_apply_end L 0 _ (Or.inr rfl))
    (by
      rw [show (L : ℤ) + 1 - 1 = L by ring, FiniteConfiguration.markedWindow_apply_before,
        FiniteConfiguration.markedWindow_apply_before])

/-- The reflection of a mirrored marked window state: set at `-L` and `2`, zero at `1`. -/
private theorem merges_reflect_markedWindowLeft {f : LocalRule} {hq : f 0 0 0 = 0}
    (hends : LocalRule.EndsDetermine f hq) (L : ℕ) (w : Fin L → ZMod 2) :
    Nonautonomous.Merges (LocalRule.finRule f hq)
      (FiniteConfiguration.reflect (FiniteConfiguration.markedWindowLeft L w))
      (FiniteConfiguration.reflect (FiniteConfiguration.markedWindowLeft L 0)) := by
  have hsupp : ∀ w' : Fin L → ZMod 2,
      ∀ i ∈ (FiniteConfiguration.reflect (FiniteConfiguration.markedWindowLeft L w')).support,
        -(L : ℤ) ≤ i ∧ i ≤ 2 := by
    intro w' i hi
    rw [Finsupp.mem_support_iff, FiniteConfiguration.reflect_apply_cell] at hi
    have := FiniteConfiguration.markedWindowLeft_support L w' (-i)
      (Finsupp.mem_support_iff.mpr hi)
    omega
  refine hends (-(L : ℤ)) 2 (by omega) _ _ (hsupp w) (hsupp 0) ?_ ?_ ?_ ?_ ?_
  · rw [FiniteConfiguration.reflect_apply_cell, neg_neg]
    exact FiniteConfiguration.markedWindowLeft_apply_end L w _ (Or.inr rfl)
  · rw [FiniteConfiguration.reflect_apply_cell]
    exact FiniteConfiguration.markedWindowLeft_apply_end L w _ (Or.inl rfl)
  · rw [FiniteConfiguration.reflect_apply_cell, neg_neg]
    exact FiniteConfiguration.markedWindowLeft_apply_end L 0 _ (Or.inr rfl)
  · rw [FiniteConfiguration.reflect_apply_cell]
    exact FiniteConfiguration.markedWindowLeft_apply_end L 0 _ (Or.inl rfl)
  · rw [FiniteConfiguration.reflect_apply_cell, FiniteConfiguration.reflect_apply_cell,
      show -(2 - 1 : ℤ) = -1 by norm_num, FiniteConfiguration.markedWindowLeft_apply_gap,
      FiniteConfiguration.markedWindowLeft_apply_gap]

/-- The iterate of the mirror rule at a reflected state is the reflection of the iterate. -/
private theorem iterate_finRule_mirrorRule_reflect (f : LocalRule) (hq : f 0 0 0 = 0)
    (s : FiniteConfiguration) :
    ∀ k : ℕ, (LocalRule.finRule (LocalRule.mirrorRule f) hq)^[k] (FiniteConfiguration.reflect s) =
      FiniteConfiguration.reflect ((LocalRule.finRule f hq)^[k] s)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      iterate_finRule_mirrorRule_reflect f hq s k, LocalRule.finRule_mirrorRule_reflect]

/-- **At a table whose mirror ends determine, the mirrored marked window states merge**. -/
private theorem merges_markedWindowLeft_of_mirror {g f : LocalRule}
    (hg : g = LocalRule.mirrorRule f) {hq : f 0 0 0 = 0} (hqg : g 0 0 0 = 0)
    (hends : LocalRule.EndsDetermine f hq) (L : ℕ) (w : Fin L → ZMod 2) :
    Nonautonomous.Merges (LocalRule.finRule g hqg) (FiniteConfiguration.markedWindowLeft L w)
      (FiniteConfiguration.markedWindowLeft L 0) := by
  subst hg
  obtain ⟨k, hk⟩ := merges_reflect_markedWindowLeft hends L w
  refine ⟨k, ?_⟩
  rw [← FiniteConfiguration.reflect_reflect (FiniteConfiguration.markedWindowLeft L w),
    ← FiniteConfiguration.reflect_reflect (FiniteConfiguration.markedWindowLeft L 0),
    iterate_finRule_mirrorRule_reflect f hq, iterate_finRule_mirrorRule_reflect f hq, hk]

/-- **A mirrored marked window state is in the growing part of the mirror of rule `188`**: its
reflection is nonzero, so in the growing part of rule `188`. -/
private theorem markedWindowLeft_mem_growingPart {g : LocalRule}
    (hg : g = LocalRule.mirrorRule f188) (hqg : g 0 0 0 = 0) (L : ℕ) (w : Fin L → ZMod 2) :
    FiniteConfiguration.markedWindowLeft L w ∈
      Nonautonomous.GrowingPart (LocalRule.finRule g hqg) FiniteConfiguration.diam := by
  subst hg
  have hY : FiniteConfiguration.reflect (FiniteConfiguration.markedWindowLeft L w) ≠ 0 := by
    intro h
    have h1 := FiniteConfiguration.markedWindowLeft_apply_end L w (-2) (Or.inl rfl)
    have h2 := congrArg (fun y : FiniteConfiguration => y 2) h
    simp only [FiniteConfiguration.reflect_apply_cell, Finsupp.coe_zero, Pi.zero_apply] at h2
    rw [show -(2 : ℤ) = -2 by norm_num, h1] at h2
    exact absurd h2 (by decide)
  have hmem := FiniteConfiguration.reflect_mem_growingPart_mirrorRule (mem_growingPart_f188 hY)
  rw [FiniteConfiguration.reflect_reflect] at hmem
  exact hmem

/-- A cell left of the marked window state is zero. -/
private theorem FiniteConfiguration.markedWindow_apply_of_lt (L : ℕ) (w : Fin L → ZMod 2) (i : ℤ)
    (h : i < -1) : FiniteConfiguration.markedWindow L w i = 0 := by
  have h1 : ¬ (i = -1 ∨ i = (L : ℤ) + 1) := by omega
  have h2 : ¬ (0 ≤ i ∧ i < (L : ℤ)) := by omega
  simp only [FiniteConfiguration.markedWindow, Finsupp.onFinset_apply, h1, h2, ↓reduceIte,
    ↓reduceDIte]

/-- A cell right of the marked window state is zero. -/
private theorem FiniteConfiguration.markedWindow_apply_of_gt (L : ℕ) (w : Fin L → ZMod 2) (i : ℤ)
    (h : (L : ℤ) + 1 < i) : FiniteConfiguration.markedWindow L w i = 0 := by
  have h1 : ¬ (i = -1 ∨ i = (L : ℤ) + 1) := by omega
  have h2 : ¬ (0 ≤ i ∧ i < (L : ℤ)) := by omega
  simp only [FiniteConfiguration.markedWindow, Finsupp.onFinset_apply, h1, h2, ↓reduceIte,
    ↓reduceDIte]

/-- The cells of the marked window state `1 1 0 1` at window one. -/
private theorem markedWindow_one_apply_one (j : ℤ) :
    FiniteConfiguration.markedWindow 1 (fun _ => 1) j =
      if j = -1 ∨ j = 0 ∨ j = 2 then 1 else 0 := by
  simp only [FiniteConfiguration.markedWindow, Finsupp.onFinset_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The cells of the marked window state `1 0 0 1` at window one. -/
private theorem markedWindow_one_apply_zero (j : ℤ) :
    FiniteConfiguration.markedWindow 1 0 j = if j = -1 ∨ j = 2 then 1 else 0 := by
  simp only [FiniteConfiguration.markedWindow, Finsupp.onFinset_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- At window one, the states `1 1 0 1` and `1 0 0 1` meet after three steps of rule `188`. -/
private theorem merges_markedWindow_one :
    Nonautonomous.Merges (LocalRule.finRule f188 hq188)
      (FiniteConfiguration.markedWindow 1 (fun _ => 1)) (FiniteConfiguration.markedWindow 1 0) := by
  refine ⟨3, ?_⟩
  ext i
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, LocalRule.finRule_apply]
  by_cases hl : i ≤ -5
  · simp (disch := omega) only [FiniteConfiguration.markedWindow_apply_of_lt]
  by_cases hr : 6 ≤ i
  · simp (disch := omega) only [FiniteConfiguration.markedWindow_apply_of_gt]
  have hi : -4 ≤ i ∧ i ≤ 5 := by omega
  obtain ⟨hi1, hi2⟩ := hi
  simp only [markedWindow_one_apply_one, markedWindow_one_apply_zero]
  interval_cases i <;> decide

/-- **The generic statement's hypotheses are jointly satisfiable**, at table `188` with window `1`,
the zero local rule, the identity as the law, the marked window family, and the light cone of the
one-cell window restricted to the growing part at time `3`: the table is quiescent, the local rule
sends the zero window to zero, the family reads every window at the cell `0`, every member merges
with the member of the zero window, the law is injective, the fibers are positively invariant, the
code is a semiconjugacy, and every member lies in the fiber. The conclusion forces the code to be
zero, so this shows only that the hypotheses are consistent. -/
theorem LocalRule.blockCode_eq_zero_of_window_merges_nonvacuous :
    f188 0 0 0 = 0 ∧ (0 : (Fin 1 → ZMod 2) → ZMod 2) 0 = 0 ∧
      (∀ (w : Fin 1 → ZMod 2) (k : Fin 1),
        FiniteConfiguration.markedWindow 1 w (0 + (k : ℕ)) = w k) ∧
      (∀ w : Fin 1 → ZMod 2, Nonautonomous.Merges (LocalRule.finRule f188 hq188)
        (FiniteConfiguration.markedWindow 1 w) (FiniteConfiguration.markedWindow 1 0)) ∧
      Function.Injective (id : FiniteConfiguration → FiniteConfiguration) ∧
      Nonautonomous.PositivelyInvariant (LocalRule.finRule f188 hq188)
        (fun t => lightCone 1 t ∩
          Nonautonomous.GrowingPart (LocalRule.finRule f188 hq188) FiniteConfiguration.diam) ∧
      Nonautonomous.Semiconj (LocalRule.finRule f188 hq188) id
        (fun _ => FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2)
          (Pi.zero_apply _))
        (fun t => lightCone 1 t ∩
          Nonautonomous.GrowingPart (LocalRule.finRule f188 hq188) FiniteConfiguration.diam) ∧
      ∀ w : Fin 1 → ZMod 2, FiniteConfiguration.markedWindow 1 w ∈
        (fun t => lightCone 1 t ∩
          Nonautonomous.GrowingPart (LocalRule.finRule f188 hq188) FiniteConfiguration.diam) 3 := by
  refine ⟨hq188, Pi.zero_apply _, FiniteConfiguration.markedWindow_apply_window 1, ?_,
    Function.injective_id,
    Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f188 hq188 1),
    fun t s _ => ?_, fun w => ⟨markedWindow_mem_lightCone 1 1 w,
      mem_growingPart_f188 (markedWindow_ne_zero 1 w)⟩⟩
  · intro w
    rcases (by decide : ∀ w : Fin 1 → ZMod 2, w = 0 ∨ w = fun _ => 1) w with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact merges_markedWindow_one
  · ext i
    change FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _)
        (LocalRule.finRule f188 hq188 s) i =
      FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _) s i
    rw [FiniteConfiguration.blockCode_apply, FiniteConfiguration.blockCode_apply]
    rfl

/-- **Table `188` carries no sliding block code with an injective law but zero, if its ends
determine**: given `LocalRule.EndsDetermine` at rule `188`, a sliding block code of any window, a
semiconjugacy from the table's update on the light cone of any window restricted to the growing part
to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f188 (hends : LocalRule.EndsDetermine f188 hq188)
    (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f188 hq188) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f188 hq188) FiniteConfiguration.diam)) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_window_merges f188 hq188 g hg (FiniteConfiguration.markedWindow L)
    (FiniteConfiguration.markedWindow_apply_window L) (merges_markedWindow hends L)
    hF (Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f188 hq188 n)) hsq (L + 2)
    (fun w => ⟨markedWindow_mem_lightCone n L w, mem_growingPart_f188 (markedWindow_ne_zero L w)⟩)

/-- **Table `230` carries no sliding block code with an injective law but zero, if the ends of its
mirror determine**: given `LocalRule.EndsDetermine` at rule `188`, a sliding block code of any
window, a semiconjugacy from the table's update on the light cone of any window restricted to the
growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f230 (hends : LocalRule.EndsDetermine f188 hq188)
    (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f230 hq230) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f230 hq230) FiniteConfiguration.diam)) :
    g = 0 := by
  refine LocalRule.blockCode_eq_zero_of_window_merges f230 hq230 g hg
    (FiniteConfiguration.markedWindowLeft L) (FiniteConfiguration.markedWindowLeft_apply_window L)
    (merges_markedWindowLeft_of_mirror f230_eq_mirrorRule hq230 hends L)
    hF (Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f230 hq230 n)) hsq (L + 2) (fun w => ⟨?_, ?_⟩)
  · exact markedWindowLeft_mem_lightCone n L w
  · exact markedWindowLeft_mem_growingPart f230_eq_mirrorRule hq230 L w

/-! ## The ends determine at rule `188` -/

/-- One step of rule `188` on all configurations of the line. -/
private def step188 (z : ℤ → ZMod 2) : ℤ → ZMod 2 := fun j => f188 (z (j - 1)) (z j) (z (j + 1))

private theorem step188_eq (z : ℤ → ZMod 2) (j m p : ℤ) (hm : m = j - 1) (hp : p = j + 1) :
    step188 z j = f188 (z m) (z j) (z p) := by
  subst hm hp
  rfl

private theorem zmod2_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  revert v
  decide

/-- A cell set at its left neighbour `0` and itself `1` is set after the step. -/
private theorem f188_zero_one (r : ZMod 2) : f188 0 1 r = 1 := by
  revert r
  decide

/-- The cell behind the right end alternates: `110` goes to `0` and `010` to `1`. -/
private theorem f188_one_right_zero (v : ZMod 2) : f188 v 1 0 = 1 + v := by
  revert v
  decide

/-- Two adjacent cells `0` after a step come from three cells `0`. -/
private theorem f188_pair_zero :
    ∀ a b c d : ZMod 2, f188 a b c = 0 → f188 b c d = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

/-- A cell that is zero after a step, with no two adjacent zeros before it, has a zero right
neighbour. -/
private theorem f188_zero_right :
    ∀ l c r : ZMod 2, f188 l c r = 0 → ¬ (l = 0 ∧ c = 0) → r = 0 := by
  decide

/-- A cell whose left neighbour is zero is zero after the step exactly when it is zero. -/
private theorem f188_zero_left : ∀ c r : ZMod 2, f188 0 c r = 0 → c = 0 := by
  decide

/-- With no two adjacent zeros and no word `0 1 0`, a step is a left shift. -/
private theorem f188_shift :
    ∀ l c r : ZMod 2, ¬ (l = 0 ∧ c = 0) → ¬ (c = 0 ∧ r = 0) → ¬ (l = 0 ∧ c = 1 ∧ r = 0) →
      f188 l c r = r := by
  decide

/-- **The ends of an iterate**: from a configuration set at `a` and at `b` and zero outside
`[a, b]`, after `t` steps the cell `a` is set with zeros to its left, the cell `b + t` is set with
zeros to its right, and the cell before it is the cell before `b` plus `t`. -/
private theorem step188_ends (z : ℤ → ZMod 2) (a b : ℤ) (hl : ∀ i, i < a → z i = 0)
    (hr : ∀ i, b < i → z i = 0) (ha : z a = 1) (hb : z b = 1) (t : ℕ) :
    (∀ i, i < a → step188^[t] z i = 0) ∧ step188^[t] z a = 1 ∧
      (∀ i, b + t < i → step188^[t] z i = 0) ∧ step188^[t] z (b + t) = 1 ∧
      step188^[t] z (b + t - 1) = z (b - 1) + t := by
  induction t with
  | zero =>
    exact ⟨hl, ha, fun i hi => hr i (by simpa using hi), by simpa using hb, by simp⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have e1 : b + ((t + 1 : ℕ) : ℤ) = b + t + 1 := by push_cast; ring
    have e2 : b + ((t + 1 : ℕ) : ℤ) - 1 = b + t := by push_cast; ring
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [Function.iterate_succ_apply', step188_eq _ i (i - 1) (i + 1) rfl rfl,
        h1 _ (by omega), h1 _ hi]
      rcases lt_or_eq_of_le (show i + 1 ≤ a by omega) with h | h
      · rw [h1 _ h]
        decide
      · rw [h, h2]
        decide
    · rw [Function.iterate_succ_apply', step188_eq _ a (a - 1) (a + 1) rfl rfl, h1 _ (by omega),
        h2]
      exact f188_zero_one _
    · intro i hi
      rw [e1] at hi
      rw [Function.iterate_succ_apply', step188_eq _ i (i - 1) (i + 1) rfl rfl,
        h3 _ (by omega), h3 _ (by omega), h3 _ (by omega)]
      decide
    · rw [Function.iterate_succ_apply', e1, step188_eq _ (b + t + 1) (b + t) (b + t + 2)
        (by ring) (by ring), h4, h3 _ (by omega), h3 _ (by omega)]
      decide
    · rw [Function.iterate_succ_apply', e2, step188_eq _ (b + t) (b + t - 1) (b + t + 1) rfl rfl,
        h5, h4, h3 _ (by omega), f188_one_right_zero]
      push_cast
      ring

/-- **No pair of zeros is made**: two adjacent zero cells after `t` steps force the configuration
to vanish on the `t + 2` cells from `t` before the first to the second. -/
private theorem step188_zero_pair (z : ℤ → ZMod 2) (t : ℕ) :
    ∀ j : ℤ, step188^[t] z j = 0 → step188^[t] z (j + 1) = 0 →
      ∀ i, j - t ≤ i → i ≤ j + 1 → z i = 0 := by
  induction t with
  | zero =>
    intro j h0 h1 i hi1 hi2
    simp only [Function.iterate_zero, id_eq] at h0 h1
    rcases (by omega : i = j ∨ i = j + 1) with rfl | rfl
    · exact h0
    · exact h1
  | succ t ih =>
    intro j h0 h1 i hi1 hi2
    rw [Function.iterate_succ_apply'] at h0 h1
    rw [step188_eq _ j (j - 1) (j + 1) rfl rfl] at h0
    rw [step188_eq _ (j + 1) j (j + 1 + 1) (by ring) rfl] at h1
    obtain ⟨e1, e2, e3⟩ := f188_pair_zero _ _ _ _ h0 h1
    by_cases hij : i ≤ j
    · exact ih (j - 1) e1 (by rw [sub_add_cancel]; exact e2) i (by omega) (by omega)
    · exact ih j e2 e3 i (by omega) hi2

/-- **From `b - a` steps on, no two adjacent cells of `[a, b + t]` are both zero**. -/
private theorem step188_no_zero_pair_iter (z : ℤ → ZMod 2) (a b : ℤ) (ha : z a = 1)
    (hb : z b = 1) (t : ℕ) (ht : b - a ≤ t) (j : ℤ) (hj1 : a ≤ j) (hj2 : j < b + t) :
    step188^[t] z j = 1 ∨ step188^[t] z (j + 1) = 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : step188^[t] z j = 0 := (zmod2_cases _).resolve_right hcon.1
  have h1 : step188^[t] z (j + 1) = 0 := (zmod2_cases _).resolve_right hcon.2
  have key := step188_zero_pair z t j h0 h1
  by_cases hja : j ≤ a + t
  · have h := key a (by omega) (by omega)
    rw [ha] at h
    exact absurd h (by decide)
  · have h := key b (by omega) (by omega)
    rw [hb] at h
    exact absurd h (by decide)

/-- A configuration set at `a` and at `R`, zero outside `[a, R]`, with no two adjacent zero cells
in `[a, R]`. -/
private abbrev Pre188 (z : ℤ → ZMod 2) (a R : ℤ) : Prop :=
  (∀ i, i < a → z i = 0) ∧ (∀ i, R < i → z i = 0) ∧ z a = 1 ∧ z R = 1 ∧
    ∀ j, a ≤ j → j < R → z j = 1 ∨ z (j + 1) = 1

/-- A configuration of `Pre188` with no word `0 1 0` on three adjacent cells of `[a + 1, R]`. -/
private abbrev Settled188 (z : ℤ → ZMod 2) (a R : ℤ) : Prop :=
  Pre188 z a R ∧ ∀ j, a + 1 ≤ j - 1 → j + 1 ≤ R → ¬ (z (j - 1) = 0 ∧ z j = 1 ∧ z (j + 1) = 0)

private theorem pre188_nz {z : ℤ → ZMod 2} {a R : ℤ} (h : Pre188 z a R) (j : ℤ) (h1 : a ≤ j)
    (h2 : j ≤ R) : ¬ (z j = 0 ∧ z (j + 1) = 0) := by
  obtain ⟨_, _, _, hb, hnz⟩ := h
  rintro ⟨e1, e2⟩
  rcases lt_or_eq_of_le h2 with h | h
  · rcases hnz j h1 h with h' | h'
    · rw [e1] at h'
      exact absurd h' (by decide)
    · rw [e2] at h'
      exact absurd h' (by decide)
  · rw [h] at e1
    rw [hb] at e1
    exact absurd e1 (by decide)

/-- **The interior step**: one step of rule `188` takes a configuration of `Pre188` at `(a, R)` to a
settled configuration at `(a, R + 1)`. -/
private theorem step188_pre_settled {z : ℤ → ZMod 2} {a R : ℤ} (h : Pre188 z a R) :
    Settled188 (step188 z) a (R + 1) := by
  have nz := pre188_nz h
  obtain ⟨hl, hr, ha, hb, hnz⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [step188_eq _ i (i - 1) (i + 1) rfl rfl, hl _ (by omega), hl _ hi]
    rcases lt_or_eq_of_le (show i + 1 ≤ a by omega) with h | h
    · rw [hl _ h]
      decide
    · rw [h, ha]
      decide
  · intro i hi
    rw [step188_eq _ i (i - 1) (i + 1) rfl rfl, hr _ (by omega), hr _ (by omega),
      hr _ (by omega)]
    decide
  · rw [step188_eq _ a (a - 1) (a + 1) rfl rfl, hl _ (by omega), ha]
    exact f188_zero_one _
  · rw [step188_eq _ (R + 1) R (R + 1 + 1) (by ring) rfl, hb, hr _ (by omega), hr _ (by omega)]
    decide
  · intro j h1 h2
    by_contra hc
    push Not at hc
    have h0 : step188 z j = 0 := (zmod2_cases _).resolve_right hc.1
    have h0' : step188 z (j + 1) = 0 := (zmod2_cases _).resolve_right hc.2
    rw [step188_eq _ j (j - 1) (j + 1) rfl rfl] at h0
    rw [step188_eq _ (j + 1) j (j + 1 + 1) (by ring) rfl] at h0'
    obtain ⟨_, p, q⟩ := f188_pair_zero _ _ _ _ h0 h0'
    exact nz j h1 (by omega) ⟨p, q⟩
  · intro j h1 h2 ⟨e1, _, e3⟩
    rw [step188_eq _ (j - 1) (j - 2) j (by ring) (by ring)] at e1
    rw [step188_eq _ (j + 1) j (j + 2) (by ring) (by ring)] at e3
    have n1 := nz (j - 2) (by omega) (by omega)
    rw [show j - 2 + 1 = j - 1 by ring] at n1
    have hj : z j = 0 := f188_zero_right _ _ _ e1 n1
    rw [hj] at e3
    exact nz j (by omega) (by omega) ⟨hj, f188_zero_left _ _ e3⟩

/-- **A settled configuration steps by a left shift** on the cells of `[a + 1, R - 1]`. -/
private theorem step188_shift {z : ℤ → ZMod 2} {a R : ℤ} (h : Settled188 z a R) (j : ℤ)
    (h1 : a + 1 ≤ j) (h2 : j + 1 ≤ R) : step188 z j = z (j + 1) := by
  have nz := pre188_nz h.1
  obtain ⟨⟨_, _, ha, _, _⟩, h010⟩ := h
  rw [step188_eq _ j (j - 1) (j + 1) rfl rfl]
  apply f188_shift
  · have := nz (j - 1) (by omega) (by omega)
    rwa [sub_add_cancel] at this
  · exact nz j (by omega) (by omega)
  · by_cases hj : a + 1 ≤ j - 1
    · exact h010 j hj h2
    · have : j - 1 = a := by omega
      rw [this, ha]
      rintro ⟨e, _⟩
      exact absurd e (by decide)

/-- Two settled configurations agree at every cell not right of `a`. -/
private theorem settled188_left {y y' : ℤ → ZMod 2} {a R R' : ℤ} (hy : Settled188 y a R)
    (hy' : Settled188 y' a R') (i : ℤ) (hi : i ≤ a) : y i = y' i := by
  rcases lt_or_eq_of_le hi with h | h
  · rw [hy.1.1 i h, hy'.1.1 i h]
  · rw [h, hy.1.2.2.1, hy'.1.2.2.1]

/-- **Two settled states meet**: settled at the same `(a, R)` and equal at `R - 1`, their iterates
stay settled at `(a, R + k)` and agree at every cell outside `[a + 1, R - 2 - k]`. -/
private theorem settled188_agree {z z' : ℤ → ZMod 2} {a R : ℤ} (hz : Settled188 z a R)
    (hz' : Settled188 z' a R) (h : z (R - 1) = z' (R - 1)) (k : ℕ) :
    Settled188 (step188^[k] z) a (R + k) ∧ Settled188 (step188^[k] z') a (R + k) ∧
      ∀ i, i ≤ a ∨ R - 1 - k ≤ i → step188^[k] z i = step188^[k] z' i := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, add_zero, sub_zero]
    refine ⟨hz, hz', fun i hi => ?_⟩
    rcases hi with hi | hi
    · exact settled188_left hz hz' i hi
    · rcases lt_trichotomy i (R - 1) with h1 | h1 | h1
      · omega
      · rw [h1]
        exact h
      · rcases lt_or_eq_of_le (show R ≤ i by omega) with h2 | h2
        · rw [hz.1.2.1 i h2, hz'.1.2.1 i h2]
        · rw [← h2, hz.1.2.2.2.1, hz'.1.2.2.2.1]
  | succ k ih =>
    obtain ⟨hY, hY', hag⟩ := ih
    have e : R + ((k + 1 : ℕ) : ℤ) = R + k + 1 := by push_cast; ring
    simp only [Function.iterate_succ_apply', e]
    have s1 := step188_pre_settled hY.1
    have s2 := step188_pre_settled hY'.1
    refine ⟨s1, s2, fun i hi => ?_⟩
    by_cases hia : i ≤ a
    · exact settled188_left s1 s2 i hia
    · have hi' : R - 1 - ((k + 1 : ℕ) : ℤ) ≤ i := hi.resolve_left hia
      by_cases hc : R - k ≤ i
      · rw [step188_eq _ i (i - 1) (i + 1) rfl rfl, step188_eq _ i (i - 1) (i + 1) rfl rfl,
          hag (i - 1) (Or.inr (by omega)), hag i (Or.inr (by omega)),
          hag (i + 1) (Or.inr (by omega))]
      · rw [step188_shift hY i (by omega) (by omega), step188_shift hY' i (by omega) (by omega)]
        exact hag (i + 1) (Or.inr (by omega))

/-- **A configuration settles after `b - a + 1` steps**: from a configuration set at `a` and at `b`
and zero outside `[a, b]`, the iterate after `b - a + 1` steps is settled between `a` and the cell
`b + (b - a + 1)`. -/
private theorem step188_settled_after (z : ℤ → ZMod 2) (a b : ℤ) (hl : ∀ i, i < a → z i = 0)
    (hr : ∀ i, b < i → z i = 0) (ha : z a = 1) (hb : z b = 1) :
    Settled188 (step188^[(b - a).toNat + 1] z) a (b + (((b - a).toNat + 1 : ℕ) : ℤ)) := by
  have ht : b - a ≤ (((b - a).toNat : ℕ) : ℤ) := Int.self_le_toNat _
  obtain ⟨e1, e2, e3, e4, _⟩ := step188_ends z a b hl hr ha hb (b - a).toNat
  have pre : Pre188 (step188^[(b - a).toNat] z) a (b + (((b - a).toNat : ℕ) : ℤ)) :=
    ⟨e1, e3, e2, e4, fun j h1 h2 =>
      step188_no_zero_pair_iter z a b ha hb _ ht j h1 h2⟩
  have e : b + (((b - a).toNat + 1 : ℕ) : ℤ) = b + (((b - a).toNat : ℕ) : ℤ) + 1 := by
    push_cast
    ring
  rw [Function.iterate_succ_apply', e]
  exact step188_pre_settled pre

/-- The iterates of the finite-configuration update are the iterates of the step on cells. -/
private theorem coe_iterate_finRule_f188 (s : FiniteConfiguration) (n : ℕ) :
    ⇑((LocalRule.finRule f188 hq188)^[n] s) = step188^[n] ⇑s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    funext j
    exact LocalRule.finRule_apply f188 hq188 _ j

/-- **At rule `188`, the ends determine**: two finite configurations supported in `[a, b]` with
`a < b`, both set at `a` and at `b` and equal at `b - 1`, are identified by some number of steps.
After `b - a + 1` steps both are settled at the same ends with equal cells before the right end,
and two such settled states meet by left shifts. -/
theorem endsDetermine_f188 : LocalRule.EndsDetermine f188 hq188 := by
  intro a b _ s s' hs hs' ha hb ha' hb' hmid
  have hl : ∀ i, i < a → (⇑s) i = 0 := fun i hi => by
    by_contra hne
    have := (hs i (Finsupp.mem_support_iff.mpr hne)).1
    omega
  have hr : ∀ i, b < i → (⇑s) i = 0 := fun i hi => by
    by_contra hne
    have := (hs i (Finsupp.mem_support_iff.mpr hne)).2
    omega
  have hl' : ∀ i, i < a → (⇑s') i = 0 := fun i hi => by
    by_contra hne
    have := (hs' i (Finsupp.mem_support_iff.mpr hne)).1
    omega
  have hr' : ∀ i, b < i → (⇑s') i = 0 := fun i hi => by
    by_contra hne
    have := (hs' i (Finsupp.mem_support_iff.mpr hne)).2
    omega
  have hset := step188_settled_after ⇑s a b hl hr ha hb
  have hset' := step188_settled_after ⇑s' a b hl' hr' ha' hb'
  have hends := step188_ends ⇑s a b hl hr ha hb ((b - a).toNat + 1)
  have hends' := step188_ends ⇑s' a b hl' hr' ha' hb' ((b - a).toNat + 1)
  have hfront : step188^[(b - a).toNat + 1] ⇑s
      (b + (((b - a).toNat + 1 : ℕ) : ℤ) - 1) =
      step188^[(b - a).toNat + 1] ⇑s' (b + (((b - a).toNat + 1 : ℕ) : ℤ) - 1) := by
    rw [hends.2.2.2.2, hends'.2.2.2.2]
    have : (⇑s) (b - 1) = (⇑s') (b - 1) := hmid
    rw [this]
  obtain ⟨_, _, hag⟩ := settled188_agree hset hset' hfront
    ((b + (((b - a).toNat + 1 : ℕ) : ℤ) - a).toNat)
  refine ⟨(b + (((b - a).toNat + 1 : ℕ) : ℤ) - a).toNat + ((b - a).toNat + 1), ?_⟩
  apply DFunLike.coe_injective
  rw [coe_iterate_finRule_f188, coe_iterate_finRule_f188,
    Function.iterate_add_apply step188 _ ((b - a).toNat + 1) ⇑s,
    Function.iterate_add_apply step188 _ ((b - a).toNat + 1) ⇑s']
  funext i
  rcases le_or_gt i a with h | h
  · exact hag i (Or.inl h)
  · exact hag i (Or.inr (by omega))

/-! ## The unconditional exclusions -/

/-- **Table `188` carries no sliding block code with an injective law but zero**: a sliding block
code of any window, a semiconjugacy from the table's update on the light cone of any window
restricted to the growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f188' (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f188 hq188) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f188 hq188) FiniteConfiguration.diam)) :
    g = 0 :=
  blockCode_eq_zero_of_injective_law_f188 endsDetermine_f188 n g hg hF hsq

/-- **Table `230` carries no sliding block code with an injective law but zero**: a sliding block
code of any window, a semiconjugacy from the table's update on the light cone of any window
restricted to the growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f230' (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f230 hq230) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f230 hq230) FiniteConfiguration.diam)) :
    g = 0 :=
  blockCode_eq_zero_of_injective_law_f230 endsDetermine_f188 n g hg hF hsq

/-- **The hypotheses of the exclusion at table `188` hold together**, at window `1`, the zero local
rule, the identity as the law and the light cone of the one-cell window restricted to the growing
part: the ends determine, the local rule sends the zero window to zero, the law is injective and
the code is a semiconjugacy. The conclusion forces the code to be zero, so this shows only that the
hypotheses are consistent. -/
theorem blockCode_eq_zero_of_injective_law_f188_nonvacuous :
    LocalRule.EndsDetermine f188 hq188 ∧ (0 : (Fin 1 → ZMod 2) → ZMod 2) 0 = 0 ∧
      Function.Injective (id : FiniteConfiguration → FiniteConfiguration) ∧
      Nonautonomous.Semiconj (LocalRule.finRule f188 hq188) id
        (fun _ => FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2)
          (Pi.zero_apply _))
        (fun t => lightCone 1 t ∩
          Nonautonomous.GrowingPart (LocalRule.finRule f188 hq188) FiniteConfiguration.diam) := by
  refine ⟨endsDetermine_f188, Pi.zero_apply _, Function.injective_id, fun t s _ => ?_⟩
  ext i
  change FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _)
      (LocalRule.finRule f188 hq188 s) i =
    FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _) s i
  rw [FiniteConfiguration.blockCode_apply, FiniteConfiguration.blockCode_apply]
  rfl

/-- **The hypotheses of the exclusion at table `230` hold together**, at window `1`, the zero local
rule, the identity as the law and the light cone of the one-cell window restricted to the growing
part: the ends of the mirror determine, the local rule sends the zero window to zero, the law is
injective and the code is a semiconjugacy. The conclusion forces the code to be zero, so this shows
only that the hypotheses are consistent. -/
theorem blockCode_eq_zero_of_injective_law_f230_nonvacuous :
    LocalRule.EndsDetermine f188 hq188 ∧ (0 : (Fin 1 → ZMod 2) → ZMod 2) 0 = 0 ∧
      Function.Injective (id : FiniteConfiguration → FiniteConfiguration) ∧
      Nonautonomous.Semiconj (LocalRule.finRule f230 hq230) id
        (fun _ => FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2)
          (Pi.zero_apply _))
        (fun t => lightCone 1 t ∩
          Nonautonomous.GrowingPart (LocalRule.finRule f230 hq230) FiniteConfiguration.diam) := by
  refine ⟨endsDetermine_f188, Pi.zero_apply _, Function.injective_id, fun t s _ => ?_⟩
  ext i
  change FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _)
      (LocalRule.finRule f230 hq230 s) i =
    FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _) s i
  rw [FiniteConfiguration.blockCode_apply, FiniteConfiguration.blockCode_apply]
  rfl

end ECA
