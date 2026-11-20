module

public import ECA.ForcingTables
public import ECA.LightConeWidth
public import Nonautonomous.MergeQuotient

/-!
# A wall of two set cells: six tables carry no sliding block code with an injective law

Let a quiescent table have `f 1 b c = 1` for every `b` and `c` (a set left cell gives `1`) and
`f 0 1 1 = 1`. A block of two set cells is then a **wall**: its left cell reads `011` or `111` and
its right cell `110` or `111`, so both stay `1` for ever, whatever stands beside them. Nothing
crosses a wall: a cell left of the left wall sees only cells that do not depend on what stands to
the right of it, and the cells right of the right wall follow the wall alone. So the state with the
walls at the cells `-2, -1` and `L, L + 1` and a window `w` of `L` cells between them steps, after
`L` steps, to the same state as the one with the zero window there: the left wall's `1`s fill the
window from the left, one cell a step. The mirror image has `f a b 1 = 1` for every `a` and `b`
and `f 1 1 0 = 1`, the right wall filling the window from the right. Tables `248`, `250`, `252` and
`254` meet the first criterion and tables `234` and `238` the second.

Two states of a fiber that some number of steps make equal are merged, and a semiconjugate factor
map with an injective law takes one value on merged states of a fiber
(`Nonautonomous.Semiconj.merges_invariant`, [RuleSpace] §2 Proposition 2.6(ii), the universality
of the merge quotient). A sliding block code reading the window of the walled state therefore takes
the same value on every window, its value on the zero window, which is zero. So a sliding block
code, read on the light cone restricted to the growing part, has an injective law only at the zero
code: the table's merge quotient is too coarse to carry a nonzero code with an injective law.

## Main results

* `FiniteConfiguration.walled` — the state with set cells at `-2`, `-1`, `L` and `L + 1`, a window
  `w` on the cells `0` to `L - 1`, and zeros elsewhere.
* `LocalRule.iterate_walled_eq_of_leftForcing` and `LocalRule.iterate_walled_eq_of_rightForcing` —
  at a quiescent table with the left (right) forcing criterion and the pair persisting, `L` steps
  take the walled state with any window and the walled state with the zero window to one state.
* `LocalRule.blockCode_eq_zero_of_walled_merges` — a sliding block code whose local rule sends the
  zero window to zero, read through a semiconjugacy with an injective law on positively invariant
  fibers holding every walled state, is the zero code at any table where every walled state merges
  with the walled state of the zero window.
* `LocalRule.blockCode_eq_zero_of_walled_merges_nonvacuous` — the hypotheses of that statement
  hold together, at table `254` with window `1` and the zero local rule.
* `blockCode_eq_zero_of_injective_law_f234`, `blockCode_eq_zero_of_injective_law_f238`,
  `blockCode_eq_zero_of_injective_law_f248`, `blockCode_eq_zero_of_injective_law_f250`,
  `blockCode_eq_zero_of_injective_law_f252` and `blockCode_eq_zero_of_injective_law_f254` — at each
  of the six tables, a sliding block code of any window with an injective law, a semiconjugacy
  on the light cone of any window restricted to the growing part, is the zero code.
* `blockCode_walled_injective_load_bearing` — the injectivity of the law is needed: at table `254`
  the code of window one reading the cell itself is a nonzero code whose law, the table's update,
  is not injective.
-/

@[expose] public section

namespace ECA

namespace FiniteConfiguration

/-- **The walled state**: a set cell at each of `-2`, `-1`, `L` and `L + 1` (two walls of two cells
each), the window `w` on the cells `0` to `L - 1` between them, and zeros elsewhere. -/
noncomputable def walled (L : ℕ) (w : Fin L → ZMod 2) : FiniteConfiguration :=
  Finsupp.onFinset (Finset.Icc (-2 : ℤ) ((L : ℤ) + 1))
    (fun i => if i = -2 ∨ i = -1 ∨ i = (L : ℤ) ∨ i = (L : ℤ) + 1 then 1
      else if h : 0 ≤ i ∧ i < (L : ℤ) then w ⟨i.toNat, by omega⟩ else 0) (by
      intro i hi
      by_contra hcon
      rw [Finset.mem_Icc] at hcon
      apply hi
      have h1 : ¬ (i = -2 ∨ i = -1 ∨ i = (L : ℤ) ∨ i = (L : ℤ) + 1) := by omega
      have h2 : ¬ (0 ≤ i ∧ i < (L : ℤ)) := by omega
      simp [h1, h2])

/-- A cell of a wall of the walled state is set. -/
private theorem walled_apply_of_wall (L : ℕ) (w : Fin L → ZMod 2) (i : ℤ)
    (h : i = -2 ∨ i = -1 ∨ i = (L : ℤ) ∨ i = (L : ℤ) + 1) : walled L w i = 1 := by
  simp [walled, Finsupp.onFinset_apply, h]

/-- The window of the walled state is the window it was built from. -/
private theorem walled_apply_window (L : ℕ) (w : Fin L → ZMod 2) (k : Fin L) :
    walled L w (0 + (k : ℕ)) = w k := by
  have hk := k.2
  have h1 : ¬ ((0 : ℤ) + (k : ℕ) = -2 ∨ (0 : ℤ) + (k : ℕ) = -1 ∨ (0 : ℤ) + (k : ℕ) = (L : ℤ) ∨
      (0 : ℤ) + (k : ℕ) = (L : ℤ) + 1) := by omega
  have h2 : 0 ≤ (0 : ℤ) + (k : ℕ) ∧ (0 : ℤ) + (k : ℕ) < (L : ℤ) := by omega
  simp only [walled, Finsupp.onFinset_apply]
  split_ifs
  congr 1
  ext
  simp

/-- Outside the window the walled state does not depend on the window. -/
private theorem walled_apply_of_not_window (L : ℕ) (w w' : Fin L → ZMod 2) (i : ℤ)
    (h : ¬ (0 ≤ i ∧ i < (L : ℤ))) : walled L w i = walled L w' i := by
  simp only [walled, Finsupp.onFinset_apply]
  simp [h]

end FiniteConfiguration

namespace LocalRule

/-- At a left-forcing table, cells `-2` to `k - 1` are `1` after `k` steps from a state with `1` at
`-2` and `-1`: the `1`s fill from the left one cell a step. -/
private theorem iterate_finRule_apply_left_ones {f : LocalRule} {hq : f 0 0 0 = 0}
    (hforce : ∀ b c, f 1 b c = 1) (h011 : f 0 1 1 = 1) (x : FiniteConfiguration)
    (hx2 : x (-2) = 1) (hx1 : x (-1) = 1) (k : ℕ) :
    ∀ i : ℤ, -2 ≤ i → i < (k : ℤ) → ((finRule f hq)^[k] x) i = 1 := by
  induction k with
  | zero =>
    intro i hi1 hi2
    rcases (by omega : i = -2 ∨ i = -1) with rfl | rfl
    · simpa using hx2
    · simpa using hx1
  | succ k ih =>
    intro i hi1 hi2
    rw [Function.iterate_succ_apply', finRule_apply]
    by_cases hi : i = -2
    · subst hi
      have a := ih (-2) le_rfl (by omega)
      have b := ih (-2 + 1) (by omega) (by omega)
      rw [a, b]
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1)
        ((finRule f hq)^[k] x (-2 - 1)) with h | h <;> rw [h]
      · exact h011
      · exact hforce 1 1
    · have a := ih (i - 1) (by omega) (by omega)
      rw [a]
      exact hforce _ _

/-- At a right-forcing table, cells `L - k` to `L + 1` are `1` after `k` steps from a state with `1`
at `L` and `L + 1`: the `1`s fill from the right one cell a step. -/
private theorem iterate_finRule_apply_right_ones {f : LocalRule} {hq : f 0 0 0 = 0}
    (hforce : ∀ a b, f a b 1 = 1) (h110 : f 1 1 0 = 1) (L : ℕ) (x : FiniteConfiguration)
    (hxL : x (L : ℤ) = 1) (hxL1 : x ((L : ℤ) + 1) = 1) (k : ℕ) :
    ∀ i : ℤ, (L : ℤ) - k ≤ i → i ≤ (L : ℤ) + 1 → ((finRule f hq)^[k] x) i = 1 := by
  induction k with
  | zero =>
    intro i hi1 hi2
    rcases (by omega : i = (L : ℤ) ∨ i = (L : ℤ) + 1) with rfl | rfl
    · simpa using hxL
    · simpa using hxL1
  | succ k ih =>
    intro i hi1 hi2
    rw [Function.iterate_succ_apply', finRule_apply]
    by_cases hi : i = (L : ℤ) + 1
    · subst hi
      have a := ih (L : ℤ) (by omega) (by omega)
      have b := ih ((L : ℤ) + 1) (by omega) le_rfl
      rw [show (L : ℤ) + 1 - 1 = L by ring, a, b]
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1)
        ((finRule f hq)^[k] x ((L : ℤ) + 1 + 1)) with h | h <;> rw [h]
      · exact h110
      · exact hforce 1 1
    · have a := ih (i + 1) (by omega) (by omega)
      rw [a]
      exact hforce _ _

/-- **At a left-forcing table, `L` steps erase the window of the walled state**: a block of two set
cells is a wall (its cells read `011` or `111`, and `110` or `111`, and stay `1`), nothing crosses
it, and the left wall's `1`s fill the window one cell a step. -/
theorem iterate_walled_eq_of_leftForcing (f : LocalRule) (hq : f 0 0 0 = 0)
    (hforce : ∀ b c, f 1 b c = 1) (h011 : f 0 1 1 = 1) {L : ℕ} (w : Fin L → ZMod 2) :
    (finRule f hq)^[L] (FiniteConfiguration.walled L w) =
      (finRule f hq)^[L] (FiniteConfiguration.walled L 0) := by
  have hl : ∀ w' : Fin L → ZMod 2, FiniteConfiguration.walled L w' (-2) = 1 ∧
      FiniteConfiguration.walled L w' (-1) = 1 ∧ FiniteConfiguration.walled L w' (L : ℤ) = 1 ∧
      FiniteConfiguration.walled L w' ((L : ℤ) + 1) = 1 := fun w' =>
    ⟨FiniteConfiguration.walled_apply_of_wall L w' _ (by omega),
      FiniteConfiguration.walled_apply_of_wall L w' _ (by omega),
      FiniteConfiguration.walled_apply_of_wall L w' _ (by omega),
      FiniteConfiguration.walled_apply_of_wall L w' _ (by omega)⟩
  have hwall : ∀ (w' : Fin L → ZMod 2) (k : ℕ),
      (finRule f hq)^[k] (FiniteConfiguration.walled L w') (L : ℤ) = 1 ∧
        (finRule f hq)^[k] (FiniteConfiguration.walled L w') ((L : ℤ) + 1) = 1 := fun w' k =>
    iterate_finRule_pair h011 (hforce 1 1) (hforce 1 0) (hl w').2.2.1 (hl w').2.2.2 k
  have hones : ∀ (w' : Fin L → ZMod 2) (k : ℕ) (i : ℤ), -2 ≤ i → i < (k : ℤ) →
      (finRule f hq)^[k] (FiniteConfiguration.walled L w') i = 1 := fun w' k =>
    iterate_finRule_apply_left_ones hforce h011 _ (hl w').1 (hl w').2.1 k
  have key : ∀ k : ℕ, k ≤ L → ∀ i : ℤ, ¬ ((k : ℤ) ≤ i ∧ i < (L : ℤ)) →
      (finRule f hq)^[k] (FiniteConfiguration.walled L w) i =
        (finRule f hq)^[k] (FiniteConfiguration.walled L 0) i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      simp only [Function.iterate_zero, id_eq]
      exact FiniteConfiguration.walled_apply_of_not_window L w 0 i (by simpa using hi)
    | succ k ih =>
      intro hk i hi
      by_cases hA : -2 ≤ i ∧ i < ((k + 1 : ℕ) : ℤ)
      · rw [hones w (k + 1) i hA.1 hA.2, hones 0 (k + 1) i hA.1 hA.2]
      by_cases hB : i = (L : ℤ) ∨ i = (L : ℤ) + 1
      · rcases hB with rfl | rfl
        · rw [(hwall w _).1, (hwall 0 _).1]
        · rw [(hwall w _).2, (hwall 0 _).2]
      · have ih' := ih (by omega)
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', finRule_apply,
          finRule_apply, ih' (i - 1) (by push_cast at hA hi ⊢; omega),
          ih' i (by push_cast at hA hi ⊢; omega), ih' (i + 1) (by push_cast at hA hi ⊢; omega)]
  ext i
  exact key L le_rfl i (by omega)

/-- **At a right-forcing table, `L` steps erase the window of the walled state**: the mirror of
`iterate_walled_eq_of_leftForcing`, the right wall's `1`s filling the window from the right. -/
theorem iterate_walled_eq_of_rightForcing (f : LocalRule) (hq : f 0 0 0 = 0)
    (hforce : ∀ a b, f a b 1 = 1) (h110 : f 1 1 0 = 1) {L : ℕ} (w : Fin L → ZMod 2) :
    (finRule f hq)^[L] (FiniteConfiguration.walled L w) =
      (finRule f hq)^[L] (FiniteConfiguration.walled L 0) := by
  have hl : ∀ w' : Fin L → ZMod 2, FiniteConfiguration.walled L w' (-2) = 1 ∧
      FiniteConfiguration.walled L w' (-1) = 1 ∧ FiniteConfiguration.walled L w' (L : ℤ) = 1 ∧
      FiniteConfiguration.walled L w' ((L : ℤ) + 1) = 1 := fun w' =>
    ⟨FiniteConfiguration.walled_apply_of_wall L w' _ (by omega),
      FiniteConfiguration.walled_apply_of_wall L w' _ (by omega),
      FiniteConfiguration.walled_apply_of_wall L w' _ (by omega),
      FiniteConfiguration.walled_apply_of_wall L w' _ (by omega)⟩
  have hwall : ∀ (w' : Fin L → ZMod 2) (k : ℕ),
      (finRule f hq)^[k] (FiniteConfiguration.walled L w') (-2) = 1 ∧
        (finRule f hq)^[k] (FiniteConfiguration.walled L w') (-2 + 1) = 1 := fun w' k =>
    iterate_finRule_pair (hforce 0 1) (hforce 1 1) h110 (hl w').1
      (by rw [show (-2 : ℤ) + 1 = -1 by norm_num]; exact (hl w').2.1) k
  have hones : ∀ (w' : Fin L → ZMod 2) (k : ℕ) (i : ℤ), (L : ℤ) - k ≤ i → i ≤ (L : ℤ) + 1 →
      (finRule f hq)^[k] (FiniteConfiguration.walled L w') i = 1 := fun w' k =>
    iterate_finRule_apply_right_ones hforce h110 L _ (hl w').2.2.1 (hl w').2.2.2 k
  have key : ∀ k : ℕ, k ≤ L → ∀ i : ℤ, ¬ (0 ≤ i ∧ i < (L : ℤ) - k) →
      (finRule f hq)^[k] (FiniteConfiguration.walled L w) i =
        (finRule f hq)^[k] (FiniteConfiguration.walled L 0) i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      simp only [Function.iterate_zero, id_eq]
      exact FiniteConfiguration.walled_apply_of_not_window L w 0 i (by simpa using hi)
    | succ k ih =>
      intro hk i hi
      by_cases hA : (L : ℤ) - ((k + 1 : ℕ) : ℤ) ≤ i ∧ i ≤ (L : ℤ) + 1
      · rw [hones w (k + 1) i hA.1 hA.2, hones 0 (k + 1) i hA.1 hA.2]
      by_cases hB : i = -2 ∨ i = -1
      · rcases hB with rfl | rfl
        · rw [(hwall w _).1, (hwall 0 _).1]
        · have e : (-1 : ℤ) = -2 + 1 := by norm_num
          rw [e, (hwall w _).2, (hwall 0 _).2]
      · have ih' := ih (by omega)
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', finRule_apply,
          finRule_apply, ih' (i - 1) (by push_cast at hA hi ⊢; omega),
          ih' i (by push_cast at hA hi ⊢; omega), ih' (i + 1) (by push_cast at hA hi ⊢; omega)]
  ext i
  exact key L le_rfl i (by omega)

/-- **A sliding block code with an injective law is zero at a table where the walled states
merge**: if the state with any window between two walls merges with the one with the zero window,
a sliding block code of that window whose local rule sends the zero window to zero and which
semiconjugates the table's update, on positively invariant fibers holding every walled state, to
an injective law, is zero. The code takes one value on merged states of a fiber
([RuleSpace] §2 Proposition 2.6(ii), the universality of the merge quotient), and reads the window
of the walled state at the cell `0`. -/
theorem blockCode_eq_zero_of_walled_merges (f : LocalRule) (hq : f 0 0 0 = 0) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hmerge : ∀ w, Nonautonomous.Merges (finRule f hq) (FiniteConfiguration.walled L w)
      (FiniteConfiguration.walled L 0))
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    {Ω : ℕ → Set FiniteConfiguration} (hadv : Nonautonomous.PositivelyInvariant (finRule f hq) Ω)
    (hsq : Nonautonomous.Semiconj (finRule f hq) F
      (fun _ => FiniteConfiguration.blockCode L g hg) Ω)
    (t : ℕ) (hmem : ∀ w, FiniteConfiguration.walled L w ∈ Ω t) :
    g = 0 := by
  funext w
  have h := Nonautonomous.Semiconj.merges_invariant hF hadv hsq t
    (FiniteConfiguration.walled L w) (hmem w) (FiniteConfiguration.walled L 0) (hmem 0) (hmerge w)
  have h0 := congrArg (fun y : FiniteConfiguration => y 0) h
  simp only [FiniteConfiguration.blockCode_apply] at h0
  have e1 : (fun k : Fin L => FiniteConfiguration.walled L w (0 + (k : ℕ))) = w :=
    funext (FiniteConfiguration.walled_apply_window L w)
  have e2 : (fun k : Fin L => FiniteConfiguration.walled L 0 (0 + (k : ℕ))) = 0 :=
    funext (FiniteConfiguration.walled_apply_window L 0)
  rw [e1, e2] at h0
  rw [h0, hg]
  rfl

/-- Every walled state lies in the light cone at `L + 2`. -/
private theorem walled_mem_lightCone (n L : ℕ) (w : Fin L → ZMod 2) :
    FiniteConfiguration.walled L w ∈ lightCone n (L + 2) := by
  intro i hi
  have hb := Finsupp.support_onFinset_subset hi
  rw [Finset.mem_Icc] at hb
  push_cast
  omega

/-- A walled state is in the growing part when the table moves the right end out and keeps a pair
of set cells. -/
private theorem walled_mem_of_rightTap {f : LocalRule} {hq : f 0 0 0 = 0} (h0 : f 1 0 0 = 1)
    (h1 : f 0 1 1 = 1) (h2 : f 1 1 1 = 1) (h3 : f 1 1 0 = 1) (n L : ℕ) (w : Fin L → ZMod 2) :
    FiniteConfiguration.walled L w ∈ lightCone n (L + 2) ∩
      Nonautonomous.GrowingPart (finRule f hq) FiniteConfiguration.diam :=
  ⟨walled_mem_lightCone n L w,
    mem_growingPart_of_rightTap_pair h0 h1 h2 h3 (i := -2)
      (FiniteConfiguration.walled_apply_of_wall L w _ (by omega))
      (FiniteConfiguration.walled_apply_of_wall L w _ (by omega))⟩

/-- A walled state is in the growing part when the table moves the left end out and keeps a pair
of set cells. -/
private theorem walled_mem_of_leftTap {f : LocalRule} {hq : f 0 0 0 = 0} (h0 : f 0 0 1 = 1)
    (h1 : f 0 1 1 = 1) (h2 : f 1 1 1 = 1) (h3 : f 1 1 0 = 1) (n L : ℕ) (w : Fin L → ZMod 2) :
    FiniteConfiguration.walled L w ∈ lightCone n (L + 2) ∩
      Nonautonomous.GrowingPart (finRule f hq) FiniteConfiguration.diam :=
  ⟨walled_mem_lightCone n L w,
    mem_growingPart_of_leftTap_pair h0 h1 h2 h3 (i := -2)
      (FiniteConfiguration.walled_apply_of_wall L w _ (by omega))
      (FiniteConfiguration.walled_apply_of_wall L w _ (by omega))⟩

/-- **The statement's hypotheses are jointly satisfiable**, at table `254` with window `1`, the zero
local rule, the identity as the law, and the light cone of the one-cell window restricted to the
growing part at time `3`: the table is quiescent, the local rule sends the zero window to zero,
every walled state merges with the walled state of the zero window, the law is injective, the
fibers are positively invariant, the code is a semiconjugacy, and every walled state lies in the
fiber. The conclusion forces the code to be zero, so this shows only that the hypotheses are
consistent. -/
theorem blockCode_eq_zero_of_walled_merges_nonvacuous :
    f254 0 0 0 = 0 ∧ (0 : (Fin 1 → ZMod 2) → ZMod 2) 0 = 0 ∧
      (∀ w : Fin 1 → ZMod 2, Nonautonomous.Merges (finRule f254 hq254)
        (FiniteConfiguration.walled 1 w) (FiniteConfiguration.walled 1 0)) ∧
      Function.Injective (id : FiniteConfiguration → FiniteConfiguration) ∧
      Nonautonomous.PositivelyInvariant (finRule f254 hq254)
        (fun t => lightCone 1 t ∩
          Nonautonomous.GrowingPart (finRule f254 hq254) FiniteConfiguration.diam) ∧
      Nonautonomous.Semiconj (finRule f254 hq254) id
        (fun _ => FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2)
          (Pi.zero_apply _))
        (fun t => lightCone 1 t ∩
          Nonautonomous.GrowingPart (finRule f254 hq254) FiniteConfiguration.diam) ∧
      ∀ w : Fin 1 → ZMod 2, FiniteConfiguration.walled 1 w ∈
        (fun t => lightCone 1 t ∩
          Nonautonomous.GrowingPart (finRule f254 hq254) FiniteConfiguration.diam) 3 := by
  refine ⟨hq254, Pi.zero_apply _,
    fun w => ⟨1, iterate_walled_eq_of_leftForcing f254 hq254 (by decide) (by decide) w⟩,
    Function.injective_id,
    Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f254 hq254 1),
    fun t s _ => ?_, fun w => walled_mem_of_rightTap (by decide) (by decide) (by decide)
      (by decide) 1 1 w⟩
  ext i
  change FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _)
      (finRule f254 hq254 s) i =
    FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _) s i
  rw [FiniteConfiguration.blockCode_apply, FiniteConfiguration.blockCode_apply]
  rfl

end LocalRule

/-- **Table `248` carries no sliding block code with an injective law but zero**: a sliding block
code of any window, a semiconjugacy from the table's update on the light cone of any window
restricted to the growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f248 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f248 hq248) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f248 hq248) FiniteConfiguration.diam)) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_walled_merges f248 hq248 g hg
    (fun w => ⟨L, LocalRule.iterate_walled_eq_of_leftForcing f248 hq248 (by decide) (by decide) w⟩)
    hF (Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f248 hq248 n)) hsq (L + 2)
    (fun w => LocalRule.walled_mem_of_rightTap (by decide) (by decide) (by decide) (by decide)
      n L w)

/-- **Table `250` carries no sliding block code with an injective law but zero**: a sliding block
code of any window, a semiconjugacy from the table's update on the light cone of any window
restricted to the growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f250 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f250 hq250) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f250 hq250) FiniteConfiguration.diam)) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_walled_merges f250 hq250 g hg
    (fun w => ⟨L, LocalRule.iterate_walled_eq_of_leftForcing f250 hq250 (by decide) (by decide) w⟩)
    hF (Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f250 hq250 n)) hsq (L + 2)
    (fun w => LocalRule.walled_mem_of_rightTap (by decide) (by decide) (by decide) (by decide)
      n L w)

/-- **Table `252` carries no sliding block code with an injective law but zero**: a sliding block
code of any window, a semiconjugacy from the table's update on the light cone of any window
restricted to the growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f252 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f252 hq252) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f252 hq252) FiniteConfiguration.diam)) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_walled_merges f252 hq252 g hg
    (fun w => ⟨L, LocalRule.iterate_walled_eq_of_leftForcing f252 hq252 (by decide) (by decide) w⟩)
    hF (Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f252 hq252 n)) hsq (L + 2)
    (fun w => LocalRule.walled_mem_of_rightTap (by decide) (by decide) (by decide) (by decide)
      n L w)

/-- **Table `254` carries no sliding block code with an injective law but zero**: a sliding block
code of any window, a semiconjugacy from the table's update on the light cone of any window
restricted to the growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f254 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f254 hq254) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f254 hq254) FiniteConfiguration.diam)) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_walled_merges f254 hq254 g hg
    (fun w => ⟨L, LocalRule.iterate_walled_eq_of_leftForcing f254 hq254 (by decide) (by decide) w⟩)
    hF (Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f254 hq254 n)) hsq (L + 2)
    (fun w => LocalRule.walled_mem_of_rightTap (by decide) (by decide) (by decide) (by decide)
      n L w)

/-- **Table `234` carries no sliding block code with an injective law but zero**, the mirror: a
sliding block code of any window, a semiconjugacy from the table's update on the light cone of any
window restricted to the growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f234 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f234 hq234) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f234 hq234) FiniteConfiguration.diam)) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_walled_merges f234 hq234 g hg
    (fun w => ⟨L, LocalRule.iterate_walled_eq_of_rightForcing f234 hq234 (by decide) (by decide)
      w⟩)
    hF (Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f234 hq234 n)) hsq (L + 2)
    (fun w => LocalRule.walled_mem_of_leftTap (by decide) (by decide) (by decide) (by decide)
      n L w)

/-- **Table `238` carries no sliding block code with an injective law but zero**, the mirror: a
sliding block code of any window, a semiconjugacy from the table's update on the light cone of any
window restricted to the growing part to an injective law, is the zero code. -/
theorem blockCode_eq_zero_of_injective_law_f238 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f238 hq238) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f238 hq238) FiniteConfiguration.diam)) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_walled_merges f238 hq238 g hg
    (fun w => ⟨L, LocalRule.iterate_walled_eq_of_rightForcing f238 hq238 (by decide) (by decide)
      w⟩)
    hF (Nonautonomous.positivelyInvariant_growingPart (size := FiniteConfiguration.diam)
      (positivelyInvariant_lightCone_finRule f238 hq238 n)) hsq (L + 2)
    (fun w => LocalRule.walled_mem_of_leftTap (by decide) (by decide) (by decide) (by decide)
      n L w)

/-- **The injectivity of the law is load-bearing**: at table `254` the code of window one, which
reads the cell itself, is a nonzero code the table's update carries to itself, and that update is
not injective. -/
theorem blockCode_walled_injective_load_bearing :
    ¬ Function.Injective (LocalRule.finRule f254 hq254) ∧
      (∀ s : FiniteConfiguration,
        FiniteConfiguration.blockCode 1 (fun w : Fin 1 → ZMod 2 => w 0) rfl
            (LocalRule.finRule f254 hq254 s) =
          LocalRule.finRule f254 hq254
            (FiniteConfiguration.blockCode 1 (fun w : Fin 1 → ZMod 2 => w 0) rfl s)) ∧
      (fun w : Fin 1 → ZMod 2 => w 0) ≠ 0 := by
  refine ⟨not_injective_finRule_f254, fun s => ?_, fun h => ?_⟩
  · have e : FiniteConfiguration.blockCode 1 (fun w : Fin 1 → ZMod 2 => w 0) rfl = id := by
      funext s
      ext i
      rw [FiniteConfiguration.blockCode_apply]
      simp
    rw [e]
    rfl
  · have h1 := congrFun h (fun _ => 1)
    revert h1
    decide

end ECA
