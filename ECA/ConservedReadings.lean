module

public import ECA.BlockCode
public import ECA.LightConeWidth
public import Nonautonomous.MergeQuotient
public import Mathlib.Data.Int.Interval

/-!
# Table `206`: an injective law fixes every reading of a conserved code
([RuleSpace] §2 Proposition 2.6 for the reduction and the merge invariance)

Table `206` carries a sliding block code that is not zero: the pattern `10` is conserved
(`blockCode_finRule_f206`), and its growing part under the support diameter is the nonzero states
(`growingPart_f206_eq_ne_zero`). The rule keeps every set cell and sets a clear cell whose left
neighbour is clear and right neighbour set: the left end of the support moves out one cell a step,
every `10` stays in place, and a run of clear cells between two set cells fills from its right
until one clear cell is left.

So the zero-code argument of the tables whose ends determine does not apply, and what an injective
law fixes is every reading of such a code, not the code. Two states of one stage that agree but
for a run of clear cells, one with the run filled from its right in the other, merge, and they read
at one cell the zero window and a window `0^a 1^b` with no `10`, so the code's local rule vanishes
on every such window (`[RuleSpace] §2 Proposition 2.6`, the merge invariance). A nonzero state
reaches, after enough steps, a state whose every internal run of clear cells is one cell and whose
left end stands more than the window length to the left of the leftmost `10`; a step then changes
one cell, the new left end, and every window holding it reads `0^a 1^b` before and after, so the
code is unchanged by a step at the state itself (the reduction,
`Nonautonomous.Semiconj.eq_of_iterate_eq`).

The statement is at table `206`; a law of finite order at the other tables carrying a code is not
stated.

## Main results

* `blockCode_finRule_eq_of_injective_law_f206` — at table `206`, a sliding block code of any
  window with an injective law, a semiconjugacy on the light cone of any window restricted to the
  growing part, is unchanged by a step at every state of the fiber.
* `law_apply_blockCode_eq_of_injective_law_f206` — the law is the identity on the image of the
  code at every state of the fiber.
* `blockCode_finRule_eq_of_injective_law_f206_nonvacuous` — the hypotheses hold together, with the
  code of the pattern `10` and the identity as the law.
-/

@[expose] public section

namespace ECA

/-! ## Two states that agree but for a run of clear cells -/

/-- The state `1 0^(a+1) 1^(L-a+1)` after `k` steps of table `206`: the cells `-2 - k` to `-2` and
the cells `max (a - k) 0` to `L` are set, the others clear. -/
private noncomputable def runState (L a k : ℕ) : FiniteConfiguration :=
  Finsupp.onFinset (Finset.Icc (-2 - (k : ℤ)) (L : ℤ))
    (fun i => if (-2 - (k : ℤ) ≤ i ∧ i ≤ -2) ∨ (max ((a : ℤ) - k) 0 ≤ i ∧ i ≤ L) then 1 else 0) (by
      intro i hi
      rw [Finset.mem_Icc]
      by_contra hcon
      apply hi
      rw [ite_eq_right_iff]
      intro hc
      exfalso
      omega)

private theorem runState_apply (L a k : ℕ) (i : ℤ) :
    runState L a k i =
      if (-2 - (k : ℤ) ≤ i ∧ i ≤ -2) ∨ (max ((a : ℤ) - k) 0 ≤ i ∧ i ≤ L) then 1 else 0 := by
  simp [runState, Finsupp.onFinset_apply]

/-- A step of table `206` is a cell set when it is set or when its left neighbour is clear and its
right neighbour is set. -/
private theorem f206_eq_ite (l c r : ZMod 2) :
    f206 l c r = if c = 1 ∨ (l = 0 ∧ r = 1) then 1 else 0 := by
  revert l c r
  decide

private theorem finRule_f206_apply (s : FiniteConfiguration) (i : ℤ) :
    LocalRule.finRule f206 hq206 s i =
      if s i = 1 ∨ (s (i - 1) = 0 ∧ s (i + 1) = 1) then 1 else 0 := by
  rw [LocalRule.finRule_apply, f206_eq_ite]

private theorem ite_eq_one_iff (P : Prop) [Decidable P] :
    ((if P then 1 else 0 : ZMod 2) = 1) ↔ P := by
  by_cases h : P <;> simp [h]

private theorem ite_eq_zero_iff (P : Prop) [Decidable P] :
    ((if P then 1 else 0 : ZMod 2) = 0) ↔ ¬P := by
  by_cases h : P <;> simp [h]

private theorem finRule_runState (L a k : ℕ) (ha : a ≤ L) :
    LocalRule.finRule f206 hq206 (runState L a k) = runState L a (k + 1) := by
  ext i
  rw [finRule_f206_apply]
  simp only [runState_apply, ite_eq_one_iff, ite_eq_zero_iff]
  push_cast
  refine if_congr ?_ rfl rfl
  omega

private theorem iterate_finRule_runState (L a : ℕ) (ha : a ≤ L) (k : ℕ) :
    (LocalRule.finRule f206 hq206)^[k] (runState L a 0) = runState L a k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, finRule_runState L a k ha]

private theorem runState_eq_of_le (L a k : ℕ) (ha : a ≤ L) (hk : L ≤ k) :
    runState L a k = runState L L k := by
  ext i
  rw [runState_apply, runState_apply]
  refine if_congr ?_ rfl rfl
  omega

/-- The state `1 0^(a+1) 1^(L-a+1)` and the state `1 0^(L+1) 1` merge: after `L` steps both are
`1^(L+1) 0 1^(L+1)`. -/
private theorem merges_runState (L a : ℕ) (ha : a ≤ L) :
    Nonautonomous.Merges (LocalRule.finRule f206 hq206) (runState L a 0) (runState L L 0) :=
  ⟨L, by
    rw [iterate_finRule_runState L a ha, iterate_finRule_runState L L le_rfl,
      runState_eq_of_le L a L ha le_rfl]⟩

private theorem runState_mem_lightCone (n L a k : ℕ) :
    runState L a k ∈ lightCone n (L + 2 + k) := by
  intro i hi
  have hb := Finsupp.support_onFinset_subset hi
  rw [Finset.mem_Icc] at hb
  push_cast
  omega

private theorem runState_ne_zero (L a : ℕ) : runState L a 0 ≠ 0 := by
  intro h
  have h1 := congrArg (fun y : FiniteConfiguration => y (-2)) h
  simp only [runState_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
  rw [ite_eq_right_iff] at h1
  exact absurd (h1 (Or.inl ⟨by norm_num, le_rfl⟩)) (by decide)

private theorem runState_window (L a : ℕ) (m : Fin L) :
    runState L a 0 (0 + (m : ℕ)) = if a ≤ (m : ℕ) then 1 else 0 := by
  rw [runState_apply]
  refine if_congr ?_ rfl rfl
  have hm := m.isLt
  push_cast
  omega

/-- **The code's local rule is zero on every window with no `10`**: at table `206`, a sliding block
code with an injective law, semiconjugate on the growing part of the light cone, reads zero at a
window of clear cells followed by set cells. -/
private theorem window_eq_zero_of_injective_law_f206 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f206 hq206) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam))
    (a : ℕ) (ha : a ≤ L) :
    g (fun m : Fin L => if a ≤ (m : ℕ) then 1 else 0) = 0 := by
  have hadv := Nonautonomous.positivelyInvariant_growingPart
    (size := FiniteConfiguration.diam) (positivelyInvariant_lightCone_finRule f206 hq206 n)
  have hmem : ∀ b : ℕ, runState L b 0 ∈ lightCone n (L + 2) ∩
      Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam :=
    fun b => ⟨runState_mem_lightCone n L b 0, by
      rw [growingPart_f206_eq_ne_zero]
      exact runState_ne_zero L b⟩
  have h := Nonautonomous.Semiconj.merges_invariant hF hadv hsq (L + 2) (runState L a 0) (hmem a)
    (runState L L 0) (hmem L) (merges_runState L a ha)
  have h0 := congrArg (fun y : FiniteConfiguration => y 0) h
  simp only [FiniteConfiguration.blockCode_apply] at h0
  have e1 : (fun m : Fin L => runState L a 0 (0 + (m : ℕ))) =
      fun m : Fin L => if a ≤ (m : ℕ) then 1 else 0 := funext (runState_window L a)
  have e2 : (fun m : Fin L => runState L L 0 (0 + (m : ℕ))) = 0 := by
    funext m
    rw [runState_window L L m]
    have hlt : ¬ L ≤ (m : ℕ) := by have := m.isLt; omega
    simp [hlt]
  rw [e1, e2] at h0
  rw [h0, hg]

/-! ## A step at a settled state changes one cell -/

private theorem zmod2_zero_or_one (v : ZMod 2) : v = 0 ∨ v = 1 := by
  revert v
  decide

/-- A set cell of a state stays set after a step. -/
private theorem finRule_f206_of_eq_one {s : FiniteConfiguration} {i : ℤ} (h : s i = 1) :
    LocalRule.finRule f206 hq206 s i = 1 := by
  simp [finRule_f206_apply, h]

/-- A clear cell stays clear when its right neighbour is clear. -/
private theorem finRule_f206_of_right {s : FiniteConfiguration} {i : ℤ} (h : s i = 0)
    (hr : s (i + 1) = 0) : LocalRule.finRule f206 hq206 s i = 0 := by
  simp [finRule_f206_apply, h, hr]

section Settled

variable {s : FiniteConfiguration} {e r : ℤ}

/-- **The shape of an iterate**: a state whose cells left of `e` and right of `r` are clear and
whose cell `e` is set, at `k` steps, has clear cells left of `e - k` and right of `r`, and every
cell from `e - k` to `e` set. -/
private theorem iterate_shape (hs1 : s e = 1) (hs2 : ∀ i, i < e → s i = 0)
    (hs3 : ∀ i, r < i → s i = 0) (k : ℕ) :
    (∀ i, i < e - k → (LocalRule.finRule f206 hq206)^[k] s i = 0) ∧
      (∀ i, e - k ≤ i → i ≤ e → (LocalRule.finRule f206 hq206)^[k] s i = 1) ∧
      (∀ i, r < i → (LocalRule.finRule f206 hq206)^[k] s i = 0) := by
  induction k with
  | zero =>
    refine ⟨fun i hi => hs2 i (by simpa using hi), fun i h1 h2 => ?_, hs3⟩
    have : i = e := le_antisymm h2 (by simpa using h1)
    subst this
    exact hs1
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨fun i hi => ?_, fun i hi hi' => ?_, fun i hi => ?_⟩
    · push_cast at hi
      exact finRule_f206_of_right (h1 i (by omega)) (h1 (i + 1) (by omega))
    · push_cast at hi
      by_cases hc : e - k ≤ i
      · exact finRule_f206_of_eq_one (h2 i hc hi')
      · rw [finRule_f206_apply, h1 i (by omega), h1 (i - 1) (by omega),
          h2 (i + 1) (by omega) (by omega)]
        decide
    · exact finRule_f206_of_right (h3 i hi) (h3 (i + 1) (by omega))

/-- **A state is settled at `e`** when no clear cell from `e` on has a clear left neighbour and a
set right neighbour: every internal run of clear cells is one cell, and no cell right of the left
end is about to be set. -/
private def NoBad (e : ℤ) (u : FiniteConfiguration) : Prop :=
  ∀ j, e ≤ j → ¬(u (j - 1) = 0 ∧ u j = 0 ∧ u (j + 1) = 1)

/-- **A step at a settled iterate changes one cell**: with `NoBad` at the `k`-th iterate, the step
leaves every cell but the new left end, `e - k - 1`, unchanged. -/
private theorem finRule_apply_of_noBad (hs1 : s e = 1) (hs2 : ∀ i, i < e → s i = 0)
    (hs3 : ∀ i, r < i → s i = 0) {k : ℕ} (hnb : NoBad e ((LocalRule.finRule f206 hq206)^[k] s))
    {j : ℤ} (hj : j ≠ e - k - 1) :
    LocalRule.finRule f206 hq206 ((LocalRule.finRule f206 hq206)^[k] s) j =
      (LocalRule.finRule f206 hq206)^[k] s j := by
  obtain ⟨a1, a2, _⟩ := iterate_shape (r := r) hs1 hs2 hs3 k
  obtain ⟨b1, b2, _⟩ := iterate_shape (r := r) hs1 hs2 hs3 (k + 1)
  have hU : LocalRule.finRule f206 hq206 ((LocalRule.finRule f206 hq206)^[k] s) =
      (LocalRule.finRule f206 hq206)^[k + 1] s := (Function.iterate_succ_apply' _ k s).symm
  rw [hU]
  push_cast at b1 b2
  by_cases hlt : j < e - k - 1
  · rw [b1 j (by omega), a1 j (by omega)]
  by_cases hle : j ≤ e
  · rw [b2 j (by omega) hle, a2 j (by omega) hle]
  rw [← hU]
  rcases zmod2_zero_or_one ((LocalRule.finRule f206 hq206)^[k] s j) with h | h
  · rw [finRule_f206_apply, h, ite_eq_right_iff]
    rintro (h' | ⟨h1, h2⟩)
    · exact absurd h' (by decide)
    · exact (hnb j (by omega) ⟨h1, h, h2⟩).elim
  · rw [h]
    exact finRule_f206_of_eq_one h

/-- The number of clear cells of a state from `e` to `r`. -/
private noncomputable def clearCount (e r : ℤ) (u : FiniteConfiguration) : ℕ :=
  ((Finset.Icc e r).filter fun j => u j = 0).card

/-- **An unsettled state loses a clear cell**: a clear cell from `e` on with a clear left neighbour
and a set right neighbour is set by the step, and no set cell is cleared, so the count of clear
cells from `e` to `r` falls when the state is clear right of `r`. -/
private theorem clearCount_finRule_lt {u : FiniteConfiguration} (hu : ∀ i, r < i → u i = 0)
    (hb : ¬ NoBad e u) :
    clearCount e r (LocalRule.finRule f206 hq206 u) < clearCount e r u := by
  unfold NoBad at hb
  push Not at hb
  obtain ⟨j, hej, h1, h2, h3⟩ := hb
  have hjr : j ≤ r := by
    by_contra hcon
    have := hu (j + 1) (by omega)
    rw [this] at h3
    exact absurd h3 (by decide)
  have hset : LocalRule.finRule f206 hq206 u j = 1 := by
    simp [finRule_f206_apply, h1, h3]
  unfold clearCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hej, hjr⟩, h2⟩, ?_⟩
    intro hj
    have := (Finset.mem_filter.mp hj).2
    rw [hset] at this
    exact absurd this (by decide)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hx1, ?_⟩
    rcases zmod2_zero_or_one (u x) with h | h
    · exact h
    · have := finRule_f206_of_eq_one h
      rw [this] at hx2
      exact absurd hx2 (by decide)

/-- **A nonzero state settles**: from every exponent `L` on there is one at which the iterate is
settled at the left end of the state, the count of clear cells between its ends falling at every
step that is not settled. -/
private theorem exists_noBad (hs1 : s e = 1) (hs2 : ∀ i, i < e → s i = 0)
    (hs3 : ∀ i, r < i → s i = 0) (L : ℕ) :
    ∃ k, L ≤ k ∧ NoBad e ((LocalRule.finRule f206 hq206)^[k] s) := by
  have key : ∀ n k : ℕ, L ≤ k →
      clearCount e r ((LocalRule.finRule f206 hq206)^[k] s) ≤ n →
      ∃ k', L ≤ k' ∧ NoBad e ((LocalRule.finRule f206 hq206)^[k'] s) := by
    intro n
    induction n with
    | zero =>
      intro k hk hN
      by_cases hb : NoBad e ((LocalRule.finRule f206 hq206)^[k] s)
      · exact ⟨k, hk, hb⟩
      · exfalso
        have hlt := clearCount_finRule_lt (e := e)
          (iterate_shape (r := r) hs1 hs2 hs3 k).2.2 hb
        omega
    | succ n ih =>
      intro k hk hN
      by_cases hb : NoBad e ((LocalRule.finRule f206 hq206)^[k] s)
      · exact ⟨k, hk, hb⟩
      · have hlt := clearCount_finRule_lt (e := e)
          (iterate_shape (r := r) hs1 hs2 hs3 k).2.2 hb
        rw [← Function.iterate_succ_apply' (LocalRule.finRule f206 hq206) k s] at hlt
        have hlt' : clearCount e r ((LocalRule.finRule f206 hq206)^[k + 1] s) <
            clearCount e r ((LocalRule.finRule f206 hq206)^[k] s) := hlt
        exact ih (k + 1) (by omega) (by omega)
  exact key _ L le_rfl le_rfl

/-- The windows `0^a 1^b`, read at any integer threshold, are the windows on which the code's local
rule vanishes. -/
private theorem window_threshold_eq_zero {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2)
    (hwin : ∀ a : ℕ, a ≤ L → g (fun m : Fin L => if a ≤ (m : ℕ) then 1 else 0) = 0) (τ : ℤ) :
    g (fun m : Fin L => if τ ≤ (m : ℤ) then 1 else 0) = 0 := by
  have h := hwin (min (max τ 0).toNat L) (min_le_right _ _)
  have e : (fun m : Fin L => if τ ≤ (m : ℤ) then (1 : ZMod 2) else 0) =
      fun m : Fin L => if min (max τ 0).toNat L ≤ (m : ℕ) then 1 else 0 := by
    funext m
    have hm := m.isLt
    refine if_congr ?_ rfl rfl
    omega
  rw [e]
  exact h

/-- **A step at a settled iterate leaves every reading unchanged**: at the `k`-th iterate of a
state, `L ≤ k`, settled at the left end, the step changes the new left end alone, every window
holding it reads `0^a 1^b` before and after, and the code's local rule is zero there. -/
private theorem blockCode_finRule_iterate_eq {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hwin : ∀ τ : ℤ, g (fun m : Fin L => if τ ≤ (m : ℤ) then 1 else 0) = 0)
    (hs1 : s e = 1) (hs2 : ∀ i, i < e → s i = 0) (hs3 : ∀ i, r < i → s i = 0) {k : ℕ}
    (hk : L ≤ k) (hnb : NoBad e ((LocalRule.finRule f206 hq206)^[k] s)) :
    FiniteConfiguration.blockCode L g hg
        (LocalRule.finRule f206 hq206 ((LocalRule.finRule f206 hq206)^[k] s)) =
      FiniteConfiguration.blockCode L g hg ((LocalRule.finRule f206 hq206)^[k] s) := by
  obtain ⟨a1, a2, _⟩ := iterate_shape (r := r) hs1 hs2 hs3 k
  obtain ⟨b1, b2, _⟩ := iterate_shape (r := r) hs1 hs2 hs3 (k + 1)
  have hU : LocalRule.finRule f206 hq206 ((LocalRule.finRule f206 hq206)^[k] s) =
      (LocalRule.finRule f206 hq206)^[k + 1] s := (Function.iterate_succ_apply' _ k s).symm
  push_cast at b1 b2
  ext i
  rw [FiniteConfiguration.blockCode_apply, FiniteConfiguration.blockCode_apply]
  by_cases hi : i ≤ e - k - 1 ∧ e - k - 1 < i + L
  · have w1 : (fun m : Fin L => (LocalRule.finRule f206 hq206)^[k] s (i + (m : ℕ))) =
        fun m : Fin L => if e - k - i ≤ (m : ℤ) then 1 else 0 := by
      funext m
      have hm := m.isLt
      by_cases h : e - k - i ≤ (m : ℤ)
      · simp only [h, ↓reduceIte]
        exact a2 _ (by omega) (by omega)
      · simp only [h, ↓reduceIte]
        exact a1 _ (by omega)
    have w2 : (fun m : Fin L => LocalRule.finRule f206 hq206
        ((LocalRule.finRule f206 hq206)^[k] s) (i + (m : ℕ))) =
        fun m : Fin L => if e - k - 1 - i ≤ (m : ℤ) then 1 else 0 := by
      funext m
      have hm := m.isLt
      rw [hU]
      by_cases h : e - k - 1 - i ≤ (m : ℤ)
      · simp only [h, ↓reduceIte]
        exact b2 _ (by omega) (by omega)
      · simp only [h, ↓reduceIte]
        exact b1 _ (by omega)
    rw [w1, w2, hwin, hwin]
  · congr 1
    funext m
    have hm := m.isLt
    exact finRule_apply_of_noBad hs1 hs2 hs3 hnb (by omega)

/-- A nonzero finite configuration has a set leftmost cell, clear cells left of it and clear cells
right of its rightmost. -/
private theorem exists_endpoints (hs : s ≠ 0) :
    ∃ e r : ℤ, s e = 1 ∧ (∀ i, i < e → s i = 0) ∧ (∀ i, r < i → s i = 0) := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  refine ⟨s.support.min' hne, s.support.max' hne, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rcases zmod2_zero_or_one (s (s.support.min' hne)) with h | h
    · exact absurd h (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
    · exact h
  · by_contra hcon
    exact absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hcon)) (by omega)
  · by_contra hcon
    exact absurd (Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hcon)) (by omega)

end Settled

/-- **Table `206` fixes every reading of a conserved code under an injective law**: a sliding block
code of any window, with an injective law, a semiconjugacy from the table's update on the light cone
of any window restricted to the growing part, is unchanged by a step at every state of the fiber.
The code's local rule is zero on every window `0^a 1^b` with no `10`, and a nonzero state reaches
a state at which a step changes one cell, the new left end, which only windows of that form read
([RuleSpace] §2 Proposition 2.6, the merge invariance and the reduction). -/
theorem blockCode_finRule_eq_of_injective_law_f206 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f206 hq206) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam))
    (t : ℕ) (s : FiniteConfiguration)
    (hs : s ∈ lightCone n t ∩
      Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam) :
    FiniteConfiguration.blockCode L g hg (LocalRule.finRule f206 hq206 s) =
      FiniteConfiguration.blockCode L g hg s := by
  have hwin := window_threshold_eq_zero g (window_eq_zero_of_injective_law_f206 n g hg hF hsq)
  have hs0 : s ≠ 0 := by
    have h := hs.2
    rw [growingPart_f206_eq_ne_zero] at h
    exact h
  obtain ⟨e, r, h1, h2, h3⟩ := exists_endpoints hs0
  obtain ⟨k, hk, hnb⟩ := exists_noBad h1 h2 h3 L
  have hread := blockCode_finRule_iterate_eq g hg hwin h1 h2 h3 hk hnb
  have hadv := Nonautonomous.positivelyInvariant_growingPart
    (size := FiniteConfiguration.diam) (positivelyInvariant_lightCone_finRule f206 hq206 n)
  have hit : (LocalRule.finRule f206 hq206)^[k] (LocalRule.finRule f206 hq206 s) =
      LocalRule.finRule f206 hq206 ((LocalRule.finRule f206 hq206)^[k] s) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  exact Nonautonomous.Semiconj.eq_of_iterate_eq hF hadv hsq hs k 1 (by
    change FiniteConfiguration.blockCode L g hg
        ((LocalRule.finRule f206 hq206)^[k] (LocalRule.finRule f206 hq206 s)) = _
    rw [hit]
    exact hread)

/-- **The law is the identity on the image of the code**: at table `206`, with the hypotheses of
`blockCode_finRule_eq_of_injective_law_f206`, the injective law fixes the code of every state of the
fiber. -/
theorem law_apply_blockCode_eq_of_injective_law_f206 (n : ℕ) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    {F : FiniteConfiguration → FiniteConfiguration} (hF : Function.Injective F)
    (hsq : Nonautonomous.Semiconj (LocalRule.finRule f206 hq206) F
      (fun _ => FiniteConfiguration.blockCode L g hg)
      (fun t => lightCone n t ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam))
    (t : ℕ) (s : FiniteConfiguration)
    (hs : s ∈ lightCone n t ∩
      Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam) :
    F (FiniteConfiguration.blockCode L g hg s) = FiniteConfiguration.blockCode L g hg s :=
  (hsq t s hs).symm.trans (blockCode_finRule_eq_of_injective_law_f206 n g hg hF hsq t s hs)

/-- **The hypotheses hold together**, at table `206` with the code of the pattern `10`, which is not
zero, and the identity as the law: the local rule sends the zero window to zero, the law is
injective, the code closes the semiconjugacy on the light cone restricted to the growing part, and
the state with one set cell lies in the fiber at time `1`. -/
theorem blockCode_finRule_eq_of_injective_law_f206_nonvacuous (n : ℕ) :
    (∃ w : Fin 2 → ZMod 2, codeF206 w ≠ 0) ∧ codeF206 0 = 0 ∧
      Function.Injective (id : FiniteConfiguration → FiniteConfiguration) ∧
      Nonautonomous.Semiconj (LocalRule.finRule f206 hq206) id
        (fun _ => FiniteConfiguration.blockCode 2 codeF206 codeF206_zero)
        (fun t => lightCone n t ∩
          Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam) ∧
      Finsupp.single (0 : ℤ) (1 : ZMod 2) ∈ lightCone n 1 ∩
        Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam := by
  refine ⟨⟨fun k => if k = 0 then 1 else 0, by decide⟩, codeF206_zero, Function.injective_id,
    fun t s _ => blockCode_finRule_f206 s, ?_, ?_⟩
  · intro i hi
    have h0 : i = 0 := by
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hi) (by simp [Ne.symm hne])
    subst h0
    push_cast
    exact ⟨trivial, by omega⟩
  · rw [growingPart_f206_eq_ne_zero]
    exact Finsupp.single_ne_zero.mpr one_ne_zero

end ECA
