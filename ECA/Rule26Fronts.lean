module

public import ECA.KinkMonotone
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import ECA.Rule26Clearing

/-!
# Rules `26` and `82`: a held suffix of one parity from two statements about spaced states

A kink of a finite configuration is a pair of consecutive set cells at odd distance, and its right
cell is the kink's right end.
A configuration is **spaced** (`FiniteConfiguration.Spaced`) when it holds no word `1 0^(2r) 1 1`,
that is, when no kink's right end has its right neighbour set.
At rule `26` a spaced state stays spaced, the right ends of its kinks each move one cell left at
every step, and past the last of them the orbit is the orbit of the state's part from there on,
which is of one parity (`spacedHeld_f26`); and every finite configuration reaches a spaced state
(`reachesSpaced_f26`).
The first fact is `LocalRule.SpacedHeld` at rule `26` and the second is `LocalRule.ReachesSpaced`
at rule `26`; both are proved here.
The second runs on the kink count, which rule `26` never increases (`kinkCountMono_f26`, after
Sabrié and Törmä 2023 and Kůrka 2003): a state that is not spaced has a least bad cell, and the
orbit reaches a spaced state or a state whose least bad cell follows more fronts.
Together they give the held suffix of one parity (`LocalRule.EventuallyOneParitySuffix`): run the
state until it is spaced, then take the suffix from the last right end.
The conditional theorems `conservesNoCode_f26_f82_of_spaced` and
`conservesNoCode_f26_f82_of_reachesSpaced` give that rules `26` and `82` conserve no sliding
block code but zero from either or both of the two facts, and with both proved
`conservesNoCode_f26_f82`, `clearsWindows_f26` and `clearsWindows_f82` hold with no hypothesis.

## Main results

* `FiniteConfiguration.Spaced` — no word `1 0^(2r) 1 1`.
* `LocalRule.SpacedHeld` — every spaced state has a suffix of one parity whose own orbit the
  state's orbit follows on every cell the suffix's left end reaches moving left at one cell a step.
* `spacedHeld_f26` — it holds at rule `26`.
* `LocalRule.ReachesSpaced` — every finite configuration reaches a spaced state.
* `reachesSpaced_f26` — it holds at rule `26`.
* `LocalRule.ReachesSpaced.eventuallyOneParitySuffix` — the two hypotheses compose to the held
  suffix of one parity, and `LocalRule.ReachesSpaced.eventuallyOneParitySuffix_nonvacuous` shows
  they hold together.
* `conservesNoCode_f26_f82_of_spaced` — rules `26` and `82` conserve no sliding block code but
  zero, with the two hypotheses at rule `26` as the conditions.
* `conservesNoCode_f26_f82_of_reachesSpaced` — the same, with `LocalRule.ReachesSpaced` at rule
  `26` as the one condition.
* `conservesNoCode_f26_f82` — **rules `26` and `82` conserve no sliding block code but zero**, with
  no hypothesis.
* `clearsWindows_f26` and `clearsWindows_f82` — rules `26` and `82` clear windows, with no
  hypothesis.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- A finite configuration is spaced when it holds no word `1 0^(2r) 1 1`: no set cell whose
nearest set cell to the left lies at odd distance has its right neighbour set. -/
def FiniteConfiguration.Spaced (s : FiniteConfiguration) : Prop :=
  ∀ p F : ℤ, p < F → s p ≠ 0 → s F ≠ 0 → Odd (F - p) → (∀ m, p < m → m < F → s m = 0) →
    s (F + 1) = 0

/-- Every spaced state has a suffix of one parity whose own orbit the state's orbit follows on
every cell the suffix's left end reaches moving left at one cell a step. -/
def LocalRule.SpacedHeld (f : LocalRule) (hq : f 0 0 0 = 0) : Prop :=
  ∀ s : FiniteConfiguration, s.Spaced → ∃ q : ℤ,
    OneParity (s.filter (fun i => q ≤ i)) ∧
      ∀ (m : ℕ) (i : ℤ), q - m ≤ i →
        ((finRule f hq)^[m] s) i = ((finRule f hq)^[m] (s.filter (fun i => q ≤ i))) i

/-- Every finite configuration reaches a spaced state. -/
def LocalRule.ReachesSpaced (f : LocalRule) (hq : f 0 0 0 = 0) : Prop :=
  ∀ z : FiniteConfiguration, ∃ n : ℕ, ((finRule f hq)^[n] z).Spaced

/-- **Reaching a spaced state and holding a suffix of one parity from every spaced state give the
held suffix of one parity**: run the configuration until it is spaced and take the suffix of that
state; the orbit from there is the orbit of the spaced state, which the second hypothesis
compares with the suffix's own. -/
theorem LocalRule.ReachesSpaced.eventuallyOneParitySuffix {f : LocalRule} {hq : f 0 0 0 = 0}
    (hr : f.ReachesSpaced hq) (hs : f.SpacedHeld hq) : f.EventuallyOneParitySuffix hq := by
  intro z
  obtain ⟨n, hn⟩ := hr z
  obtain ⟨q, hone, hheld⟩ := hs _ hn
  refine ⟨n, q, hone, fun m i hi => ?_⟩
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hheld m i hi

private theorem zeroTable_finRule (s : FiniteConfiguration) :
    finRule (fun _ _ _ => (0 : ZMod 2)) rfl s = 0 := by
  ext i
  rw [finRule_apply]
  rfl

private theorem zeroTable_iterate_succ (m : ℕ) (s : FiniteConfiguration) :
    (finRule (fun _ _ _ => (0 : ZMod 2)) rfl)^[m + 1] s = 0 := by
  induction m with
  | zero => exact zeroTable_finRule s
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      exact zeroTable_finRule 0

private theorem spaced_zero : (0 : FiniteConfiguration).Spaced := by
  intro p F _ hp
  exact absurd rfl hp

/-- The two hypotheses of `LocalRule.ReachesSpaced.eventuallyOneParitySuffix` hold together: at the
zero table every configuration is clear after one step, and the clear configuration is spaced; the
suffix of a spaced state from a cell beyond its support is zero, hence of one parity, and the
orbit agrees with it on every cell from there at step zero and after the first step. -/
theorem LocalRule.ReachesSpaced.eventuallyOneParitySuffix_nonvacuous :
    LocalRule.ReachesSpaced (fun _ _ _ => (0 : ZMod 2)) rfl ∧
      LocalRule.SpacedHeld (fun _ _ _ => (0 : ZMod 2)) rfl := by
  refine ⟨fun z => ⟨1, ?_⟩, fun s _ => ?_⟩
  · rw [zeroTable_iterate_succ 0 z]
    exact spaced_zero
  · set B : ℕ := s.support.sup (fun i => i.natAbs) with hB
    have hbeyond : ∀ i : ℤ, (B : ℤ) + 1 ≤ i → s i = 0 := fun i hi => by
      by_contra hc
      have : i.natAbs ≤ B := Finset.le_sup (f := fun i : ℤ => i.natAbs)
        (Finsupp.mem_support_iff.mpr hc)
      omega
    have hfilt : s.filter (fun i => (B : ℤ) + 1 ≤ i) = 0 := by
      ext i
      rw [Finsupp.filter_apply]
      split_ifs with h
      · exact hbeyond i h
      · rfl
    refine ⟨(B : ℤ) + 1, ?_, fun m i hi => ?_⟩
    · rw [hfilt]
      intro i j hi
      exact absurd rfl hi
    · rw [hfilt]
      cases m with
      | zero =>
          rw [Function.iterate_zero, id_eq, id_eq]
          exact hbeyond i (by simpa using hi)
      | succ m =>
          rw [zeroTable_iterate_succ, zeroTable_iterate_succ]

/-! ## Rule `26` holds the suffix of every spaced state

The phase of a state at a cell is the parity of the distance from the cell to the nearest set cell
at or to its left.
A front is a set cell whose nearest set cell on the left, if there is one, lies at an odd
distance; the least set cell is a front, and a state of one parity from a cell on has no front
above it.
On a spaced state a step of rule `26` shifts the phase by one cell, keeps the state spaced and
moves each front one cell left, and the cell two left of a front is clear; so from the largest
front the orbit of the state and the orbit of its part from there on agree, the front moving left
at one cell a step. -/

/-- The phase of a state at a cell `j`: the parity of the distance from `j` to the nearest set cell
at or to its left, and `none` when no set cell lies there. -/
private noncomputable def leftPhase (t : FiniteConfiguration) (j : ℤ) : Option (ZMod 2) :=
  if h : (t.support.filter (fun i => i ≤ j)).Nonempty then
    some (((j - (t.support.filter (fun i => i ≤ j)).max' h : ℤ)) : ZMod 2)
  else none

/-- The phase at the next cell from the phase at a cell and the value at the next cell: a set cell
has phase `0`, and a clear one flips the phase to its left. -/
private def nextPhase (b : ZMod 2) (φ : Option (ZMod 2)) : Option (ZMod 2) :=
  if b = 0 then φ.map (· + 1) else some 0

/-- The phase at `j + 1` from the phase at `j` and the value at `j + 1`. -/
private theorem leftPhase_succ (t : FiniteConfiguration) (j : ℤ) :
    leftPhase t (j + 1) = nextPhase (t (j + 1)) (leftPhase t j) := by
  by_cases hb : t (j + 1) = 0
  · have hS : t.support.filter (fun i => i ≤ j + 1) = t.support.filter (fun i => i ≤ j) := by
      ext i
      simp only [Finset.mem_filter, Finsupp.mem_support_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        by_contra hc
        have : i = j + 1 := by omega
        exact h1 (this ▸ hb)
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
    unfold leftPhase
    rw [hS]
    by_cases hne : (t.support.filter (fun i => i ≤ j)).Nonempty
    · simp only [nextPhase, hb, hne, dite_true, ite_true, Option.map_some, Option.some.injEq]
      push_cast
      ring
    · simp [nextPhase, hb, hne]
  · have hmem : j + 1 ∈ t.support.filter (fun i => i ≤ j + 1) := by
      simp only [Finset.mem_filter, Finsupp.mem_support_iff]
      exact ⟨hb, le_refl _⟩
    have hne : (t.support.filter (fun i => i ≤ j + 1)).Nonempty := ⟨_, hmem⟩
    have hmax : (t.support.filter (fun i => i ≤ j + 1)).max' hne = j + 1 := by
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        simp only [Finset.mem_filter] at hy
        exact hy.2
      · exact Finset.le_max' _ _ hmem
    unfold leftPhase
    simp only [hne, dite_true, hmax, sub_self, Int.cast_zero, nextPhase, hb, ite_false]

/-- With no set cell at or left of `j`, the phase at `j` is `none`. -/
private theorem leftPhase_eq_none {t : FiniteConfiguration} {j : ℤ}
    (h : ∀ i, i ≤ j → t i = 0) : leftPhase t j = none := by
  have hne : ¬ (t.support.filter (fun i => i ≤ j)).Nonempty := by
    rintro ⟨i, hi⟩
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hi
    exact hi.1 (h i hi.2)
  simp [leftPhase, hne]

/-- A set cell has phase `0`. -/
private theorem leftPhase_of_ne {t : FiniteConfiguration} {j : ℤ} (h : t j ≠ 0) :
    leftPhase t j = some 0 := by
  have := leftPhase_succ t (j - 1)
  rw [sub_add_cancel] at this
  rw [this]
  simp [nextPhase, h]

/-- A phase that is `some` names the nearest set cell at or left of `j`, at the distance whose
parity it is. -/
private theorem leftPhase_eq_some {t : FiniteConfiguration} {j : ℤ} {φ : ZMod 2}
    (h : leftPhase t j = some φ) :
    ∃ p, p ≤ j ∧ t p ≠ 0 ∧ (∀ m, p < m → m ≤ j → t m = 0) ∧ φ = ((j - p : ℤ) : ZMod 2) := by
  unfold leftPhase at h
  by_cases hne : (t.support.filter (fun i => i ≤ j)).Nonempty
  · simp only [hne, dite_true, Option.some.injEq] at h
    have hmem := Finset.max'_mem _ hne
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hmem
    refine ⟨_, hmem.2, hmem.1, fun m h1 h2 => ?_, h.symm⟩
    by_contra hm
    have hm' : m ∈ t.support.filter (fun i => i ≤ j) := by
      simp only [Finset.mem_filter, Finsupp.mem_support_iff]
      exact ⟨hm, h2⟩
    have := Finset.le_max' _ m hm'
    omega
  · simp [hne] at h

/-- The finite check behind the shift of phases. -/
private theorem nextPhase_f26_local : ∀ (a b c : ZMod 2) (ψ : Option (ZMod 2)),
    (a ≠ 0 → ψ = some 0) → (b ≠ 0 → ψ = some 0 → c = 0) →
    nextPhase (f26 a b c) (nextPhase b ψ) = nextPhase c (nextPhase b ψ) := by
  unfold nextPhase f26
  decide

/-- The finite check behind the preservation of spacing. -/
private theorem phaseSpaced_f26_local : ∀ (a b c d : ZMod 2) (ψ : Option (ZMod 2)),
    (a ≠ 0 → ψ = some 0) → (b ≠ 0 → ψ = some 0 → c = 0) →
    (c ≠ 0 → nextPhase b ψ = some 0 → d = 0) →
    f26 a b c ≠ 0 → nextPhase b ψ = some 0 → f26 b c d = 0 := by
  unfold nextPhase f26
  decide

/-- The finite check behind the clear cell two left of a front. -/
private theorem gap_f26_local : ∀ (a b c : ZMod 2) (ψ : Option (ZMod 2)),
    (a ≠ 0 → ψ = some 0) → (b ≠ 0 → ψ = some 0 → c = 0) →
    c ≠ 0 → nextPhase b ψ ≠ some 1 → a = 0 := by
  unfold nextPhase
  decide

/-- The finite check behind the set cell left of a front after a step. -/
private theorem front_f26_local : ∀ (a b c : ZMod 2), a = 0 → c ≠ 0 → f26 a b c ≠ 0 := by
  unfold f26
  decide

/-- One step of rule `26` at the cell `j + 1`. -/
private theorem finRule_f26_apply_succ (t : FiniteConfiguration) (j : ℤ) :
    finRule f26 hq26 t (j + 1) = f26 (t j) (t (j + 1)) (t (j + 2)) := by
  rw [finRule_apply, add_sub_cancel_right, add_assoc, one_add_one_eq_two]

/-- Spacing in terms of phases: a set cell at distance an odd number from the nearest set cell on
its left has its right neighbour clear. -/
private def PhaseSpaced (t : FiniteConfiguration) : Prop :=
  ∀ j : ℤ, t (j + 1) ≠ 0 → leftPhase t j = some 0 → t (j + 2) = 0

/-- **Rule `26` shifts the phase by one cell** on a spaced state: the phase at `j` of the next
state is the phase at `j + 1` of the state. -/
private theorem leftPhase_finRule_f26 {t : FiniteConfiguration} (hs : PhaseSpaced t) (j : ℤ) :
    leftPhase (finRule f26 hq26 t) j = leftPhase t (j + 1) := by
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i, i < N → t i = 0 := by
    refine ⟨-((t.support.sup (fun i => i.natAbs) : ℕ) : ℤ), fun i hi => ?_⟩
    by_contra hc
    have := Finset.le_sup (f := fun i : ℤ => i.natAbs) (Finsupp.mem_support_iff.mpr hc)
    omega
  have hnone : ∀ j, j ≤ N - 2 →
      leftPhase (finRule f26 hq26 t) j = none ∧ leftPhase t (j + 1) = none := by
    intro j hj
    refine ⟨leftPhase_eq_none fun i hi => ?_, leftPhase_eq_none fun i hi => hN i (by omega)⟩
    rw [finRule_apply, hN (i - 1) (by omega), hN i (by omega), hN (i + 1) (by omega)]
    exact hq26
  by_cases hj : j ≤ N - 2
  · rw [(hnone j hj).1, (hnone j hj).2]
  · have hall : ∀ n : ℕ, leftPhase (finRule f26 hq26 t) (N - 2 + n) =
        leftPhase t (N - 2 + n + 1) := by
      intro n
      induction n with
      | zero =>
          rw [Nat.cast_zero, add_zero, (hnone (N - 2) le_rfl).1, (hnone (N - 2) le_rfl).2]
      | succ n ih =>
          rw [Nat.cast_succ, ← add_assoc, leftPhase_succ (finRule f26 hq26 t) _, ih,
            finRule_f26_apply_succ, leftPhase_succ t (N - 2 + n + 1),
            show N - 2 + n + 1 + 1 = N - 2 + n + 2 by omega, leftPhase_succ t (N - 2 + n)]
          exact nextPhase_f26_local _ _ _ _ (fun h => leftPhase_of_ne h) (hs _)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, j = N - 2 + n := ⟨(j - (N - 2)).toNat, by omega⟩
    rw [hn]
    exact hall n

/-- A front of a state: a set cell whose nearest set cell on the left, if there is one, lies at an
odd distance. -/
private def IsFront (t : FiniteConfiguration) (r : ℤ) : Prop :=
  t r ≠ 0 ∧ leftPhase t (r - 1) ≠ some 1

/-- On a spaced state the cell two left of a front is clear. -/
private theorem IsFront.gap {t : FiniteConfiguration} (hs : PhaseSpaced t) {r : ℤ}
    (hf : IsFront t r) :
    t (r - 2) = 0 := by
  obtain ⟨hr, hp⟩ := hf
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by ring⟩
  rw [add_sub_cancel_right]
  rw [show j + 2 - 1 = j + 1 by ring, leftPhase_succ] at hp
  by_contra hj
  exact hj (gap_f26_local (t j) (t (j + 1)) (t (j + 2)) (leftPhase t j)
    (fun h => leftPhase_of_ne h) (hs j) hr hp)

/-- On a spaced state a front moves one cell left in one step of rule `26`. -/
private theorem IsFront.finRule_f26 {t : FiniteConfiguration} (hs : PhaseSpaced t) {r : ℤ}
    (hf : IsFront t r) :
    IsFront (finRule f26 hq26 t) (r - 1) := by
  have h0 := IsFront.gap hs hf
  obtain ⟨hr, hp⟩ := hf
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by ring⟩
  rw [add_sub_cancel_right] at h0
  rw [show j + 2 - 1 = j + 1 by ring] at hp ⊢
  refine ⟨?_, ?_⟩
  · rw [finRule_f26_apply_succ]
    exact front_f26_local _ _ _ h0 hr
  · rw [show j + 1 - 1 = j by ring, leftPhase_finRule_f26 hs]
    exact hp

/-- A step of rule `26` keeps a state spaced. -/
private theorem phaseSpaced_finRule_f26 {t : FiniteConfiguration} (hs : PhaseSpaced t) :
    PhaseSpaced (finRule f26 hq26 t) := by
  intro j h1 h2
  rw [leftPhase_finRule_f26 hs] at h2
  rw [finRule_f26_apply_succ] at h1
  have e2 : finRule f26 hq26 t (j + 2) = f26 (t (j + 1)) (t (j + 2)) (t (j + 3)) := by
    rw [finRule_apply, show j + 2 - 1 = j + 1 by ring, show j + 2 + 1 = j + 3 by ring]
  rw [e2]
  have e : leftPhase t (j + 1) = nextPhase (t (j + 1)) (leftPhase t j) := leftPhase_succ t j
  rw [e] at h2
  have hs' := hs (j + 1)
  rw [show j + 1 + 1 = j + 2 by ring, show j + 1 + 2 = j + 3 by ring, e] at hs'
  exact phaseSpaced_f26_local (t j) (t (j + 1)) (t (j + 2)) (t (j + 3)) (leftPhase t j)
    (fun h => leftPhase_of_ne h) (hs j) hs' h1 h2

/-- The finite check behind the agreement at the front's own cell. -/
private theorem agree_f26_local : ∀ (a b c : ZMod 2), b ≠ 0 → (a ≠ 0 → c = 0) →
    f26 a b c = f26 0 b c := by
  unfold f26
  decide

/-- One step of the induction: a spaced state with a front `r`, and a state agreeing with it from
`r` on and clear left of `r`, keep all four properties at the front `r - 1` after a step. -/
private theorem held_step {t u : FiniteConfiguration} {r : ℤ} (hs : PhaseSpaced t)
    (hf : IsFront t r)
    (hag : ∀ i, r ≤ i → t i = u i) (hu : ∀ i, i < r → u i = 0) :
    PhaseSpaced (finRule f26 hq26 t) ∧ IsFront (finRule f26 hq26 t) (r - 1) ∧
      (∀ i, r - 1 ≤ i → finRule f26 hq26 t i = finRule f26 hq26 u i) ∧
      (∀ i, i < r - 1 → finRule f26 hq26 u i = 0) := by
  refine ⟨phaseSpaced_finRule_f26 hs, IsFront.finRule_f26 hs hf, ?_, ?_⟩
  · intro i hi
    have h0 := IsFront.gap hs hf
    have hr := hf.1
    rw [finRule_apply, finRule_apply]
    rcases (show i = r - 1 ∨ i = r ∨ r + 1 ≤ i by omega) with rfl | rfl | h
    · rw [sub_add_cancel, show r - 1 - 1 = r - 2 by ring, h0, hu (r - 2) (by omega),
        hu (r - 1) (by omega), ← hag r le_rfl]
      simp [f26]
    · have hs' := hs (i - 1)
      rw [sub_add_cancel, show i - 1 + 2 = i + 1 by ring] at hs'
      rw [hu (i - 1) (by omega), ← hag i le_rfl, ← hag (i + 1) (by omega)]
      exact agree_f26_local _ _ _ hr (fun ha => hs' hr (leftPhase_of_ne ha))
    · rw [← hag (i - 1) (by omega), ← hag i (by omega), ← hag (i + 1) (by omega)]
  · intro i hi
    rw [finRule_apply, hu (i - 1) (by omega), hu i (by omega), hu (i + 1) (by omega)]
    exact hq26

/-- The induction: the four properties of `held_step` hold at the front `q - m` after `m` steps. -/
private theorem held_iterate {s u : FiniteConfiguration} {q : ℤ} (hs : PhaseSpaced s)
    (hf : IsFront s q)
    (hag : ∀ i, q ≤ i → s i = u i) (hu : ∀ i, i < q → u i = 0) (m : ℕ) :
    PhaseSpaced ((finRule f26 hq26)^[m] s) ∧ IsFront ((finRule f26 hq26)^[m] s) (q - m) ∧
      (∀ i, q - m ≤ i → ((finRule f26 hq26)^[m] s) i = ((finRule f26 hq26)^[m] u) i) ∧
      (∀ i, i < q - m → ((finRule f26 hq26)^[m] u) i = 0) := by
  induction m with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero]
      exact ⟨hs, hf, hag, hu⟩
  | succ m ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have := held_step h1 h2 h3 h4
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        show q - ((m + 1 : ℕ) : ℤ) = q - m - 1 by push_cast; ring]
      exact this

/-- A spaced state is spaced in terms of phases. -/
private theorem phaseSpaced_of_spaced {s : FiniteConfiguration} (hs : s.Spaced) :
    PhaseSpaced s := by
  intro j h1 h2
  obtain ⟨p, hp, hpne, hbetween, hφ⟩ := leftPhase_eq_some h2
  have heven : Even (j - p) := (ZMod.intCast_eq_zero_iff_even).1 hφ.symm
  obtain ⟨k, hk⟩ := heven
  have := hs p (j + 1) (by omega) hpne h1 ⟨k, by omega⟩
    (fun m a b => hbetween m a (by omega))
  rwa [show j + 1 + 1 = j + 2 by ring] at this

/-- A nonzero state has a largest front: the least set cell is one. -/
private theorem exists_largest_front {s : FiniteConfiguration} (h : s ≠ 0) :
    ∃ q, IsFront s q ∧ ∀ y, IsFront s y → y ≤ q := by
  classical
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr h
  have hx0 : IsFront s (s.support.min' hne) := by
    refine ⟨Finsupp.mem_support_iff.mp (Finset.min'_mem _ _), ?_⟩
    rw [leftPhase_eq_none]
    · simp
    · intro i hi
      by_contra hc
      have := Finset.min'_le _ i (Finsupp.mem_support_iff.mpr hc)
      omega
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image (s.support.filter (fun y => IsFront s y)) id
    ⟨_, Finset.mem_filter.mpr ⟨Finset.min'_mem _ _, hx0⟩⟩
  refine ⟨q, (Finset.mem_filter.mp hq).2, fun y hy => ?_⟩
  exact hmax y (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hy.1, hy⟩)

/-- The part of a state from its largest front on is of one parity: no front lies above it, so
the phase at every cell from there on is the parity of the distance to the front. -/
private theorem oneParity_part {s : FiniteConfiguration} {q : ℤ} (hf : IsFront s q)
    (hmax : ∀ y, IsFront s y → y ≤ q) : OneParity (s.filter (fun i => q ≤ i)) := by
  have hall : ∀ n : ℕ, leftPhase s (q + n) = some (((q + n - q : ℤ)) : ZMod 2) := by
    intro n
    induction n with
    | zero => simp [leftPhase_of_ne hf.1]
    | succ n ih =>
        rw [Nat.cast_succ, ← add_assoc, leftPhase_succ, ih]
        have e : (((q + n + 1 - q : ℤ)) : ZMod 2) = (((q + n - q : ℤ)) : ZMod 2) + 1 := by
          push_cast; ring
        by_cases hb : s (q + n + 1) = 0
        · simp only [nextPhase, hb, ite_true, Option.map_some, e]
        · simp only [nextPhase, hb, ite_false, e]
          by_contra hne
          have hν : (((q + n - q : ℤ)) : ZMod 2) ≠ 1 := fun h1 => by
            apply hne
            rw [h1]
            decide
          have := hmax (q + n + 1) ⟨hb, by
            rw [add_sub_cancel_right, ih]
            intro h2
            exact hν (Option.some.inj h2)⟩
          omega
  have hphase : ∀ i, q ≤ i → s i ≠ 0 → Even (i - q) := by
    intro i hqi hi
    obtain ⟨n, hn⟩ : ∃ n : ℕ, i = q + n := ⟨(i - q).toNat, by omega⟩
    have h1 := leftPhase_of_ne hi
    rw [hn, hall n] at h1
    rw [hn]
    exact (ZMod.intCast_eq_zero_iff_even).1 (Option.some.inj h1)
  have hmem : ∀ i, (s.filter (fun i => q ≤ i)) i ≠ 0 → q ≤ i ∧ s i ≠ 0 := by
    intro i hi
    rw [Finsupp.filter_apply] at hi
    split_ifs at hi with h
    · exact ⟨h, hi⟩
    · exact absurd rfl hi
  intro i j hi hj
  obtain ⟨hi1, hi2⟩ := hmem i hi
  obtain ⟨hj1, hj2⟩ := hmem j hj
  obtain ⟨a, ha⟩ := hphase i hi1 hi2
  obtain ⟨b, hb⟩ := hphase j hj1 hj2
  exact ⟨a - b, by omega⟩


/-- **Rule `26` holds a suffix of one parity from every spaced state.** A nonzero spaced state has
a largest front, a set cell whose nearest set cell on the left, if any, lies at an odd distance;
its part from there on is of one parity.
At each step of rule `26` the state stays spaced and the front moves one cell left, with the cell
two left of it clear, so the orbit of the state agrees with the orbit of that part on every cell
from the front's position moving left at one cell a step. -/
theorem spacedHeld_f26 : LocalRule.SpacedHeld f26 hq26 := by
  intro s hs
  by_cases h0 : s = 0
  · subst h0
    have hz : (0 : FiniteConfiguration).filter (fun i => (0 : ℤ) ≤ i) = 0 := by
      ext i
      simp [Finsupp.filter_apply]
    refine ⟨0, ?_, fun m i _ => ?_⟩
    · rw [hz]
      intro i j hi
      exact absurd rfl hi
    · rw [hz]
  · obtain ⟨q, hq, hmax⟩ := exists_largest_front h0
    refine ⟨q, oneParity_part hq hmax, fun m i hi => ?_⟩
    exact (held_iterate (phaseSpaced_of_spaced hs) hq
      (fun i hi => by simp [hi])
      (fun i hi => by simp [not_le.2 hi]) m).2.2.1 i hi

/-- **Rules `26` and `82` conserve no sliding block code but zero**, with two hypotheses at rule
`26`: every finite configuration reaches a spaced state (`LocalRule.ReachesSpaced`), and every
spaced state has a suffix of one parity whose orbit the state's follows (`LocalRule.SpacedHeld`).
They compose to the held suffix of one parity, which gives the conclusion. -/
theorem conservesNoCode_f26_f82_of_spaced (hr : LocalRule.ReachesSpaced f26 hq26)
    (hs : LocalRule.SpacedHeld f26 hq26) :
    LocalRule.ConservesNoCode f26 hq26 ∧ LocalRule.ConservesNoCode f82 hq82 :=
  conservesNoCode_f26_f82_of_eventuallyOneParitySuffix (hr.eventuallyOneParitySuffix hs)

/-- **Rules `26` and `82` conserve no sliding block code but zero**, with one hypothesis at rule
`26`: every finite configuration reaches a spaced state (`LocalRule.ReachesSpaced`). The other
hypothesis of `conservesNoCode_f26_f82_of_spaced` holds at rule `26` (`spacedHeld_f26`). -/
theorem conservesNoCode_f26_f82_of_reachesSpaced (hr : LocalRule.ReachesSpaced f26 hq26) :
    LocalRule.ConservesNoCode f26 hq26 ∧ LocalRule.ConservesNoCode f82 hq82 :=
  conservesNoCode_f26_f82_of_spaced hr spacedHeld_f26

/-! ## Every finite state reaches a spaced one

A bad cell of a state is a front other than the least set cell whose right neighbour is set; a
state is spaced exactly when it has none.
Its least bad cell `B` cuts the state to a part `P` up to `B`, which is spaced.
By the light cone the orbit of the state agrees with the orbit of `P` on every cell at most `B`
minus the time, and on the orbit of `P` the cells between the two fronts `B'` and `B` left of `B`
evolve by rule `90` while the front `B'` moves left at one cell a step, so the cell left of the
front `B` is set at some time.
Then rule `26` clears the right neighbour of the front, and the orbit has no bad cell up to two
cells beyond it: either it is spaced, or its least bad cell is a new front.
The number of fronts up to the least bad cell grows at each such event, and is bounded by the kink
count plus one, which does not increase (`kinkCountMono_f26`; the kink count is Sabrié and Törmä's,
2023, after Kůrka 2003). -/

/-- A bad cell: a set cell whose nearest set cell to the left lies at an odd distance and whose
right neighbour is set. -/
private def Bad (t : FiniteConfiguration) (r : ℤ) : Prop :=
  t r ≠ 0 ∧ leftPhase t (r - 1) = some 0 ∧ t (r + 1) ≠ 0

private theorem phaseSpaced_of_noBad {t : FiniteConfiguration} (h : ∀ r, ¬ Bad t r) :
    PhaseSpaced t := by
  intro j h1 h2
  by_contra h3
  exact h (j + 1) ⟨h1, by rwa [add_sub_cancel_right], by rwa [show j + 1 + 1 = j + 2 by ring]⟩

private theorem not_bad_of_phaseSpaced {t : FiniteConfiguration} (hs : PhaseSpaced t) (r : ℤ) :
    ¬ Bad t r := by
  rintro ⟨h1, h2, h3⟩
  have := hs (r - 1) (by rwa [sub_add_cancel]) h2
  rw [show r - 1 + 2 = r + 1 by ring] at this
  exact h3 this

private theorem Bad.isFront {t : FiniteConfiguration} {r : ℤ} (h : Bad t r) : IsFront t r :=
  ⟨h.1, by rw [h.2.1]; decide⟩

/-- The cells of a state are clear far to the left. -/
private theorem exists_lower {t : FiniteConfiguration} : ∃ N : ℤ, ∀ i, i < N → t i = 0 := by
  refine ⟨-((t.support.sup (fun i => i.natAbs) : ℕ) : ℤ), fun i hi => ?_⟩
  by_contra hc
  have := Finset.le_sup (f := fun i : ℤ => i.natAbs) (Finsupp.mem_support_iff.mpr hc)
  omega

/-- A state with a bad cell has a least one. -/
private theorem exists_least_bad {t : FiniteConfiguration} (h : ∃ r, Bad t r) :
    ∃ B, Bad t B ∧ ∀ r, r < B → ¬ Bad t r := by
  classical
  obtain ⟨r, hr⟩ := h
  have hne : (t.support.filter (fun r => Bad t r)).Nonempty :=
    ⟨r, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hr.1, hr⟩⟩
  have hmem := Finset.mem_filter.mp (Finset.min'_mem _ hne)
  refine ⟨_, hmem.2, fun r' hr' hb => ?_⟩
  have := Finset.min'_le (t.support.filter (fun r => Bad t r)) r'
    (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hb.1, hb⟩)
  omega

/-- A state agrees with the part of itself up to a cell on every cell at most that cell. -/
private theorem iterate_agree {t u : FiniteConfiguration} {B : ℤ}
    (h : ∀ i, i ≤ B → t i = u i) :
    ∀ (τ : ℕ) (i : ℤ), i ≤ B - τ →
      ((finRule f26 hq26)^[τ] t) i = ((finRule f26 hq26)^[τ] u) i := by
  intro τ
  induction τ with
  | zero =>
      intro i hi
      simpa using h i (by simpa using hi)
  | succ τ ih =>
      intro i hi
      push_cast at hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', finRule_apply,
        finRule_apply, ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]

/-- The phase at a cell reads only the cells at or left of it. -/
private theorem leftPhase_congr {t u : FiniteConfiguration} {j : ℤ}
    (h : ∀ i, i ≤ j → t i = u i) : leftPhase t j = leftPhase u j := by
  have hS : t.support.filter (fun i => i ≤ j) = u.support.filter (fun i => i ≤ j) := by
    ext i
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [← h i h2], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [h i h2], h2⟩
  unfold leftPhase
  rw [hS]

/-- Being a front reads only the cells at or left of it. -/
private theorem isFront_congr {t u : FiniteConfiguration} {r : ℤ}
    (h : ∀ i, i ≤ r → t i = u i) : IsFront t r ↔ IsFront u r := by
  unfold IsFront
  rw [h r le_rfl, leftPhase_congr (j := r - 1) (fun i hi => h i (by omega))]

private theorem phaseSpaced_iterate {t : FiniteConfiguration} (hs : PhaseSpaced t) (τ : ℕ) :
    PhaseSpaced ((finRule f26 hq26)^[τ] t) := by
  induction τ with
  | zero => exact hs
  | succ τ ih =>
      rw [Function.iterate_succ_apply']
      exact phaseSpaced_finRule_f26 ih

/-- The finite check behind the converse of the motion of fronts. -/
private theorem front_back_local : ∀ (a b c : ZMod 2) (ψ : Option (ZMod 2)),
    (a ≠ 0 → ψ = some 0) → nextPhase b ψ ≠ some 1 → f26 a b c ≠ 0 → c ≠ 0 := by
  unfold nextPhase f26
  decide

/-- On a spaced state the fronts of the next state are the fronts of the state moved one cell
left. -/
private theorem isFront_finRule_f26_iff {t : FiniteConfiguration} (hs : PhaseSpaced t) (j : ℤ) :
    IsFront (finRule f26 hq26 t) j ↔ IsFront t (j + 1) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [show j - 1 = (j - 2) + 1 by ring, leftPhase_finRule_f26 hs,
      show j - 2 + 1 + 1 = j by ring] at h2
    have e := leftPhase_succ t (j - 1)
    rw [sub_add_cancel] at e
    have hj : leftPhase t j ≠ some 1 := h2
    rw [e] at h2
    have h3 : t (j + 1) ≠ 0 := by
      rw [finRule_apply] at h1
      exact front_back_local (t (j - 1)) (t j) (t (j + 1)) (leftPhase t (j - 1))
        (fun h => leftPhase_of_ne h) h2 h1
    exact ⟨h3, by rwa [add_sub_cancel_right]⟩
  · intro hf
    have := IsFront.finRule_f26 hs hf
    rwa [add_sub_cancel_right] at this

private theorem isFront_iterate_iff {t : FiniteConfiguration} (hs : PhaseSpaced t) (τ : ℕ)
    (j : ℤ) : IsFront ((finRule f26 hq26)^[τ] t) j ↔ IsFront t (j + τ) := by
  induction τ generalizing j with
  | zero => simp
  | succ τ ih =>
      rw [Function.iterate_succ_apply', isFront_finRule_f26_iff (phaseSpaced_iterate hs τ), ih]
      push_cast
      rw [add_assoc, add_comm 1 (τ : ℤ)]

/-- The least set cell of a nonzero state is a front. -/
private theorem isFront_min {s : FiniteConfiguration} (h : s ≠ 0) :
    IsFront s (s.support.min' (Finsupp.support_nonempty_iff.mpr h)) := by
  refine ⟨Finsupp.mem_support_iff.mp (Finset.min'_mem _ _), ?_⟩
  rw [leftPhase_eq_none]
  · simp
  · intro i hi
    by_contra hc
    have := Finset.min'_le _ i (Finsupp.mem_support_iff.mpr hc)
    omega

/-- A front with a set cell below it has a front below it with no front between. -/
private theorem exists_prev_front {s : FiniteConfiguration} {B p : ℤ}
    (hp : p < B) (hps : s p ≠ 0) :
    ∃ B', IsFront s B' ∧ B' < B ∧ ∀ y, B' < y → y < B → ¬ IsFront s y := by
  classical
  have h0 : s ≠ 0 := fun h => hps (by simp [h])
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr h0
  have hmin : s.support.min' hne ∈ s.support.filter (fun y => IsFront s y ∧ y < B) := by
    refine Finset.mem_filter.mpr ⟨Finset.min'_mem _ _, isFront_min h0, ?_⟩
    exact lt_of_le_of_lt (Finset.min'_le _ p (Finsupp.mem_support_iff.mpr hps)) hp
  obtain ⟨B', hB'S, hmax⟩ := Finset.exists_max_image
    (s.support.filter (fun y => IsFront s y ∧ y < B)) id ⟨_, hmin⟩
  rw [Finset.mem_filter] at hB'S
  refine ⟨B', hB'S.2.1, hB'S.2.2, fun y h1 h2 hy => ?_⟩
  have := hmax y (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hy.1, hy, h2⟩)
  simp only [id] at this
  omega

/-- A set cell at or left of `j` gives a phase at `j`. -/
private theorem leftPhase_ne_none {t : FiniteConfiguration} {i j : ℤ} (h : t i ≠ 0) (hij : i ≤ j) :
    ∃ φ, leftPhase t j = some φ := by
  have hne : (t.support.filter (fun i => i ≤ j)).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, hij⟩⟩
  unfold leftPhase
  simp only [hne, dite_true]
  exact ⟨_, rfl⟩

/-- The nearest set cell at or left of `j` determines the phase at `j`. -/
private theorem leftPhase_of_nearest {t : FiniteConfiguration} {p j : ℤ} (hp : t p ≠ 0)
    (hpj : p ≤ j) (hbet : ∀ m, p < m → m ≤ j → t m = 0) :
    leftPhase t j = some (((j - p : ℤ)) : ZMod 2) := by
  have hne : (t.support.filter (fun i => i ≤ j)).Nonempty :=
    ⟨p, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hp, hpj⟩⟩
  have hmax : (t.support.filter (fun i => i ≤ j)).max' hne = p := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hy
      by_contra hc
      exact hy.1 (hbet y (by omega) hy.2)
    · exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hp, hpj⟩)
  unfold leftPhase
  simp only [hne, dite_true, hmax]

/-- A state that is spaced in terms of phases is spaced. -/
private theorem spaced_of_phaseSpaced {s : FiniteConfiguration} (hs : PhaseSpaced s) :
    s.Spaced := by
  intro p F hpF hp hF hodd hbetween
  by_contra hne
  have h1 : leftPhase s (F - 1) = some 0 := by
    rw [leftPhase_of_nearest hp (by omega) (fun m h1 h2 => hbetween m h1 (by omega))]
    congr 1
    exact (ZMod.intCast_eq_zero_iff_even).2 (by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by omega⟩)
  have := hs (F - 1) (by rwa [sub_add_cancel]) h1
  rw [show F - 1 + 2 = F + 1 by ring] at this
  exact hne this

open scoped Classical in
/-- The number of fronts of a state at most a cell. -/
private noncomputable def frontCount (t : FiniteConfiguration) (b : ℤ) : ℕ :=
  (t.support.filter (fun r => IsFront t r ∧ r ≤ b)).card

/-- The number of fronts of a state is at most its kink count plus one: each front but the least
set cell is the right end of a kink, and a kink's left end determines it. -/
private theorem frontCount_le_kinkCount (t : FiniteConfiguration) (b : ℤ) :
    frontCount t b ≤ kinkCount t + 1 := by
  classical
  by_cases h0 : t = 0
  · subst h0
    simp [frontCount]
  have hne : t.support.Nonempty := Finsupp.support_nonempty_iff.mpr h0
  set x := t.support.min' hne with hx
  have hxf : IsFront t x := isFront_min h0
  have key : ((t.support.filter (fun r => IsFront t r ∧ r ≤ b)).erase x).card ≤ kinkCount t := by
    unfold kinkCount
    refine Finset.card_le_card_of_forall_subsingleton
      (fun (r p : ℤ) => p < r ∧ (∀ m, p < m → m < r → t m = 0) ∧ t p ≠ 0 ∧ Odd (r - p))
      (fun r hr => ?_) (fun p hp => ?_)
    · simp only [Finset.mem_erase, Finset.mem_filter, Finsupp.mem_support_iff] at hr
      obtain ⟨hrx, hrt, ⟨_, hrf⟩, _⟩ := hr
      have hxr : x < r := by
        have := Finset.min'_le t.support r (Finsupp.mem_support_iff.mpr hrt)
        exact lt_of_le_of_ne this (Ne.symm hrx)
      have hxt : t x ≠ 0 := hxf.1
      obtain ⟨φ, hφ⟩ := leftPhase_ne_none hxt (show x ≤ r - 1 by omega)
      have hφ0 : φ = 0 := by
        have hne1 := hrf
        rw [hφ] at hne1
        revert hne1
        generalize φ = φ'
        revert φ'
        decide
      obtain ⟨p, hp1, hp2, hp3, hp4⟩ := leftPhase_eq_some hφ
      have hev : Even (r - 1 - p) := (ZMod.intCast_eq_zero_iff_even).1 (hφ0 ▸ hp4).symm
      have hodd : Odd (r - p) := by
        obtain ⟨k, hk⟩ := hev
        exact ⟨k, by omega⟩
      have hbet : ∀ m, p < m → m < r → t m = 0 := fun m h1 h2 => hp3 m h1 (by omega)
      refine ⟨p, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hp2, r,
        Finsupp.mem_support_iff.mpr hrt, by omega, hodd, fun m hm => ?_⟩,
        by omega, hbet, hp2, hodd⟩
      by_contra hc
      simp only [not_or, not_le] at hc
      exact (Finsupp.mem_support_iff.mp hm) (hbet m hc.1 hc.2)
    · intro r hr r' hr'
      by_contra hne
      have hrt : t r ≠ 0 := by
        have := hr.1
        simp only [Finset.mem_erase, Finset.mem_filter, Finsupp.mem_support_iff]
          at this
        exact this.2.1
      have hrt' : t r' ≠ 0 := by
        have := hr'.1
        simp only [Finset.mem_erase, Finset.mem_filter, Finsupp.mem_support_iff]
          at this
        exact this.2.1
      rcases lt_or_gt_of_ne hne with h | h
      · exact hrt (hr'.2.2.1 r hr.2.1 h)
      · exact hrt' (hr.2.2.1 r' hr'.2.1 h)
  have := Finset.pred_card_le_card_erase (s := t.support.filter (fun r => IsFront t r ∧ r ≤ b))
    (a := x)
  unfold frontCount
  omega

/-- Moving the fronts of the part up to `B` left through `τ` steps of a spaced state keeps them
distinct fronts of any state agreeing with the orbit up to `B - τ`, below a front beyond. -/
private theorem frontCount_shift {t P u : FiniteConfiguration} {B b : ℤ} {τ : ℕ}
    (hPs : PhaseSpaced P) (hPt : ∀ i, i ≤ B → P i = t i)
    (hu : ∀ i, i ≤ B - τ → u i = ((finRule f26 hq26)^[τ] P) i)
    (hb : IsFront u b) (hbB : B - τ < b) :
    frontCount t B + 1 ≤ frontCount u b := by
  classical
  unfold frontCount
  have hbmem : b ∈ u.support.filter (fun r => IsFront u r ∧ r ≤ b) :=
    Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hb.1, hb, le_rfl⟩
  have hle : (t.support.filter (fun r => IsFront t r ∧ r ≤ B)).card ≤
      ((u.support.filter (fun r => IsFront u r ∧ r ≤ b)).erase b).card := by
    refine Finset.card_le_card_of_injOn (fun r => r - τ) (fun r hr => ?_)
      (fun r _ r' _ h => by simpa using h)
    simp only [Finset.coe_filter, Finsupp.mem_support_iff, Set.mem_ofPred_eq] at hr
    obtain ⟨_, hrf, hrB⟩ := hr
    have h1 : IsFront P r := (isFront_congr (fun i hi => (hPt i (by omega)).symm)).1 hrf
    have h2 : IsFront ((finRule f26 hq26)^[τ] P) (r - τ) :=
      (isFront_iterate_iff hPs τ (r - τ)).2 (by rwa [sub_add_cancel])
    have h3 : IsFront u (r - τ) :=
      (isFront_congr (fun i hi => hu i (by omega))).2 h2
    simp only [Finset.coe_erase, Finset.coe_filter, Finsupp.mem_support_iff, Set.mem_sdiff,
      Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨⟨h3.1, h3, by omega⟩, by omega⟩
  rw [Finset.card_erase_of_mem hbmem] at hle
  have := Finset.card_pos.2 ⟨b, hbmem⟩
  omega

private theorem kinkCount_iterate_le (z : FiniteConfiguration) (n : ℕ) :
    kinkCount ((finRule f26 hq26)^[n] z) ≤ kinkCount z := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (kinkCountMono_f26 _).trans ih

/-- The cell left of the front `B` of a spaced state is set at some time along the orbit, `B`
moving left at one cell a step: between the two fronts `B'` and `B` the cells at odd offset from
`B'` stay clear and the others, apart from the front `B'` itself, follow rule `90`, so none of
them is eventually clear. -/
private theorem exists_diagonal_set {P : FiniteConfiguration} {B B' : ℤ} (hPs : PhaseSpaced P)
    (hB' : IsFront P B') (hlt : B' < B) (hbtw : ∀ y, B' < y → y < B → ¬ IsFront P y)
    (hph : leftPhase P (B - 1) = some 0) :
    ∃ τ : ℕ, ((finRule f26 hq26)^[τ] P) (B - 1 - τ) ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ → FiniteConfiguration, ∀ τ, s τ = (finRule f26 hq26)^[τ] P :=
    ⟨_, fun _ => rfl⟩
  have hs0 : s 0 = P := by rw [hs]; rfl
  have hsucc : ∀ τ, s (τ + 1) = finRule f26 hq26 (s τ) := fun τ => by
    rw [hs, hs, Function.iterate_succ_apply']
  have hfr : ∀ τ y, IsFront (s τ) y ↔ IsFront P (y + τ) := fun τ y => by
    rw [hs]
    exact isFront_iterate_iff hPs τ y
  have hphase : ∀ (τ n : ℕ), (n : ℤ) < B - B' →
      leftPhase (s τ) (B' - τ + n) = some (n : ZMod 2) := by
    intro τ n
    induction n with
    | zero =>
        intro _
        have hf : IsFront (s τ) (B' - τ) := (hfr τ _).2 (by rwa [sub_add_cancel])
        simpa using leftPhase_of_ne hf.1
    | succ n ih =>
        intro hn
        push_cast at hn
        have ih' := ih (by omega)
        rw [Nat.cast_succ, ← add_assoc, leftPhase_succ, ih']
        have hnf : ¬ IsFront (s τ) (B' - τ + n + 1) := fun h =>
          hbtw (B' - τ + n + 1 + τ) (by omega) (by omega) ((hfr τ _).1 h)
        by_cases hb : s τ (B' - τ + n + 1) = 0
        · simp only [nextPhase, hb, ite_true, Option.map_some]
          push_cast
          rfl
        · have h1 : leftPhase (s τ) (B' - τ + n) = some 1 := by
            by_contra hc
            exact hnf ⟨hb, by rwa [add_sub_cancel_right]⟩
          rw [ih'] at h1
          have hn1 : (n : ZMod 2) = 1 := Option.some.inj h1
          simp only [nextPhase, hb, ite_false]
          rw [Nat.cast_succ, hn1]
          decide
  have hodd : Odd (B - B') := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = B - 1 - B' := ⟨(B - 1 - B').toNat, by omega⟩
    have h := hphase 0 n (by omega)
    rw [hs0, show B' - ((0 : ℕ) : ℤ) + n = B - 1 by omega, hph] at h
    have hev : Even n := ZMod.natCast_eq_zero_iff_even.1 (Option.some.inj h).symm
    obtain ⟨k, hk⟩ := hev
    exact ⟨k, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, B - B' = 2 * K + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k.toNat, by omega⟩
  have hclear : ∀ (τ n : ℕ), 0 < n → (n : ℤ) < B - B' → Odd n →
      s τ (B' - τ + n) = 0 := by
    intro τ n _ hn hodd
    by_contra hne
    have h1 := leftPhase_of_ne hne
    rw [hphase τ n hn] at h1
    exact (Nat.not_even_iff_odd.2 hodd)
      (ZMod.natCast_eq_zero_iff_even.1 (Option.some.inj h1))
  have hrec : ∀ (τ k : ℕ), 2 * (k : ℤ) + 1 < B - B' →
      s (τ + 1) (B' - ((τ + 1 : ℕ) : ℤ) + 2 * ((k + 1 : ℕ) : ℤ)) =
        s τ (B' - τ + 2 * k) + s τ (B' - τ + 2 * ((k + 1 : ℕ) : ℤ)) := by
    intro τ k hk
    have hx : s τ (B' - τ + ((2 * k + 1 : ℕ) : ℤ)) = 0 :=
      hclear τ (2 * k + 1) (by omega) (by push_cast; omega) ⟨k, rfl⟩
    have hi : B' - ((τ + 1 : ℕ) : ℤ) + 2 * ((k + 1 : ℕ) : ℤ) =
        B' - τ + ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
    have e1 : B' - (τ : ℤ) + ((2 * k + 1 : ℕ) : ℤ) - 1 = B' - τ + 2 * k := by push_cast; ring
    have e2 : B' - (τ : ℤ) + ((2 * k + 1 : ℕ) : ℤ) + 1 = B' - τ + 2 * ((k + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [hsucc, hi, finRule_apply, hx, e1, e2]
    unfold f26
    ring
  have hfreq : ∀ k : ℕ, 2 * (k : ℤ) < B - B' → ∀ T : ℕ, ∃ τ, T ≤ τ ∧
      s τ (B' - τ + 2 * k) ≠ 0 := by
    intro k
    induction k with
    | zero =>
        intro _ T
        refine ⟨T, le_rfl, ?_⟩
        have hf : IsFront (s T) (B' - T) := (hfr T _).2 (by rwa [sub_add_cancel])
        simpa using hf.1
    | succ k ih =>
        intro hk T
        by_contra hcon
        have hz : ∀ τ, T ≤ τ → s τ (B' - τ + 2 * ((k + 1 : ℕ) : ℤ)) = 0 := fun τ hτ => by
          by_contra h
          exact hcon ⟨τ, hτ, h⟩
        obtain ⟨τ, hτT, hτ⟩ := ih (by push_cast at hk; omega) T
        have := hrec τ k (by push_cast at hk; omega)
        rw [hz (τ + 1) (by omega), hz τ hτT] at this
        exact hτ (by simpa using this.symm)
  obtain ⟨τ, _, hτ⟩ := hfreq K (by omega) 0
  refine ⟨τ, ?_⟩
  rw [← hs]
  have : B - 1 - (τ : ℤ) = B' - τ + 2 * (K : ℤ) := by omega
  rw [this]
  exact hτ

/-- The finite check behind the set cell left of a clear one. -/
private theorem f26_zero_left : ∀ a b c : ZMod 2, a = 0 → c ≠ 0 → f26 a b c ≠ 0 := by
  unfold f26
  decide

/-- The finite check behind the clear right neighbour of a front. -/
private theorem f26_all_ne : ∀ a b c : ZMod 2, a ≠ 0 → b ≠ 0 → c ≠ 0 → f26 a b c = 0 := by
  unfold f26
  decide

/-- **The event.** From a state whose least bad cell is `B`, some step count `τ` gives a spaced
state or a state whose least bad cell `b` follows more fronts than `B` does: the fronts of the
part up to `B` move left at one cell a step, the cell left of the front `B` is set at some time,
and the front's right neighbour is then cleared, so no bad cell remains up to two cells beyond it.
-/
private theorem event_f26 {t : FiniteConfiguration} {B : ℤ} (hB : Bad t B)
    (hmin : ∀ r, r < B → ¬ Bad t r) :
    ∃ τ : ℕ, PhaseSpaced ((finRule f26 hq26)^[τ] t) ∨
      ∃ b, Bad ((finRule f26 hq26)^[τ] t) b ∧
        (∀ r, r < b → ¬ Bad ((finRule f26 hq26)^[τ] t) r) ∧
        frontCount t B + 1 ≤ frontCount ((finRule f26 hq26)^[τ] t) b := by
  classical
  obtain ⟨hBt, hBph, hBr⟩ := hB
  set P : FiniteConfiguration := t.filter (fun i => i ≤ B) with hPdef
  have hPt : ∀ i, i ≤ B → P i = t i := fun i hi => by
    simp [hPdef, hi]
  have hPcone : ∀ i, B < i → P i = 0 := fun i hi => by
    simp [hPdef, not_le.2 hi]
  have hPs : PhaseSpaced P := by
    intro j h1 h2
    have hj : j + 1 ≤ B := by
      by_contra h
      exact h1 (hPcone _ (by omega))
    by_cases hj2 : j + 2 ≤ B
    · rw [hPt _ hj2]
      by_contra h3
      refine hmin (j + 1) (by omega) ⟨?_, ?_, ?_⟩
      · rwa [← hPt _ hj]
      · rw [add_sub_cancel_right, leftPhase_congr (u := P) (fun i hi => (hPt i (by omega)).symm)]
        exact h2
      · rwa [show j + 1 + 1 = j + 2 by ring]
    · exact hPcone _ (by omega)
  have hph : leftPhase P (B - 1) = some 0 := by
    rw [leftPhase_congr (u := t) (fun i hi => hPt i (by omega))]
    exact hBph
  have hBP : IsFront P B := ⟨by rw [hPt B le_rfl]; exact hBt, by rw [hph]; decide⟩
  obtain ⟨p, hp1, hp2, -, -⟩ := leftPhase_eq_some hBph
  obtain ⟨B', hB'f, hB'lt, hB'btw⟩ :=
    exists_prev_front (s := P) (B := B) (p := p) (by omega) (by rw [hPt p (by omega)]; exact hp2)
  have hex := exists_diagonal_set hPs hB'f hB'lt hB'btw hph
  have hfrP : ∀ τ : ℕ, ((finRule f26 hq26)^[τ] P) (B - τ) ≠ 0 := fun τ =>
    ((isFront_iterate_iff hPs τ (B - τ)).2 (by rwa [sub_add_cancel])).1
  have hag := iterate_agree (t := t) (u := P) (B := B) (fun i hi => (hPt i hi).symm)
  obtain ⟨τ₀, hτ₀, hmin₀⟩ : ∃ τ₀ : ℕ, ((finRule f26 hq26)^[τ₀] P) (B - 1 - τ₀) ≠ 0 ∧
      ∀ τ < τ₀, ((finRule f26 hq26)^[τ] P) (B - 1 - τ) = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun τ hτ => by
      by_contra h
      exact Nat.find_min hex hτ h⟩
  have hset : ∀ τ : ℕ, τ ≤ τ₀ → ((finRule f26 hq26)^[τ] t) (B + 1 - τ) ≠ 0 := by
    intro τ
    induction τ with
    | zero =>
        intro _
        simpa using hBr
    | succ τ ih =>
        intro hle
        have h1 := ih (by omega)
        have h3 : ((finRule f26 hq26)^[τ] t) (B - τ - 1) = 0 := by
          rw [hag τ _ (by omega), show B - (τ : ℤ) - 1 = B - 1 - τ by ring]
          exact hmin₀ τ (by omega)
        rw [Function.iterate_succ_apply', finRule_apply,
          show B + 1 - ((τ + 1 : ℕ) : ℤ) = B - τ by push_cast; ring,
          show B - (τ : ℤ) + 1 = B + 1 - τ by ring]
        exact f26_zero_left _ _ _ h3 h1
  -- the state after the clearing step
  set t₁ : FiniteConfiguration := (finRule f26 hq26)^[τ₀ + 1] t with ht₁
  have ht₁ag : ∀ i, i ≤ B - ((τ₀ + 1 : ℕ) : ℤ) → t₁ i = ((finRule f26 hq26)^[τ₀ + 1] P) i :=
    fun i hi => hag (τ₀ + 1) i hi
  have hz : t₁ (B - ((τ₀ + 1 : ℕ) : ℤ) + 1) = 0 := by
    rw [ht₁, Function.iterate_succ_apply', finRule_apply,
      show B - ((τ₀ + 1 : ℕ) : ℤ) + 1 = B - τ₀ by push_cast; ring,
      show B - (τ₀ : ℤ) - 1 = B - 1 - τ₀ by ring, show B - (τ₀ : ℤ) + 1 = B + 1 - τ₀ by ring,
      hag τ₀ (B - 1 - τ₀) (by omega), hag τ₀ (B - τ₀) le_rfl]
    exact f26_all_ne _ _ _ hτ₀ (hfrP τ₀) (by simpa using hset τ₀ le_rfl)
  have hB₁ : t₁ (B - ((τ₀ + 1 : ℕ) : ℤ)) ≠ 0 := by
    rw [ht₁ag _ le_rfl]
    exact hfrP (τ₀ + 1)
  have hnobad : ∀ r, r ≤ B - ((τ₀ + 1 : ℕ) : ℤ) + 2 → ¬ Bad t₁ r := by
    intro r hr hbad
    obtain ⟨h1, h2, h3⟩ := hbad
    rcases (show r + 1 ≤ B - ((τ₀ + 1 : ℕ) : ℤ) ∨ r = B - ((τ₀ + 1 : ℕ) : ℤ) ∨
        r = B - ((τ₀ + 1 : ℕ) : ℤ) + 1 ∨ r = B - ((τ₀ + 1 : ℕ) : ℤ) + 2 by omega) with
      h | h | h | h
    · refine not_bad_of_phaseSpaced (phaseSpaced_iterate hPs (τ₀ + 1)) r ⟨?_, ?_, ?_⟩
      · rwa [← ht₁ag r (by omega)]
      · rwa [← leftPhase_congr (t := t₁) (fun i hi => ht₁ag i (by omega))]
      · rwa [← ht₁ag (r + 1) h]
    · rw [h] at h3
      exact h3 hz
    · rw [h] at h1
      exact h1 hz
    · have e := leftPhase_succ t₁ (B - ((τ₀ + 1 : ℕ) : ℤ))
      rw [hz, leftPhase_of_ne hB₁] at e
      rw [h, show B - ((τ₀ + 1 : ℕ) : ℤ) + 2 - 1 = B - ((τ₀ + 1 : ℕ) : ℤ) + 1 by ring, e] at h2
      revert h2
      simp [nextPhase]
  refine ⟨τ₀ + 1, ?_⟩
  by_cases hsp : PhaseSpaced t₁
  · exact Or.inl hsp
  · right
    obtain ⟨b, hb, hbmin⟩ := exists_least_bad (t := t₁) (by
      by_contra h
      exact hsp (phaseSpaced_of_noBad (fun r hr => h ⟨r, hr⟩)))
    have hbgt : B - ((τ₀ + 1 : ℕ) : ℤ) + 2 < b := by
      by_contra h
      exact hnobad b (by omega) hb
    exact ⟨b, hb, hbmin, frontCount_shift hPs hPt ht₁ag hb.isFront (by omega)⟩

/-- The induction on the room left between the kink count and the number of fronts: from a state
whose least bad cell is `B`, some iterate is spaced. -/
private theorem exists_phaseSpaced_aux : ∀ (m : ℕ) (z : FiniteConfiguration) (B : ℤ), Bad z B →
    (∀ r, r < B → ¬ Bad z r) → kinkCount z + 1 ≤ frontCount z B + m →
      ∃ n : ℕ, PhaseSpaced ((finRule f26 hq26)^[n] z) := by
  intro m
  induction m with
  | zero =>
      intro z B hB hmin hm
      obtain ⟨τ, h | ⟨b, hb, hbmin, hcnt⟩⟩ := event_f26 hB hmin
      · exact ⟨τ, h⟩
      · exfalso
        have h1 := kinkCount_iterate_le z τ
        have h2 := frontCount_le_kinkCount ((finRule f26 hq26)^[τ] z) b
        omega
  | succ m ih =>
      intro z B hB hmin hm
      obtain ⟨τ, h | ⟨b, hb, hbmin, hcnt⟩⟩ := event_f26 hB hmin
      · exact ⟨τ, h⟩
      · have h1 := kinkCount_iterate_le z τ
        obtain ⟨n, hn⟩ := ih _ b hb hbmin (by omega)
        refine ⟨n + τ, ?_⟩
        rwa [Function.iterate_add_apply]

/-- **Every finite configuration reaches a spaced state at rule `26`.** A configuration that is
not spaced has a least bad cell, and from it the orbit reaches a spaced state or a state whose
least bad cell follows more fronts than before; the number of fronts is bounded by the kink count
plus one, which does not increase, so the second case occurs finitely often. -/
theorem reachesSpaced_f26 : LocalRule.ReachesSpaced f26 hq26 := by
  intro z
  by_cases hz : PhaseSpaced z
  · exact ⟨0, spaced_of_phaseSpaced hz⟩
  · obtain ⟨B, hB, hmin⟩ := exists_least_bad (t := z) (by
      by_contra h
      exact hz (phaseSpaced_of_noBad (fun r hr => h ⟨r, hr⟩)))
    obtain ⟨n, hn⟩ := exists_phaseSpaced_aux (kinkCount z + 1) z B hB hmin (by omega)
    exact ⟨n, spaced_of_phaseSpaced hn⟩

/-- **Rules `26` and `82` conserve no sliding block code but zero**, with no hypothesis: every
finite configuration reaches a spaced state at rule `26` (`reachesSpaced_f26`), and the
conditional theorem `conservesNoCode_f26_f82_of_reachesSpaced` takes that as its one condition. -/
theorem conservesNoCode_f26_f82 :
    LocalRule.ConservesNoCode f26 hq26 ∧ LocalRule.ConservesNoCode f82 hq82 :=
  conservesNoCode_f26_f82_of_reachesSpaced reachesSpaced_f26

/-- **Rule `26` clears windows**, with no hypothesis: the held suffix of one parity at rule `26`
composes from `reachesSpaced_f26` and `spacedHeld_f26`. -/
theorem clearsWindows_f26 : LocalRule.ClearsWindows f26 hq26 :=
  clearsWindows_f26_of_eventuallyOneParitySuffix
    (reachesSpaced_f26.eventuallyOneParitySuffix spacedHeld_f26)

/-- **Rule `82` clears windows**, with no hypothesis: the same held suffix at rule `26`, with
clearing passed to rule `82` by reflecting the line. -/
theorem clearsWindows_f82 : LocalRule.ClearsWindows f82 hq82 :=
  clearsWindows_f82_of_eventuallyOneParitySuffix
    (reachesSpaced_f26.eventuallyOneParitySuffix spacedHeld_f26)

/-- info:
'ECA.LocalRule.ReachesSpaced.eventuallyOneParitySuffix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ReachesSpaced.eventuallyOneParitySuffix

/-- info:
'ECA.LocalRule.ReachesSpaced.eventuallyOneParitySuffix_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ReachesSpaced.eventuallyOneParitySuffix_nonvacuous

/-- info:
'ECA.conservesNoCode_f26_f82_of_spaced' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f26_f82_of_spaced

/-- info:
'ECA.spacedHeld_f26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.spacedHeld_f26

/-- info:
'ECA.conservesNoCode_f26_f82_of_reachesSpaced' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f26_f82_of_reachesSpaced

/-- info:
'ECA.reachesSpaced_f26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reachesSpaced_f26

/-- info:
'ECA.conservesNoCode_f26_f82' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f26_f82

/-- info:
'ECA.clearsWindows_f26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.clearsWindows_f26

/-- info:
'ECA.clearsWindows_f82' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.clearsWindows_f82

end ECA
