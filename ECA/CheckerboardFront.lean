module

public import ECA.ForcingTables
import all ECA.ForcingTables

/-!
# A checkerboard that invades any window: tables `114` and `58` conserve no code but zero

A table forcing a `1` from one end overwrites a window at speed one, which is why it conserves no
sliding block code but zero (`ECA/ForcingTables.lean`). The argument needs only a pattern that
overwrites any window at a positive speed with a phase two states share. A quiescent table has a
**checkerboard front from the left** when six cells of checkerboard at either phase, followed by
any four cells, give after three steps four cells of the checkerboard at the same phase: the front
moves right by one cell in three steps whatever stood ahead of it. A table has a **checkerboard
front from the right** when the same holds for any four cells followed by six of checkerboard.
Table `114` has the front from the left and table `58`, its mirror, the front from the right.

A block of `4 L + 6` checkerboard cells beside a window of `L` cells then reaches the window in `L`
rounds of three steps, whatever the window held and with the phase the block alone decides, so a
state holding a window and a state holding zeros there read the same window after `3 L` steps. A
sliding block code that a step conserves reads the same value on both, which is its value on the
zero window, zero.

* `LocalRule.windowStep` — one step on a window of `n + 2` cells, read on the middle `n`.
* `LocalRule.CheckerboardFrontLeft` and `LocalRule.CheckerboardFrontRight` — the two fronts, a
  finite identity over the ten cells three steps read.
* `LocalRule.blockCode_eq_zero_of_checkerboardFrontLeft` and
  `LocalRule.blockCode_eq_zero_of_checkerboardFrontRight` — at a quiescent table with a front
  from the left (right), a sliding block code of any window conserved by a step is the zero code.
* `LocalRule.blockCode_eq_zero_of_checkerboardFrontLeft_nonvacuous` — the hypotheses of the
  statement from the left hold together, at table `114` with window `1` and the zero local rule.
* `blockCode_checkerboard_load_bearing` — table `50`, which has neither front, conserves a code
  that is not zero.
* `blockCode_eq_zero_f114` and `blockCode_eq_zero_f58` — tables `114` and `58` conserve no sliding
  block code of any window but zero.
-/

@[expose] public section

namespace ECA

namespace LocalRule

/-- One step on a window of `n + 2` cells, read on the middle `n` cells: the cell `k` of the image
is the local rule on the window's cells `k`, `k + 1` and `k + 2`. -/
def windowStep (f : LocalRule) {n : ℕ} (u : Fin (n + 2) → ZMod 2) : Fin n → ZMod 2 :=
  fun k => f (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩) (u ⟨k + 2, by omega⟩)

/-- **A checkerboard front from the left**: six cells of checkerboard at either phase followed by
any four cells give, after three steps, four cells of checkerboard at that phase. The cells `j - 6`
to `j + 3` step to the cells `j - 3` to `j`, so the front moves right by one cell in three steps
whatever stood ahead of it. -/
def CheckerboardFrontLeft (f : LocalRule) : Prop :=
  ∀ (p : ZMod 2) (u : Fin 10 → ZMod 2), (∀ k : Fin 6, u ⟨k, by omega⟩ = (k : ZMod 2) + p) →
    ∀ m : Fin 4, f.windowStep (f.windowStep (f.windowStep u)) m = (m : ZMod 2) + p

/-- **A checkerboard front from the right**: any four cells followed by six cells of checkerboard
at either phase give, after three steps, four cells of checkerboard at that phase; the mirror of
`CheckerboardFrontLeft`. -/
def CheckerboardFrontRight (f : LocalRule) : Prop :=
  ∀ (p : ZMod 2) (u : Fin 10 → ZMod 2),
    (∀ k : Fin 6, u ⟨k + 4, by omega⟩ = ((k + 4 : ℕ) : ZMod 2) + p) →
    ∀ m : Fin 4, f.windowStep (f.windowStep (f.windowStep u)) m = (m : ZMod 2) + p

/-- A step of the finite-configuration map is a step on the windows: the window of `n + 2` cells
from `a` steps to the window of `n` cells from `a + 1`. -/
private theorem windowStep_finRule (f : LocalRule) (hq : f 0 0 0 = 0) (x : FiniteConfiguration)
    (a : ℤ) (n : ℕ) :
    f.windowStep (fun k : Fin (n + 2) => x (a + (k : ℕ))) =
      fun k : Fin n => finRule f hq x (a + 1 + (k : ℕ)) := by
  funext k
  rw [finRule_apply]
  simp only [windowStep]
  have h1 : a + 1 + (k : ℕ) - 1 = a + ((k : ℕ) : ℕ) := by omega
  have h2 : a + 1 + (k : ℕ) = a + (((k : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
  have h3 : a + 1 + (k : ℕ) + 1 = a + (((k : ℕ) + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [h1, h3, h2]

/-- Three steps of the finite-configuration map are three steps on the windows: the window of ten
cells from `a` goes to the four cells from `a + 3`. -/
private theorem windowStep_iterate_three (f : LocalRule) (hq : f 0 0 0 = 0)
    (x : FiniteConfiguration) (a : ℤ) :
    f.windowStep (f.windowStep (f.windowStep (fun k : Fin 10 => x (a + (k : ℕ))))) =
      fun m : Fin 4 => (finRule f hq)^[3] x (a + 3 + (m : ℕ)) := by
  have h1 := windowStep_finRule f hq x a 8
  have h2 := windowStep_finRule f hq (finRule f hq x) (a + 1) 6
  have h3 := windowStep_finRule f hq (finRule f hq (finRule f hq x)) (a + 1 + 1) 4
  funext m
  have e1 : f.windowStep (fun k : Fin 10 => x (a + (k : ℕ))) =
      fun k : Fin 8 => finRule f hq x (a + 1 + (k : ℕ)) := h1
  have e2 : f.windowStep (fun k : Fin 8 => finRule f hq x (a + 1 + (k : ℕ))) =
      fun k : Fin 6 => finRule f hq (finRule f hq x) (a + 1 + 1 + (k : ℕ)) := h2
  have e3 : f.windowStep (fun k : Fin 6 => finRule f hq (finRule f hq x) (a + 1 + 1 + (k : ℕ))) =
      fun k : Fin 4 => finRule f hq (finRule f hq (finRule f hq x)) (a + 1 + 1 + 1 + (k : ℕ)) :=
    h3
  rw [e1, e2, e3]
  have e : a + 1 + 1 + 1 + (m : ℕ) = a + 3 + (m : ℕ) := by ring
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, e]

/-- **The front at a cell, from the left**: where the cells `i - 3 - m` to `i + 2 - m` of a finite
configuration read the checkerboard at phase `τ`, three steps give the cell `i` the checkerboard at
phase `τ + 3`, whatever the three cells to their right held. -/
private theorem iterate_three_of_left (f : LocalRule) (hq : f 0 0 0 = 0)
    (hfront : f.CheckerboardFrontLeft) (x : FiniteConfiguration) (τ : ZMod 2) (i : ℤ) (m : ℕ)
    (hm : m < 4)
    (h : ∀ c : ℤ, i - 3 - m ≤ c → c < i + 3 - m → x c = (c : ZMod 2) + τ) :
    (finRule f hq)^[3] x i = (i : ZMod 2) + (τ + 3) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hw := windowStep_iterate_three f hq x (i + 3 - m - 6)
  have hfr := hfront (((i + 3 - m : ℤ) : ZMod 2) + τ)
    (fun k : Fin 10 => x (i + 3 - m - 6 + (k : ℕ))) (fun k => ?_) ⟨m, hm⟩
  · rw [hw] at hfr
    have e : i + 3 - (m : ℤ) - 6 + 3 + ((⟨m, hm⟩ : Fin 4) : ℕ) = i := by
      simp only; ring
    simp only [e] at hfr
    rw [hfr]
    push_cast
    ring
  · have hk := k.2
    rw [h (i + 3 - m - 6 + (k : ℕ)) (by omega) (by omega)]
    push_cast
    linear_combination (-3 : ZMod 2) * h2

/-- **The front at a cell, from the right**: where the cells `i + 1 - m` to `i + 6 - m` of a finite
configuration read the checkerboard at phase `τ`, three steps give the cell `i` the checkerboard
at phase `τ + 3`, whatever the three cells to their left held. -/
private theorem iterate_three_of_right (f : LocalRule) (hq : f 0 0 0 = 0)
    (hfront : f.CheckerboardFrontRight) (x : FiniteConfiguration) (τ : ZMod 2) (i : ℤ) (m : ℕ)
    (hm : m < 4)
    (h : ∀ c : ℤ, i + 1 - m ≤ c → c < i + 7 - m → x c = (c : ZMod 2) + τ) :
    (finRule f hq)^[3] x i = (i : ZMod 2) + (τ + 3) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hw := windowStep_iterate_three f hq x (i - 3 - m)
  have hfr := hfront (((i - 3 - m : ℤ) : ZMod 2) + τ)
    (fun k : Fin 10 => x (i - 3 - m + (k : ℕ))) (fun k => ?_) ⟨m, hm⟩
  · rw [hw] at hfr
    have e : i - 3 - (m : ℤ) + 3 + ((⟨m, hm⟩ : Fin 4) : ℕ) = i := by
      simp only; ring
    simp only [e] at hfr
    rw [hfr]
    push_cast
    linear_combination (-3 : ZMod 2) * h2
  · have hk := k.2
    rw [h (i - 3 - m + ((k + 4 : ℕ) : ℤ)) (by push_cast; omega) (by push_cast; omega)]
    push_cast
    ring

/-- **The block, from the left**: if the cells `3 n - a` to `-1` of a finite configuration read the
checkerboard at phase zero, and the block is long enough (`2 n + 6 ≤ a`), then after `3 n` steps
the cells `3 n - a` to `n - 1` read it at phase `3 n`. -/
private theorem iterate_three_mul_of_left (f : LocalRule) (hq : f 0 0 0 = 0)
    (hfront : f.CheckerboardFrontLeft) (s : FiniteConfiguration) (a : ℕ)
    (h0 : ∀ c : ℤ, -(a : ℤ) ≤ c → c < 0 → s c = (c : ZMod 2)) (n : ℕ) (hn : 2 * n + 6 ≤ a) :
    ∀ c : ℤ, -(a : ℤ) + 3 * n ≤ c → c < n →
      (finRule f hq)^[3 * n] s c = (c : ZMod 2) + ((3 * n : ℕ) : ZMod 2) := by
  induction n with
  | zero =>
    intro c hc1 hc2
    simpa using h0 c (by simpa using hc1) (by simpa using hc2)
  | succ n ih =>
    intro i hi1 hi2
    have ih' := ih (by omega)
    have e : 3 * (n + 1) = 3 + 3 * n := by ring
    rw [e, Function.iterate_add_apply]
    rw [iterate_three_of_left f hq hfront ((finRule f hq)^[3 * n] s) ((3 * n : ℕ) : ZMod 2) i
      (i + 3 - n).toNat (by omega) (fun c hc1 hc2 => ih' c (by omega) (by omega))]
    push_cast
    ring

/-- **The block, from the right**: if the cells `l` to `l + a - 1` of a finite configuration read
the checkerboard at phase zero, and the block is long enough (`2 n + 6 ≤ a`), then after `3 n`
steps the cells `l - n` to `l + a - 3 n - 1` read it at phase `3 n`. -/
private theorem iterate_three_mul_of_right (f : LocalRule) (hq : f 0 0 0 = 0)
    (hfront : f.CheckerboardFrontRight) (s : FiniteConfiguration) (l : ℤ) (a : ℕ)
    (h0 : ∀ c : ℤ, l ≤ c → c < l + a → s c = (c : ZMod 2)) (n : ℕ) (hn : 2 * n + 6 ≤ a) :
    ∀ c : ℤ, l - n ≤ c → c < l + a - 3 * n →
      (finRule f hq)^[3 * n] s c = (c : ZMod 2) + ((3 * n : ℕ) : ZMod 2) := by
  induction n with
  | zero =>
    intro c hc1 hc2
    simpa using h0 c (by simpa using hc1) (by simpa using hc2)
  | succ n ih =>
    intro i hi1 hi2
    have ih' := ih (by omega)
    have e : 3 * (n + 1) = 3 + 3 * n := by ring
    rw [e, Function.iterate_add_apply]
    rw [iterate_three_of_right f hq hfront ((finRule f hq)^[3 * n] s) ((3 * n : ℕ) : ZMod 2) i
      (i + 7 - (l + a - 3 * n)).toNat (by omega) (fun c hc1 hc2 => ih' c (by omega) (by omega))]
    push_cast
    ring

/-- The finite configuration with the window `w` on the cells `0` to `L - 1`, the checkerboard
`c ↦ c` on the `a` cells before it, and zeros elsewhere. -/
private noncomputable def leftState (a L : ℕ) (w : Fin L → ZMod 2) : FiniteConfiguration :=
  Finsupp.onFinset (Finset.Icc (-(a : ℤ)) L)
    (fun i => if h : 0 ≤ i ∧ i < L then w ⟨i.toNat, by omega⟩
      else if -(a : ℤ) ≤ i ∧ i < 0 then (i : ZMod 2) else 0) (by
      intro i hi
      by_contra hcon
      apply hi
      rw [Finset.mem_Icc] at hcon
      have h1 : ¬ (0 ≤ i ∧ i < L) := by omega
      have h2 : ¬ (-(a : ℤ) ≤ i ∧ i < 0) := by omega
      simp [h1, h2])

private theorem leftState_window (a L : ℕ) (w : Fin L → ZMod 2) (k : Fin L) :
    leftState a L w (0 + (k : ℕ)) = w k := by
  have h : 0 ≤ (0 : ℤ) + (k : ℕ) ∧ (0 : ℤ) + (k : ℕ) < L := by
    have := k.2
    omega
  simp only [leftState, Finsupp.onFinset_apply]
  rw [dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  ext
  simp

private theorem leftState_block (a L : ℕ) (w : Fin L → ZMod 2) (c : ℤ) (h1 : -(a : ℤ) ≤ c)
    (h2 : c < 0) : leftState a L w c = (c : ZMod 2) := by
  have h3 : ¬ (0 ≤ c ∧ c < L) := by omega
  simp [leftState, Finsupp.onFinset_apply, h3, h1, h2]

/-- The finite configuration with the window `w` on the cells `0` to `L - 1`, the checkerboard
`c ↦ c` on the `a` cells from `L` on, and zeros elsewhere. -/
private noncomputable def rightState (a L : ℕ) (w : Fin L → ZMod 2) : FiniteConfiguration :=
  Finsupp.onFinset (Finset.Icc 0 ((L : ℤ) + a))
    (fun i => if h : 0 ≤ i ∧ i < L then w ⟨i.toNat, by omega⟩
      else if (L : ℤ) ≤ i ∧ i < L + a then (i : ZMod 2) else 0) (by
      intro i hi
      by_contra hcon
      apply hi
      rw [Finset.mem_Icc] at hcon
      have h1 : ¬ (0 ≤ i ∧ i < L) := by omega
      have h2 : ¬ ((L : ℤ) ≤ i ∧ i < L + a) := by omega
      simp [h1, h2])

private theorem rightState_window (a L : ℕ) (w : Fin L → ZMod 2) (k : Fin L) :
    rightState a L w (0 + (k : ℕ)) = w k := by
  have h : 0 ≤ (0 : ℤ) + (k : ℕ) ∧ (0 : ℤ) + (k : ℕ) < L := by
    have := k.2
    omega
  simp only [rightState, Finsupp.onFinset_apply]
  rw [dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  ext
  simp

private theorem rightState_block (a L : ℕ) (w : Fin L → ZMod 2) (c : ℤ) (h1 : (L : ℤ) ≤ c)
    (h2 : c < L + a) : rightState a L w c = (c : ZMod 2) := by
  have h3 : ¬ (0 ≤ c ∧ c < L) := by omega
  simp [rightState, Finsupp.onFinset_apply, h3, h1, h2]

/-- **The comparison**: two finite configurations that read the same `L` cells after `t` steps
have the same sliding block code value there, whatever they read before, once a step conserves
the code; so a code value at the window `w` is the code value at the common window. -/
private theorem blockCode_apply_eq_of_iterate (f : LocalRule) (hq : f 0 0 0 = 0) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s)
    (t : ℕ) (s : FiniteConfiguration) :
    g (fun k : Fin L => (finRule f hq)^[t] s (0 + (k : ℕ))) =
      g (fun k : Fin L => s (0 + (k : ℕ))) := by
  have h0 := blockCode_iterate_finRule f hq g hg hcons t s
  have h1 := congrArg (fun y : FiniteConfiguration => y 0) h0
  simpa only [FiniteConfiguration.blockCode_apply] using h1

/-- **A checkerboard front from the left conserves no sliding block code but zero.** If the
quiescent table `f` has a checkerboard front from the left, and a step of `f` leaves the sliding
block code of window `L` with local rule `g` unchanged at every finite configuration, then `g` is
zero at every window: a block of `4 L + 6` checkerboard cells before a window reaches it in `3 L`
steps, so the code reads the window and the zero window as the same window after those steps. -/
theorem blockCode_eq_zero_of_checkerboardFrontLeft (f : LocalRule) (hq : f 0 0 0 = 0)
    (hfront : f.CheckerboardFrontLeft) {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 := by
  have hwin : ∀ w : Fin L → ZMod 2,
      (fun k : Fin L => (finRule f hq)^[3 * L] (leftState (4 * L + 6) L w) (0 + (k : ℕ))) =
        fun k : Fin L => (((0 : ℤ) + (k : ℕ) : ℤ) : ZMod 2) + ((3 * L : ℕ) : ZMod 2) := by
    intro w
    funext k
    have hk := k.2
    exact iterate_three_mul_of_left f hq hfront (leftState (4 * L + 6) L w) (4 * L + 6)
      (fun c h1 h2 => leftState_block _ L w c h1 h2) L (by omega) _ (by push_cast; omega)
      (by omega)
  funext w
  have h1 := blockCode_apply_eq_of_iterate f hq g hg hcons (3 * L) (leftState (4 * L + 6) L w)
  have h2 := blockCode_apply_eq_of_iterate f hq g hg hcons (3 * L) (leftState (4 * L + 6) L 0)
  rw [hwin w] at h1
  rw [hwin 0] at h2
  have e1 : (fun k : Fin L => leftState (4 * L + 6) L w (0 + (k : ℕ))) = w :=
    funext fun k => leftState_window _ L w k
  have e2 : (fun k : Fin L => leftState (4 * L + 6) L 0 (0 + (k : ℕ))) = 0 :=
    funext fun k => leftState_window _ L 0 k
  rw [e1] at h1
  rw [e2, hg] at h2
  rw [← h1, h2]
  rfl

/-- **A checkerboard front from the right conserves no sliding block code but zero**: the mirror
of `blockCode_eq_zero_of_checkerboardFrontLeft`, the block of `4 L + 6` checkerboard cells standing
after the window and moving left. -/
theorem blockCode_eq_zero_of_checkerboardFrontRight (f : LocalRule) (hq : f 0 0 0 = 0)
    (hfront : f.CheckerboardFrontRight) {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 := by
  have hwin : ∀ w : Fin L → ZMod 2,
      (fun k : Fin L => (finRule f hq)^[3 * L] (rightState (4 * L + 6) L w) (0 + (k : ℕ))) =
        fun k : Fin L => (((0 : ℤ) + (k : ℕ) : ℤ) : ZMod 2) + ((3 * L : ℕ) : ZMod 2) := by
    intro w
    funext k
    have hk := k.2
    exact iterate_three_mul_of_right f hq hfront (rightState (4 * L + 6) L w) L (4 * L + 6)
      (fun c h1 h2 => rightState_block _ L w c h1 h2) L (by omega) _ (by omega)
      (by push_cast; omega)
  funext w
  have h1 := blockCode_apply_eq_of_iterate f hq g hg hcons (3 * L) (rightState (4 * L + 6) L w)
  have h2 := blockCode_apply_eq_of_iterate f hq g hg hcons (3 * L) (rightState (4 * L + 6) L 0)
  rw [hwin w] at h1
  rw [hwin 0] at h2
  have e1 : (fun k : Fin L => rightState (4 * L + 6) L w (0 + (k : ℕ))) = w :=
    funext fun k => rightState_window _ L w k
  have e2 : (fun k : Fin L => rightState (4 * L + 6) L 0 (0 + (k : ℕ))) = 0 :=
    funext fun k => rightState_window _ L 0 k
  rw [e1] at h1
  rw [e2, hg] at h2
  rw [← h1, h2]
  rfl

end LocalRule

/-- Rule `114`. -/
def f114 : LocalRule := wolframRule 114

/-- Rule `114` is quiescent. -/
theorem hq114 : f114 0 0 0 = 0 := by decide

/-- Rule `58`. -/
def f58 : LocalRule := wolframRule 58

/-- Rule `58` is quiescent. -/
theorem hq58 : f58 0 0 0 = 0 := by decide

/-- **Table `114` has a checkerboard front from the left**: six cells of checkerboard at either
phase followed by any four cells give four cells of checkerboard after three steps. -/
theorem checkerboardFrontLeft_f114 : f114.CheckerboardFrontLeft := by
  unfold LocalRule.CheckerboardFrontLeft
  decide +kernel

/-- **Table `58` has a checkerboard front from the right**: any four cells followed by six cells of
checkerboard at either phase give four cells of checkerboard after three steps. -/
theorem checkerboardFrontRight_f58 : f58.CheckerboardFrontRight := by
  unfold LocalRule.CheckerboardFrontRight
  decide +kernel

/-- **Table `114` conserves no sliding block code but zero**: it has a checkerboard front from the
left, so a code of any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f114 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f114 hq114 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_checkerboardFrontLeft f114 hq114 checkerboardFrontLeft_f114 g hg
    hcons

/-- **Table `58` conserves no sliding block code but zero**: it has a checkerboard front from the
right, so a code of any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f58 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f58 hq58 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_checkerboardFrontRight f58 hq58 checkerboardFrontRight_f58 g hg
    hcons

/-- **The left-front statement's hypotheses are jointly satisfiable**, at table `114` with window
`1` and the zero local rule: the table is quiescent and has a checkerboard front from the left, the
local rule sends the zero window to zero, and a step conserves its code. The conclusion forces the
code to be zero, so this shows only that the front and the conservation hypotheses are
consistent. -/
theorem LocalRule.blockCode_eq_zero_of_checkerboardFrontLeft_nonvacuous :
    f114 0 0 0 = 0 ∧ f114.CheckerboardFrontLeft ∧ (0 : (Fin 1 → ZMod 2) → ZMod 2) 0 = 0 ∧
      ∀ s : FiniteConfiguration,
        FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _)
            (LocalRule.finRule f114 hq114 s) =
          FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _) s := by
  refine ⟨hq114, checkerboardFrontLeft_f114, Pi.zero_apply _, fun s => ?_⟩
  ext i
  rw [FiniteConfiguration.blockCode_apply, FiniteConfiguration.blockCode_apply]
  rfl

/-- **Table `50` has neither checkerboard front and conserves a code that is not zero**: the
code of the patterns `100110` and `011001` it conserves (`blockCode_finRule_f50`) reads `1` at the
window `100110`. -/
theorem blockCode_checkerboard_load_bearing :
    ¬ f50.CheckerboardFrontLeft ∧ ¬ f50.CheckerboardFrontRight ∧ codeF50 ≠ 0 := by
  refine ⟨?_, ?_, blockCode_forcing_load_bearing.2.2⟩
  · unfold LocalRule.CheckerboardFrontLeft
    decide +kernel
  · unfold LocalRule.CheckerboardFrontRight
    decide +kernel

end ECA
