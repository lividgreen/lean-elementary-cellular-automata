module

public import ECA.EdgeWindow
public import ECA.Growth
import all ECA.EdgeWindow

/-!
# Rules `30` and `86` reproduce no pattern
([RuleSpace] §5)

At a quiescent rule with `f 0 0 1 = 1` the window read from the leftmost set cell of a nonzero
finite state obeys a recurrence in which cell `j` of the image depends on cells `j - 2`, `j - 1`
and `j` of the state. Write column `j` for the sequence of values of cell `j` along an orbit. If
such a rule reproduces a pattern `p`, the window of width `diam p + G` of the orbit of `p` is purely
periodic in time at every gap `G`; reading the period at gap `2` for the columns below `diam p + 2`
and the period at gap `2 * Q + 3` for the whole window of width `diam p + 2 * Q + 3`, a family of
purely periodic columns obeying the recurrence, with its first cell set and its cells from
`diam p` on clear, is at most `diam p + 2 * Q + 2` cells wide at a rule that also sends `0 1 1` and
`1 0 0` to `1` and ignores its last cell on a middle cell set. No such family is as wide as the
window, so rule `30` reproduces no pattern, unconditionally, and so does every quiescent rule with
those four bits; rule `86`, the mirror of rule `30`, reproduces none either, since reflection
carries reproduction to the mirror rule.

## Main results

* `LeftWindowPeriodic` / `PeriodicColumnsNarrow` / `ReproducesReflect` — the three statements the
  sink consumes, as propositions: windows of a reproduced pattern are purely periodic, a family of
  purely periodic columns is narrow, and reflection carries reproduction to the mirror rule.
* `leftWindowPeriodic` — windows of a reproduced pattern are purely periodic, the first of those
  statements; `leftWindowPeriodic_nonvacuous` — its hypotheses meet at rule `90`.
* `not_reproduces_of_columns` — a quiescent rule with `f 0 0 1 = 1`, `f 0 1 1 = 1`,
  `f 1 0 0 = 1` and `f a 1 0 = f a 1 1` for both values of `a` reproduces no pattern, from the
  first two statements as hypotheses.
* `periodicColumnsNarrow` / `periodicColumnsNarrow_nonvacuous` — a family of purely periodic
  columns is narrow, the second of those statements; its hypotheses meet at rule `30`.
* `not_reproduces_of_bits` / `not_reproduces_wolfram30` — a quiescent rule with those four bits
  reproduces no pattern, and rule `30` reproduces none, with no hypothesis beyond the rule's bits.
* `not_reproduces_wolfram30_of_columns` / `not_reproduces_wolfram86_of_columns` — rules `30` and
  `86` reproduce no pattern from the statements as hypotheses, the latter with reflection.
* `reproducesReflect` / `reproducesReflect_nonvacuous` — reflection carries reproduction to the
  mirror rule, the third of those statements; its hypotheses meet at rule `60`.
* `not_reproduces_wolfram86` — rule `86` reproduces no pattern, with no hypothesis beyond the
  rule's bits.
* `not_reproduces_of_columns_nonvacuous` — the five hypotheses on the rule meet at rule `30`.
* `exists_reproduces_wolfram60` / `exists_reproduces_wolfram18` / `exists_reproduces_wolfram26` /
  `exists_reproduces_wolfram126` — each of the four rule-bit hypotheses is needed by any argument
  from the four bits alone: at each rule one fails and the others hold, and the rule reproduces a
  pattern.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The three statements the sink consumes -/

/-- **Windows of a reproduced pattern are purely periodic**: at a quiescent rule with
`f 0 0 1 = 1` that reproduces `p`, at every gap `G` the window of width `diam p + G` of the
iterates of `p` repeats with some period `t ≥ 1` from time `0`. -/
def LeftWindowPeriodic : Prop :=
  ∀ (f : LocalRule) (hq : f 0 0 0 = 0), f 0 0 1 = 1 → ∀ p : FiniteConfiguration,
    Reproduces (finRule f hq) p → ∀ G : ℕ, ∃ t, 0 < t ∧ ∀ n : ℕ,
      ((finRule f hq)^[n + t] p).leftWindow (p.diam + G) =
        ((finRule f hq)^[n] p).leftWindow (p.diam + G)

/-- **A family of purely periodic columns is narrow**: at a rule with `f 0 0 0 = 0`,
`f 0 0 1 = 1`, `f 0 1 1 = 1`, `f 1 0 0 = 1` and `f a 1 0 = f a 1 1`, a family `e n j` obeying the
window recurrence below the width `W`, with `e 0 0 = 1`, clear cells from `d` on at time `0`,
columns below `d + 2` of period `Q` and every column of period `t`, has width
`W < d + 2 * Q + 3`. -/
def PeriodicColumnsNarrow : Prop :=
  ∀ f : LocalRule, f 0 0 0 = 0 → f 0 0 1 = 1 → f 0 1 1 = 1 → f 1 0 0 = 1 →
    (∀ a, f a 1 0 = f a 1 1) → ∀ (e : ℕ → ℕ → ZMod 2) (W d Q t : ℕ),
      (∀ n j, j < W → e (n + 1) j =
        f (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) →
      e 0 0 = 1 → (∀ j, d ≤ j → j < W → e 0 j = 0) → 0 < Q →
      (∀ n j, j < d + 2 → e (n + Q) j = e n j) → 0 < t →
      (∀ n j, j < W → e (n + t) j = e n j) → W < d + 2 * Q + 3

/-- **Reflection carries reproduction to the mirror rule**: if a quiescent rule reproduces a
pattern, its mirror reproduces the reflected pattern. -/
def ReproducesReflect : Prop :=
  ∀ (f : LocalRule) (hq : f 0 0 0 = 0) (p : FiniteConfiguration),
    Reproduces (finRule f hq) p → Reproduces (finRule (mirrorRule f) hq) (reflect p)

/-! ## Windows of a reproduced pattern are purely periodic -/

/-- Closure of windows, iterated: from two nonzero states with equal windows of width `W`, every
iterate of the rule gives a nonzero state, and equal windows of width `W`. -/
private theorem iterate_windows_eq {f : LocalRule} (hq : f 0 0 0 = 0) (h : f 0 0 1 = 1) (W : ℕ) :
    ∀ (j : ℕ) (a b : FiniteConfiguration), a ≠ 0 → b ≠ 0 → a.leftWindow W = b.leftWindow W →
      (finRule f hq)^[j] a ≠ 0 ∧
        ((finRule f hq)^[j] a).leftWindow W = ((finRule f hq)^[j] b).leftWindow W := by
  intro j
  induction j with
  | zero => intro a b ha _ hab; exact ⟨ha, hab⟩
  | succ j ih =>
    intro a b ha hb hab
    obtain ⟨ha', hab'⟩ := leftWindowClosed f hq h W a b ha hb hab
    have hb' := (leftWindowClosed f hq h W b b hb hb rfl).1
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih _ _ ha' hb' hab'

/-- **Windows of a reproduced pattern are purely periodic**: at a quiescent rule with
`f 0 0 1 = 1` that reproduces `p`, at every gap `G` the window of width `diam p + G` of the
iterates of `p` repeats with some period `t ≥ 1` from time `0`. -/
theorem leftWindowPeriodic : LeftWindowPeriodic := by
  intro f hq h p hrep G
  have hp : p ≠ 0 := hrep.1
  obtain ⟨t, k, hk, hcop⟩ := hrep.2 2 G
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exfalso
      have hd := copies_diam_le hp (by simpa using hcop) (by omega)
      have h1 := FiniteConfiguration.one_le_diam hp
      nlinarith
    · exact ht
  have hw := leftWindowCopies p _ k G hp (by omega) hcop
  have hs0 : (finRule f hq)^[t] p ≠ 0 := (iterate_windows_eq hq h 0 t p p hp hp rfl).1
  refine ⟨t, ht, fun n => ?_⟩
  rw [Function.iterate_add_apply]
  exact (iterate_windows_eq hq h (p.diam + G) n _ p hs0 hp hw).2

/-! ## Purely periodic window columns are narrow -/

private theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- The zero triangle: cells `j` with `d + 2 * n ≤ j < W` are clear at time `n`. -/
private theorem columns_zero_triangle {f : LocalRule} (hq : f 0 0 0 = 0) {e : ℕ → ℕ → ZMod 2}
    {W d : ℕ}
    (hr : ∀ n j, j + 2 < W → e (n + 1) (j + 2) = f (e n j) (e n (j + 1)) (e n (j + 2)))
    (hcl : ∀ j, d ≤ j → j < W → e 0 j = 0) :
    ∀ n j, d + 2 * n ≤ j → j < W → e n j = 0 := by
  intro n
  induction n with
  | zero => intro j hj hW; exact hcl j (by omega) hW
  | succ n ih =>
    intro j hj hW
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    rw [hr n j' hW, ih j' (by omega) (by omega), ih (j' + 1) (by omega) (by omega),
      ih (j' + 2) (by omega) (by omega), hq]

/-- Pure periodicity iterated. -/
private theorem columns_periodic_mul {e : ℕ → ℕ → ZMod 2} {W t : ℕ}
    (htp : ∀ n j, j < W → e (n + t) j = e n j) :
    ∀ m n j, j < W → e (n + m * t) j = e n j := by
  intro m
  induction m with
  | zero => intro n j _; simp
  | succ m ih =>
    intro n j hj
    rw [show n + (m + 1) * t = (n + m * t) + t by ring, htp _ _ hj, ih n j hj]

/-- The merge: a column whose two predecessors are `Q`-periodic, the second set somewhere,
is `Q`-periodic. -/
private theorem columns_merge {f : LocalRule} (hm : ∀ a, f a 1 0 = f a 1 1)
    {e : ℕ → ℕ → ZMod 2} {W Q t : ℕ}
    (hr : ∀ n j, j + 2 < W → e (n + 1) (j + 2) = f (e n j) (e n (j + 1)) (e n (j + 2)))
    (ht : 0 < t) (htp : ∀ n j, j < W → e (n + t) j = e n j) {j σ : ℕ} (hj : j + 2 < W)
    (h0 : ∀ n, e (n + Q) j = e n j) (h1 : ∀ n, e (n + Q) (j + 1) = e n (j + 1))
    (hσ : e σ (j + 1) = 1) : ∀ n, e (n + Q) (j + 2) = e n (j + 2) := by
  have hx : ∀ (a x : ZMod 2), f a 1 x = f a 1 0 := by
    intro a x
    rcases zmod2_cases x with rfl | rfl
    · rfl
    · exact (hm a).symm
  have key : ∀ k, e (σ + 1 + k + Q) (j + 2) = e (σ + 1 + k) (j + 2) := by
    intro k
    induction k with
    | zero =>
      have a := hr (σ + Q) j hj
      have b := hr σ j hj
      rw [h0 σ, h1 σ, hσ, hx] at a
      rw [hσ, hx] at b
      rw [show σ + 1 + 0 + Q = σ + Q + 1 by omega, show σ + 1 + 0 = σ + 1 by omega, a, b]
    | succ k ih =>
      have a := hr (σ + 1 + k + Q) j hj
      have b := hr (σ + 1 + k) j hj
      rw [h0, h1, ih] at a
      rw [show σ + 1 + (k + 1) + Q = σ + 1 + k + Q + 1 by omega,
        show σ + 1 + (k + 1) = σ + 1 + k + 1 by omega, a, b]
  intro n
  have hp := columns_periodic_mul htp (σ + 1) n (j + 2) hj
  have hp' := columns_periodic_mul htp (σ + 1) (n + Q) (j + 2) hj
  obtain ⟨k, hk⟩ : ∃ k, n + (σ + 1) * t = σ + 1 + k :=
    ⟨n + (σ + 1) * t - (σ + 1), by have := Nat.le_mul_of_pos_right (σ + 1) ht; omega⟩
  rw [← hp', show n + Q + (σ + 1) * t = σ + 1 + k + Q by omega, key, ← hk, hp]

/-- Column `c` periodic and clear at the first `Q` steps is always clear. -/
private theorem column_clear_of_periodic {e : ℕ → ℕ → ZMod 2} {Q c : ℕ} (hQ : 0 < Q)
    (hP : ∀ n, e (n + Q) c = e n c) (h0 : ∀ n, n < Q → e n c = 0) : ∀ n, e n c = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < Q
    · exact h0 n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + Q := ⟨n - Q, by omega⟩
      rw [hP m]
      exact ih m (by omega)

/-- Descent: two adjacent always-clear columns force the column below them clear. -/
private theorem columns_descent {f : LocalRule} (h100 : f 1 0 0 = 1)
    {e : ℕ → ℕ → ZMod 2} {W : ℕ}
    (hr : ∀ n j, j + 2 < W → e (n + 1) (j + 2) = f (e n j) (e n (j + 1)) (e n (j + 2))) :
    ∀ k, k + 1 < W → (∀ n, e n k = 0) → (∀ n, e n (k + 1) = 0) → ∀ n, e n 0 = 0 := by
  intro k
  induction k with
  | zero => intro _ h _; exact h
  | succ k ih =>
    intro hW hk hk1
    refine ih (by omega) ?_ hk
    intro n
    have a := hr n k (by omega)
    have l : e (n + 1) (k + 2) = 0 := hk1 (n + 1)
    have m1 : e n (k + 1) = 0 := hk n
    have m2 : e n (k + 2) = 0 := hk1 n
    rw [l, m1, m2] at a
    rcases zmod2_cases (e n k) with h | h
    · exact h
    · rw [h, h100] at a
      exact absurd a (by decide)

/-- The monotone step: with column `i` always clear, column `i + 1` is always clear too, when
column `i + 2` is clear at time `0` and every column is purely periodic. -/
private theorem columns_monotone {f : LocalRule} (h001 : f 0 0 1 = 1)
    (h011 : f 0 1 1 = 1) (hm : ∀ a, f a 1 0 = f a 1 1)
    {e : ℕ → ℕ → ZMod 2} {W t i : ℕ}
    (hr : ∀ n j, j + 2 < W → e (n + 1) (j + 2) = f (e n j) (e n (j + 1)) (e n (j + 2)))
    (ht : 0 < t) (htp : ∀ n j, j < W → e (n + t) j = e n j) (hi : i + 2 < W)
    (h0 : e 0 (i + 2) = 0) (hc : ∀ n, e n i = 0) :
    (∀ n, e n (i + 2) = 0) ∧ ∀ n, e n (i + 1) = 0 := by
  have mono : ∀ n, e n (i + 2) = 1 → e (n + 1) (i + 2) = 1 := by
    intro n hn
    rw [hr n i hi, hc n, hn]
    rcases zmod2_cases (e n (i + 1)) with h | h
    · rw [h, h001]
    · rw [h, h011]
  have mono' : ∀ m n, e n (i + 2) = 1 → e (n + m) (i + 2) = 1 := by
    intro m
    induction m with
    | zero => intro n hn; simpa using hn
    | succ m ih => intro n hn; exact mono _ (ih n hn)
  have hclr : ∀ n, e n (i + 2) = 0 := by
    intro n
    rcases zmod2_cases (e n (i + 2)) with h | h
    · exact h
    · exfalso
      obtain ⟨m, hmn⟩ := Nat.exists_eq_add_of_le (show n ≤ n * t by nlinarith)
      have h1 := mono' m n h
      rw [← hmn] at h1
      have h2 := columns_periodic_mul htp n 0 (i + 2) hi
      rw [zero_add] at h2
      rw [h2, h0] at h1
      exact absurd h1 (by decide)
  refine ⟨hclr, fun n => ?_⟩
  have a := hr n i hi
  rw [hclr (n + 1), hc n, hclr n] at a
  rcases zmod2_cases (e n (i + 1)) with h | h
  · exact h
  · rw [h, show f 0 1 0 = 1 by rw [hm 0, h011]] at a
    exact absurd a (by decide)

/-- **A family of purely periodic columns is narrow.** -/
theorem periodicColumnsNarrow : PeriodicColumnsNarrow := by
  intro f hq h001 h011 h100 hm e W d Q t hrec he0 hclear hQ hQp ht htp
  by_contra hW
  have hW : d + 2 * Q + 3 ≤ W := by omega
  have hr : ∀ n j, j + 2 < W → e (n + 1) (j + 2) = f (e n j) (e n (j + 1)) (e n (j + 2)) := by
    intro n j hj
    have := hrec n (j + 2) hj
    simpa using this
  have tri := columns_zero_triangle hq hr hclear
  -- some column from `d` to `d + 2 * Q` is always clear
  have hex : ∃ i, d ≤ i ∧ i ≤ d + 2 * Q ∧ ∀ n, e n i = 0 := by
    by_contra hno
    push Not at hno
    have hset : ∀ i, d ≤ i → i ≤ d + 2 * Q → ∃ σ, e σ i = 1 := by
      intro i h1 h2
      obtain ⟨σ, hσ⟩ := hno i h1 h2
      exact ⟨σ, (zmod2_cases _).resolve_left hσ⟩
    have P : ∀ k, k ≤ 2 * Q → ∀ j, j < d + 2 + k → ∀ n, e (n + Q) j = e n j := by
      intro k
      induction k with
      | zero => intro _ j hj n; exact hQp n j (by omega)
      | succ k ih =>
        intro hk j hj n
        by_cases hjk : j < d + 2 + k
        · exact ih (by omega) j hjk n
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
          obtain ⟨σ, hσ⟩ := hset (j' + 1) (by omega) (by omega)
          exact columns_merge hm hr ht htp (by omega) (ih (by omega) j' (by omega))
            (ih (by omega) (j' + 1) (by omega)) hσ n
    have hper := P (2 * Q) le_rfl (d + 2 * Q) (by omega)
    have hz : ∀ n, e n (d + 2 * Q) = 0 := by
      refine column_clear_of_periodic hQ hper fun n hn => ?_
      exact tri n _ (by omega) (by omega)
    obtain ⟨σ, hσ⟩ := hset (d + 2 * Q) (by omega) le_rfl
    rw [hz σ] at hσ
    exact absurd hσ (by decide)
  obtain ⟨i, hi1, hi2, hc⟩ := hex
  have h0 : e 0 (i + 2) = 0 := hclear (i + 2) (by omega) (by omega)
  obtain ⟨hc2, hc1⟩ := columns_monotone h001 h011 hm hr ht htp (by omega) h0 hc
  have := columns_descent h100 hr i (by omega) hc hc1 0
  rw [this] at he0
  exact absurd he0 (by decide)

/-- **The hypotheses of the narrowness statement meet**: at rule `30`, width `4`, `d = 2`,
`Q = t = 2`, the family of the window `1100` (which steps to `1101` and back) meets every
hypothesis, and the conclusion `4 < 2 + 2 * 2 + 3` is visible. -/
theorem periodicColumnsNarrow_nonvacuous (e : ℕ → ℕ → ZMod 2)
    (he : ∀ n j, e n j =
      if j = 0 ∨ j = 1 then 1 else if j = 3 ∧ n % 2 = 1 then 1 else 0) :
    (wolframRule 30 0 0 0 = 0 ∧ wolframRule 30 0 0 1 = 1 ∧ wolframRule 30 0 1 1 = 1 ∧
      wolframRule 30 1 0 0 = 1 ∧ ∀ a, wolframRule 30 a 1 0 = wolframRule 30 a 1 1) ∧
    (∀ n j, j < 4 → e (n + 1) j = wolframRule 30 (if 2 ≤ j then e n (j - 2) else 0)
      (if 1 ≤ j then e n (j - 1) else 0) (e n j)) ∧
    e 0 0 = 1 ∧ (∀ j, 2 ≤ j → j < 4 → e 0 j = 0) ∧ 0 < 2 ∧
    (∀ n j, j < 2 + 2 → e (n + 2) j = e n j) ∧ 0 < 2 ∧ (∀ n j, j < 4 → e (n + 2) j = e n j) ∧
    4 < 2 + 2 * 2 + 3 := by
  refine ⟨by decide, ?_, by simp [he], ?_, by decide, ?_, by decide, ?_, by decide⟩
  · intro n j hj
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
    · have h' : (n + 1) % 2 = 0 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
  · intro j h1 h2
    interval_cases j <;> simp [he]
  · intro n j hj
    have h' : (n + 2) % 2 = n % 2 := by omega
    simp only [he, h']
  · intro n j hj
    have h' : (n + 2) % 2 = n % 2 := by omega
    simp only [he, h']

/-! ## The sink -/

private theorem iterate_ne_zero {f : LocalRule} (hq : f 0 0 0 = 0) (h : f 0 0 1 = 1)
    {p : FiniteConfiguration} (hp : p ≠ 0) :
    ∀ n : ℕ, (finRule f hq)^[n] p ≠ 0 := by
  intro n
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact LocalRule.finRule_ne_zero_of_leftTap h ih

private theorem leftWindow_zero_ne {s : FiniteConfiguration} (hs : s ≠ 0) {W : ℕ} (hW : 0 < W) :
    s.leftWindow W 0 = 1 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hmem : s.leftEnd ∈ s.support := by
    rw [FiniteConfiguration.leftEnd_eq hne]
    exact Finset.min'_mem _ _
  have h0 : s s.leftEnd ≠ 0 := Finsupp.mem_support_iff.mp hmem
  simp only [leftWindow, hW, ite_true, Nat.cast_zero, add_zero]
  generalize s s.leftEnd = x at h0
  revert x
  decide

/-- **A quiescent rule with four bits and a middle-set symmetry reproduces no pattern**, from the
periodicity of windows and the narrowness of periodic columns as hypotheses: the periods at gaps
`2` and `2 * Q + 3` give a family of purely periodic columns obeying the window recurrence whose
width exceeds what narrowness allows. -/
theorem not_reproduces_of_columns (h1 : LeftWindowPeriodic) (h2 : PeriodicColumnsNarrow)
    {f : LocalRule} (hq : f 0 0 0 = 0) (h001 : f 0 0 1 = 1) (h011 : f 0 1 1 = 1)
    (h100 : f 1 0 0 = 1) (hm : ∀ a, f a 1 0 = f a 1 1) (p : FiniteConfiguration) :
    ¬ Reproduces (finRule f hq) p := by
  intro hrep
  have hp : p ≠ 0 := hrep.1
  obtain ⟨Q, hQ, hQp⟩ := h1 f hq h001 p hrep 2
  obtain ⟨t, ht, htp⟩ := h1 f hq h001 p hrep (2 * Q + 3)
  have key := h2 f hq h001 h011 h100 hm
    (fun n j => ((finRule f hq)^[n] p).leftWindow (p.diam + (2 * Q + 3)) j)
    (p.diam + (2 * Q + 3)) p.diam Q t
    (by
      intro n j hj
      rw [Function.iterate_succ_apply']
      exact FiniteConfiguration.leftWindow_finRule h001 (iterate_ne_zero hq h001 hp n) hj)
    (leftWindow_zero_ne hp (by omega))
    (by
      intro j hj1 hj2
      exact FiniteConfiguration.leftWindow_eq_zero_of_diam_le hp hj1 hj2)
    hQ
    (by
      intro n j hj
      have hl : ∀ m : ℕ, ((finRule f hq)^[m] p).leftWindow (p.diam + (2 * Q + 3)) j =
          ((finRule f hq)^[m] p).leftWindow (p.diam + 2) j := by
        intro m
        have hj' : j < p.diam + (2 * Q + 3) := by omega
        simp only [leftWindow, hj, hj', ite_true]
      rw [hl, hl]
      exact congrFun (hQp n) j)
    ht
    (fun n j _ => congrFun (htp n) j)
  omega

/-! ## Rules `30` and `86` -/

/-- Equal rules reproduce the same patterns, whatever the proofs of quiescence. -/
private theorem reproduces_congr {f g : LocalRule} (h : f = g) (hf : f 0 0 0 = 0)
    (hg : g 0 0 0 = 0) {p : FiniteConfiguration} :
    Reproduces (finRule f hf) p → Reproduces (finRule g hg) p := by
  subst h
  exact id

/-- **Rule `30` reproduces no pattern**, from the periodicity of windows and the narrowness of
periodic columns as hypotheses. -/
theorem not_reproduces_wolfram30_of_columns (h1 : LeftWindowPeriodic)
    (h2 : PeriodicColumnsNarrow) :
    ∀ (hq : wolframRule 30 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 30) hq) p := by
  intro hq p
  exact not_reproduces_of_columns h1 h2 hq (by decide) (by decide) (by decide) (by decide) p

/-- **Rule `86` reproduces no pattern**, from the same two statements and reflection: rule `86` is
the mirror of rule `30`, so a pattern it reproduces reflects to one that rule `30` reproduces. -/
theorem not_reproduces_wolfram86_of_columns (h1 : LeftWindowPeriodic)
    (h2 : PeriodicColumnsNarrow) (h3 : ReproducesReflect) :
    ∀ (hq : wolframRule 86 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 86) hq) p := by
  intro hq p hrep
  have hm : mirrorRule (wolframRule 86) = wolframRule 30 := by
    funext a b c
    revert a b c
    decide
  have hq30 : wolframRule 30 0 0 0 = 0 := by decide
  exact not_reproduces_wolfram30_of_columns h1 h2 hq30 (reflect p)
    (reproduces_congr hm _ hq30 (h3 _ hq p hrep))

/-- **A quiescent rule with four bits and a middle-set symmetry reproduces no pattern**: if
`f` is quiescent, sends `0 0 1`, `0 1 1` and `1 0 0` to `1` and ignores its last cell on a set
middle cell, no pattern is reproduced; no hypothesis is left beyond the rule's bits. -/
theorem not_reproduces_of_bits {f : LocalRule} (hq : f 0 0 0 = 0) (h001 : f 0 0 1 = 1)
    (h011 : f 0 1 1 = 1) (h100 : f 1 0 0 = 1) (hm : ∀ a, f a 1 0 = f a 1 1)
    (p : FiniteConfiguration) : ¬ Reproduces (finRule f hq) p :=
  not_reproduces_of_columns leftWindowPeriodic periodicColumnsNarrow hq h001 h011 h100 hm p

/-- **Rule `30` reproduces no pattern**, with no hypothesis left beyond the rule's bits. -/
theorem not_reproduces_wolfram30 :
    ∀ (hq : wolframRule 30 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 30) hq) p :=
  not_reproduces_wolfram30_of_columns leftWindowPeriodic periodicColumnsNarrow

/-- **The five hypotheses on the rule meet**: rule `30` is quiescent, sends `0 0 1`, `0 1 1` and
`1 0 0` to `1`, and ignores its last cell on a set middle cell. -/
theorem not_reproduces_of_columns_nonvacuous :
    wolframRule 30 0 0 0 = 0 ∧ wolframRule 30 0 0 1 = 1 ∧ wolframRule 30 0 1 1 = 1 ∧
      wolframRule 30 1 0 0 = 1 ∧ ∀ a, wolframRule 30 a 1 0 = wolframRule 30 a 1 1 := by
  decide

/-! ## Each rule-bit hypothesis is needed -/

/-- Transport of a reproduced pattern from a rule to a pointwise equal one. -/
private theorem exists_reproduces_of_mem_fifteen {g f : LocalRule} (hf : f ∈ fifteen)
    (hg : g 0 0 0 = 0) (h : ∀ a b c, g a b c = f a b c) : ∃ p, Reproduces (finRule g hg) p := by
  have he : g = f := by
    funext a b c
    exact h a b c
  have hf0 : f 0 0 0 = 0 := he ▸ hg
  obtain ⟨p, hp⟩ := reproduces_of_mem_fifteen f hf0 hf
  exact ⟨p, reproduces_congr he.symm hf0 hg hp⟩

/-- **Rule `60` reproduces a pattern although it meets all but `f 0 0 1 = 1`**: that bit fails
there, and the other four hypotheses of the sink hold. -/
theorem exists_reproduces_wolfram60 (hq : wolframRule 60 0 0 0 = 0) :
    wolframRule 60 0 0 1 ≠ 1 ∧ wolframRule 60 0 1 1 = 1 ∧ wolframRule 60 1 0 0 = 1 ∧
      (∀ a, wolframRule 60 a 1 0 = wolframRule 60 a 1 1) ∧
      ∃ p, Reproduces (finRule (wolframRule 60) hq) p :=
  ⟨by decide, by decide, by decide, by decide,
    exists_reproduces_of_mem_fifteen (f := f60) (by simp [fifteen]) hq (by decide)⟩

/-- **Rule `18` reproduces a pattern although it meets all but `f 0 1 1 = 1`**: that bit fails
there, and the other four hypotheses of the sink hold. -/
theorem exists_reproduces_wolfram18 (hq : wolframRule 18 0 0 0 = 0) :
    wolframRule 18 0 0 1 = 1 ∧ wolframRule 18 0 1 1 ≠ 1 ∧ wolframRule 18 1 0 0 = 1 ∧
      (∀ a, wolframRule 18 a 1 0 = wolframRule 18 a 1 1) ∧
      ∃ p, Reproduces (finRule (wolframRule 18) hq) p :=
  ⟨by decide, by decide, by decide, by decide,
    exists_reproduces_of_mem_fifteen (f := f18) (by simp [fifteen]) hq (by decide)⟩

/-- **Rule `26` reproduces a pattern although it meets all but `f a 1 0 = f a 1 1` at `a = 0`**:
that equation fails there, and the other four hypotheses of the sink hold. -/
theorem exists_reproduces_wolfram26 (hq : wolframRule 26 0 0 0 = 0) :
    wolframRule 26 0 0 1 = 1 ∧ wolframRule 26 0 1 1 = 1 ∧ wolframRule 26 1 0 0 = 1 ∧
      wolframRule 26 0 1 0 ≠ wolframRule 26 0 1 1 ∧
      ∃ p, Reproduces (finRule (wolframRule 26) hq) p :=
  ⟨by decide, by decide, by decide, by decide,
    exists_reproduces_of_mem_fifteen (f := f26) (by simp [fifteen]) hq (by decide)⟩

/-- **Rule `126` reproduces a pattern although it meets all but `f a 1 0 = f a 1 1` at `a = 1`**:
that equation fails there, and the other four hypotheses of the sink hold. -/
theorem exists_reproduces_wolfram126 (hq : wolframRule 126 0 0 0 = 0) :
    wolframRule 126 0 0 1 = 1 ∧ wolframRule 126 0 1 1 = 1 ∧ wolframRule 126 1 0 0 = 1 ∧
      wolframRule 126 1 1 0 ≠ wolframRule 126 1 1 1 ∧
      ∃ p, Reproduces (finRule (wolframRule 126) hq) p :=
  ⟨by decide, by decide, by decide, by decide,
    exists_reproduces_of_mem_fifteen (f := f126) (by simp [fifteen]) hq (by decide)⟩

/-- **The hypotheses of the periodicity statement meet**: rule `90` is quiescent, sends `0 0 1`
to `1`, and reproduces a pattern. -/
theorem leftWindowPeriodic_nonvacuous (hq : wolframRule 90 0 0 0 = 0) :
    wolframRule 90 0 0 1 = 1 ∧ ∃ p, Reproduces (finRule (wolframRule 90) hq) p :=
  ⟨by decide,
    exists_reproduces_of_mem_fifteen (f := f90) (by simp [fifteen]) hq (by decide)⟩

/-! ## Reflection carries reproduction to the mirror rule -/

/-- Reflection of a translate is the translate by the opposite offset of the reflection. -/
private theorem reflect_translate (c : ℤ) (s : FiniteConfiguration) :
    reflect (FiniteConfiguration.translate c s) =
      FiniteConfiguration.translate (-c) (reflect s) := by
  unfold reflect FiniteConfiguration.translate
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext x
  simp only [Function.comp]
  ring

/-- Reflection of a nonzero pattern is nonzero. -/
private theorem reflect_ne_zero {p : FiniteConfiguration} (hp : p ≠ 0) : reflect p ≠ 0 := by
  intro h
  apply hp
  rw [← reflect_reflect p, h]
  simp [reflect]

/-- Reflection of copies: `k` copies of `p` at gap `G` reflect to `k` copies of the reflection of
`p` at gap `G`, in the opposite order. -/
private theorem copies_reflect {p s : FiniteConfiguration} {k G : ℕ} (h : Copies p s k G) :
    Copies (reflect p) (reflect s) k G := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun j => -c (k - 1 - j), ?_, ?_⟩
  · intro j hj
    have e1 : k - 1 - j = (k - 2 - j) + 1 := by omega
    have e2 : k - 1 - (j + 1) = k - 2 - j := by omega
    have := hc (k - 2 - j) (by omega)
    simp only [e1, e2, diam_reflect]
    omega
  · have hs : reflect ((Finset.range k).sum fun j => FiniteConfiguration.translate (c j) p) =
        (Finset.range k).sum fun j => reflect (FiniteConfiguration.translate (c j) p) :=
      Finsupp.mapDomain_finsetSum
    rw [hs]
    simp only [reflect_translate]
    exact (Finset.sum_range_reflect
      (fun j => FiniteConfiguration.translate (-c j) (reflect p)) k).symm

/-- Iterates of the mirror rule at a reflected state are reflections of the iterates. -/
private theorem iterate_mirror_reflect' (f : LocalRule) (hq : f 0 0 0 = 0)
    (s : FiniteConfiguration) :
    ∀ t : ℕ, (finRule (mirrorRule f) hq)^[t] (reflect s) = reflect ((finRule f hq)^[t] s) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      finRule_mirrorRule_reflect]

/-- **Reflection carries reproduction to the mirror rule**: if a quiescent rule reproduces a
pattern, its mirror reproduces the reflected pattern. -/
theorem reproducesReflect : ReproducesReflect := by
  intro f hq p hp
  obtain ⟨hne, h⟩ := hp
  refine ⟨reflect_ne_zero hne, fun N G => ?_⟩
  obtain ⟨t, k, hk, hc⟩ := h N G
  exact ⟨t, k, hk, by rw [iterate_mirror_reflect']; exact copies_reflect hc⟩

/-- **The hypothesis and conclusion of reflection meet at a rule that is not its own mirror**:
rule `60` reproduces a pattern, and its mirror, rule `102`, reproduces the reflected pattern. -/
theorem reproducesReflect_nonvacuous (hq : wolframRule 60 0 0 0 = 0) :
    ∃ p, Reproduces (finRule (wolframRule 60) hq) p ∧
      Reproduces (finRule (mirrorRule (wolframRule 60)) hq) (reflect p) := by
  obtain ⟨p, hp⟩ := (exists_reproduces_wolfram60 hq).2.2.2.2
  exact ⟨p, hp, reproducesReflect _ hq p hp⟩

/-- **Rule `86` reproduces no pattern**, with no hypothesis left. -/
theorem not_reproduces_wolfram86 :
    ∀ (hq : wolframRule 86 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 86) hq) p :=
  not_reproduces_wolfram86_of_columns leftWindowPeriodic periodicColumnsNarrow reproducesReflect

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.leftWindowPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.leftWindowPeriodic

set_option linter.style.longLine false in
/-- info: 'ECA.leftWindowPeriodic_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.leftWindowPeriodic_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_of_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_columns

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram30_of_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram30_of_columns

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram86_of_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram86_of_columns

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_of_columns_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_columns_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.exists_reproduces_wolfram60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_reproduces_wolfram60

set_option linter.style.longLine false in
/-- info: 'ECA.exists_reproduces_wolfram18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_reproduces_wolfram18

set_option linter.style.longLine false in
/-- info: 'ECA.exists_reproduces_wolfram26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_reproduces_wolfram26

set_option linter.style.longLine false in
/-- info: 'ECA.exists_reproduces_wolfram126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_reproduces_wolfram126

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsNarrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsNarrow

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsNarrow_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsNarrow_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_of_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_bits

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram30

set_option linter.style.longLine false in
/-- info: 'ECA.reproducesReflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproducesReflect

set_option linter.style.longLine false in
/-- info: 'ECA.reproducesReflect_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproducesReflect_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram86' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram86
