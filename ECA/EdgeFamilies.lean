module

public import ECA.EdgeColumns
import all ECA.EdgeColumns
import all ECA.EdgeWindow

/-!
# Rules `110` and `124` reproduce no pattern, from a bound on column periods
([RuleSpace] §5)

At a quiescent rule with `f 0 0 1 = 1` that ignores its left cells when its last cell is clear,
`f a b 0 = b`, the window read from the leftmost set cell of a reproduced pattern `p` is purely
periodic in time at every gap. Take the window of width `diam p + B` and write `e n j` for its
cell `j` at time `n`. The cells from `diam p + n` on are clear at time `n`, since the rule moves a
set cell one place to the right at most per step. If every purely periodic family of window cells
with its first cell set has all its columns of period dividing `B`, column `diam p + B - 1` is
clear at the steps `0` to `B - 1` and so at every step, and then each column in turn, down to
column `0`, is clear at every step, against the first cell being set. So no pattern is reproduced.
Rule `110` meets the three bits, and rule `124` is its mirror. The bound `64` at rule `110` is
proved in `ECA.Rule110Bound`, so rules `110` and `124` reproduce no pattern unconditionally.

## Main results

* `PeriodicColumnsBounded` — every purely periodic family of window cells at a rule, with its
  first cell set, has every column of period dividing `B`.
* `not_reproduces_of_periodicColumnsBounded` — a quiescent rule with `f 0 0 1 = 1` and
  `f a b 0 = b` reproduces no pattern, given such a bound `B`; the hypotheses on the rule and the
  bound meet at rule `110` and `B = 64` in `not_reproduces_of_periodicColumnsBounded_nonvacuous`.
* `not_reproduces_wolfram110_of_bounded` / `not_reproduces_wolfram124_of_bounded` — rules `110`
  and `124` reproduce no pattern, from the bound `64` at rule `110`, the latter by reflection;
  the bound is `periodicColumnsBounded_wolfram110` in `ECA.Rule110Bound`, which gives both
  without a hypothesis.
* `exists_reproduces_wolfram102` — the bound is needed by any argument from the rule's bits
  alone: rule `102` meets the three bits and reproduces a pattern.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- **Every purely periodic family of window cells has columns of period dividing `B`**: at the
rule `f`, a family `e n j` obeying the window recurrence below the width `W`, with its first cell
set and every column of period `t ≥ 1`, has every column of period `B`. -/
def PeriodicColumnsBounded (f : LocalRule) (B : ℕ) : Prop :=
  ∀ (e : ℕ → ℕ → ZMod 2) (W t : ℕ),
    (∀ n j, j < W → e (n + 1) j =
      f (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) →
    e 0 0 = 1 → 0 < t → (∀ n j, j < W → e (n + t) j = e n j) →
      ∀ n j, j < W → e (n + B) j = e n j

/-- The zero triangle at speed one: cells `j` with `d + n ≤ j < W` are clear at time `n`. -/
private theorem family_zero_triangle {f : LocalRule} (hb : ∀ a b, f a b 0 = b)
    {e : ℕ → ℕ → ZMod 2} {W d : ℕ}
    (hrec : ∀ n j, j < W → e (n + 1) j =
      f (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j))
    (hcl : ∀ j, d ≤ j → j < W → e 0 j = 0) :
    ∀ n j, d + n ≤ j → j < W → e n j = 0 := by
  intro n
  induction n with
  | zero => intro j hj hW; exact hcl j (by omega) hW
  | succ n ih =>
    intro j hj hW
    have h1 : 1 ≤ j := by omega
    rw [hrec n j hW, ih j (by omega) hW, hb]
    simpa [h1] using ih (j - 1) (by omega) (by omega)

/-- A column periodic of period `Q` and clear at the first `Q` steps is always clear. -/
private theorem family_column_clear {e : ℕ → ℕ → ZMod 2} {Q c : ℕ} (hQ : 0 < Q)
    (hP : ∀ n, e (n + Q) c = e n c) (h0 : ∀ n, n < Q → e n c = 0) : ∀ n, e n c = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < Q
    · exact h0 n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + Q := ⟨n - Q, by omega⟩
      rw [hP m]
      exact ih m (by omega)

/-- The descent: a column that is clear at every step has the column below it clear at every
step. -/
private theorem family_descent {f : LocalRule} (hb : ∀ a b, f a b 0 = b)
    {e : ℕ → ℕ → ZMod 2} {W : ℕ}
    (hrec : ∀ n j, j < W → e (n + 1) j =
      f (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) :
    ∀ k, k < W → (∀ n, e n k = 0) → ∀ n, e n 0 = 0 := by
  intro k
  induction k with
  | zero => intro _ h; exact h
  | succ k ih =>
    intro hW hk
    refine ih (by omega) fun n => ?_
    have a := hrec n (k + 1) hW
    rw [hk (n + 1), hk n, hb] at a
    simpa using a.symm

/-- **A quiescent rule with `f 0 0 1 = 1` and `f a b 0 = b` reproduces no pattern**, given a
bound `B ≥ 1` on the periods of the columns of purely periodic families of window cells. -/
theorem not_reproduces_of_periodicColumnsBounded {f : LocalRule} (hq : f 0 0 0 = 0)
    (h001 : f 0 0 1 = 1) (hb : ∀ a b, f a b 0 = b) {B : ℕ} (hB : 0 < B)
    (h : PeriodicColumnsBounded f B) (p : FiniteConfiguration) :
    ¬ Reproduces (finRule f hq) p := by
  intro hrep
  have hp : p ≠ 0 := hrep.1
  obtain ⟨t, ht, htp⟩ := leftWindowPeriodic f hq h001 p hrep B
  have hrec : ∀ n j, j < p.diam + B →
      ((finRule f hq)^[n + 1] p).leftWindow (p.diam + B) j =
        f (if 2 ≤ j then ((finRule f hq)^[n] p).leftWindow (p.diam + B) (j - 2) else 0)
          (if 1 ≤ j then ((finRule f hq)^[n] p).leftWindow (p.diam + B) (j - 1) else 0)
          (((finRule f hq)^[n] p).leftWindow (p.diam + B) j) := by
    intro n j hj
    rw [Function.iterate_succ_apply']
    exact FiniteConfiguration.leftWindow_finRule h001 (iterate_ne_zero hq h001 hp n) hj
  have hper := h (fun n j => ((finRule f hq)^[n] p).leftWindow (p.diam + B) j) (p.diam + B) t
    hrec (leftWindow_zero_ne hp (by omega)) ht (fun n j _ => congrFun (htp n) j)
  have tri := family_zero_triangle (e := fun n j => ((finRule f hq)^[n] p).leftWindow
      (p.diam + B) j) (W := p.diam + B) (d := p.diam) hb hrec fun j hj1 hj2 =>
    FiniteConfiguration.leftWindow_eq_zero_of_diam_le hp hj1 hj2
  have hz : ∀ n, ((finRule f hq)^[n] p).leftWindow (p.diam + B) (p.diam + B - 1) = 0 :=
    family_column_clear hB (fun n => hper n _ (by omega)) fun n hn =>
      tri n _ (by omega) (by omega)
  have h0 := family_descent hb hrec (p.diam + B - 1) (by omega) hz 0
  have h1 : ((finRule f hq)^[0] p).leftWindow (p.diam + B) 0 = 1 :=
    leftWindow_zero_ne hp (by omega)
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- **Rule `110` reproduces no pattern**, from the bound `64` on the column periods at rule
`110`. -/
theorem not_reproduces_wolfram110_of_bounded (h : PeriodicColumnsBounded (wolframRule 110) 64) :
    ∀ (hq : wolframRule 110 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 110) hq) p := by
  intro hq p
  exact not_reproduces_of_periodicColumnsBounded hq (by decide) (by decide) (by norm_num) h p

/-- **Rule `124` reproduces no pattern**, from the same bound at rule `110` and reflection: rule
`124` is the mirror of rule `110`, so a pattern it reproduces reflects to one that rule `110`
reproduces. -/
theorem not_reproduces_wolfram124_of_bounded (h : PeriodicColumnsBounded (wolframRule 110) 64) :
    ∀ (hq : wolframRule 124 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 124) hq) p := by
  intro hq p hrep
  have hm : mirrorRule (wolframRule 124) = wolframRule 110 := by
    funext a b c
    revert a b c
    decide
  have hq110 : wolframRule 110 0 0 0 = 0 := by decide
  exact not_reproduces_wolfram110_of_bounded h hq110 (reflect p)
    (reproduces_congr hm _ hq110 (reproducesReflect _ hq p hrep))

/-- **The hypotheses of the sink meet**: rule `110` is quiescent, sends `0 0 1` to `1`, ignores
its left cells when its last cell is clear, and `64` is positive. -/
theorem not_reproduces_of_periodicColumnsBounded_nonvacuous :
    wolframRule 110 0 0 0 = 0 ∧ wolframRule 110 0 0 1 = 1 ∧
      (∀ a b, wolframRule 110 a b 0 = b) ∧ 0 < 64 := by
  refine ⟨by decide, by decide, by decide, by norm_num⟩

/-- **The bound is needed**: rule `102` is quiescent, sends `0 0 1` to `1` and ignores its left
cells when its last cell is clear, and it reproduces a pattern. -/
theorem exists_reproduces_wolfram102 (hq : wolframRule 102 0 0 0 = 0) :
    wolframRule 102 0 0 1 = 1 ∧ (∀ a b, wolframRule 102 a b 0 = b) ∧
      ∃ p, Reproduces (finRule (wolframRule 102) hq) p :=
  ⟨by decide, by decide,
    exists_reproduces_of_mem_fifteen (f := f102) (by simp [fifteen]) hq (by decide)⟩

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_of_periodicColumnsBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_periodicColumnsBounded

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram110_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram110_of_bounded

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram124_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram124_of_bounded

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_of_periodicColumnsBounded_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_periodicColumnsBounded_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.exists_reproduces_wolfram102' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_reproduces_wolfram102
