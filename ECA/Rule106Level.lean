module

public import ECA.Rule106
import all ECA.Rule106

/-!
# Rule `106` renormalizes onto itself, at every scale
([RuleSpace] §5)

Write `Rule106Runs w` when every run of two or more set cells of the window `w` starts at a
multiple of `3`, and `Rule106Stays w` when every iterate of `w` under `window106` satisfies it.
Four steps of `window106` after the renormalization `renorm` equal the renormalization after one
step exactly on the windows satisfying `Rule106Runs` (`rule106RenormIff`), and the renormalization
followed by up to three steps keeps the condition (`rule106RunsRenorm`). From these two statements,
with no hypothesis left, four steps commute with the renormalization along the whole orbit of a
window exactly when the orbit stays, the renormalization of a staying window stays, and at every
scale `m`, `4 ^ m * n` steps of the `m`-fold renormalization of a staying window equal the
`m`-fold renormalization of its `n`-th iterate: rule `106` is its own next level.

## Main results

* `Rule106Runs` / `Rule106Stays` — the run condition on a window, and on its whole orbit;
  `rule106Class_iff` — the class `Rule106Class` is the run condition with cells `0` and `1` set.
* `Rule106RenormIff` / `Rule106RunsRenorm` — the two statements as propositions, and
  `rule106RenormIff` / `rule106RunsRenorm` — both proved; `renorm_window106_four_of_runs` — the
  one-step identity at every window with the run condition, cells `0` and `1` free;
  `rule106RenormIff_nonvacuous` — the backward direction with content: at the window with cells
  `0`, `2` and `3` set the condition fails and the two sides differ at cell `7`, at the window
  with cells `0`, `3` and `4` set it holds and the identity holds.
* `renorm_window106_iterate_iff` — the identity of `4 * n` steps after the renormalization with
  the renormalization after `n` steps holds at every `n` exactly when the orbit stays.
* `rule106Stays_renorm` — the renormalization of a staying window stays.
* `renorm_pow_window106_iterate` — at every scale `m`, the `m`-fold renormalization of a staying
  window stays, and `4 ^ m * n` steps of it equal the `m`-fold renormalization of the `n`-th
  iterate.
* `renorm_window106_iterate_iff_of` / `rule106Stays_renorm_of` / `renorm_pow_window106_iterate_of`
  — the same three taking the two statements as hypotheses.
* `rule106Stays_pair` / `renorm_pow_window106_iterate_nonvacuous` — the orbit of the pair stays,
  and the identity at `m = 1`, `n = 6` evaluated on the pair: both sides have cells `0`, `1`, `6`
  and `7` set.
* `not_renorm_window106_eight` — the run condition at the start is not enough: at the window with
  cells `0`, `1`, `2`, `3` and `5` set, the condition holds, its successor fails it, and the two
  sides of the identity at `m = 1`, `n = 2` differ at cell `12`.
-/

@[expose] public section

namespace ECA

/-- **The run condition**: every run of two or more set cells starts at a multiple of `3`. -/
def Rule106Runs (w : ℕ → ZMod 2) : Prop :=
  ∀ j, w j = 0 → w (j + 1) = 1 → w (j + 2) = 1 → (j + 1) % 3 = 0

/-- **The windows whose orbit stays**: every iterate of the window under `window106` satisfies the
run condition. -/
def Rule106Stays (w : ℕ → ZMod 2) : Prop :=
  ∀ n, Rule106Runs (window106^[n] w)

/-- **The renormalization of one step**: four steps after the renormalization equal the
renormalization after one step exactly on the windows satisfying the run condition. -/
def Rule106RenormIff : Prop :=
  ∀ w : ℕ → ZMod 2, window106^[4] (renorm w) = renorm (window106 w) ↔ Rule106Runs w

/-- **The run condition is kept by a renormalization**: the renormalization and up to three steps
keep the run condition. -/
def Rule106RunsRenorm : Prop :=
  ∀ w : ℕ → ZMod 2, Rule106Runs w → ∀ r < 4, Rule106Runs (window106^[r] (renorm w))

/-- **The class is the run condition with cells `0` and `1` set.** -/
theorem rule106Class_iff {w : ℕ → ZMod 2} :
    Rule106Class w ↔ w 0 = 1 ∧ w 1 = 1 ∧ Rule106Runs w := Iff.rfl

/-- **Along an orbit**: four steps commute with the renormalization at every `n` exactly when the
orbit of the window stays. -/
theorem renorm_window106_iterate_iff_of (h1 : Rule106RenormIff) (w : ℕ → ZMod 2) :
    (∀ n, window106^[4 * n] (renorm w) = renorm (window106^[n] w)) ↔ Rule106Stays w := by
  constructor
  · intro h n
    refine (h1 _).mp ?_
    have e := h (n + 1)
    have es : window106^[n + 1] w = window106 (window106^[n] w) :=
      Function.iterate_succ_apply' _ _ _
    rw [show 4 * (n + 1) = 4 + 4 * n by ring, Function.iterate_add_apply, h n, es] at e
    exact e
  · intro hs n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show 4 * (n + 1) = 4 + 4 * n by ring, Function.iterate_add_apply, ih,
        (h1 _).mpr (hs n), Function.iterate_succ_apply']

/-- **The renormalization of a staying window stays.** -/
theorem rule106Stays_renorm_of (h1 : Rule106RenormIff) (h2 : Rule106RunsRenorm)
    {w : ℕ → ZMod 2} (hw : Rule106Stays w) : Rule106Stays (renorm w) := by
  intro k
  have e : window106^[k] (renorm w) =
      window106^[k % 4] (window106^[4 * (k / 4)] (renorm w)) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [e, (renorm_window106_iterate_iff_of h1 w).mpr hw (k / 4)]
  exact h2 _ (hw (k / 4)) _ (Nat.mod_lt _ (by norm_num))

/-- **Rule `106` is its own next level**: at every scale `m`, the `m`-fold renormalization of a
staying window stays, and `4 ^ m * n` steps of it equal the `m`-fold renormalization of the
`n`-th iterate. -/
theorem renorm_pow_window106_iterate_of (h1 : Rule106RenormIff) (h2 : Rule106RunsRenorm)
    {w : ℕ → ZMod 2} (hw : Rule106Stays w) (m n : ℕ) :
    Rule106Stays (renorm^[m] w) ∧
      window106^[4 ^ m * n] (renorm^[m] w) = renorm^[m] (window106^[n] w) := by
  induction m generalizing w n with
  | zero => exact ⟨hw, by simp⟩
  | succ m ih =>
    have hs := rule106Stays_renorm_of h1 h2 hw
    obtain ⟨h3, h4⟩ := ih hs (4 * n)
    refine ⟨by rw [Function.iterate_succ_apply]; exact h3, ?_⟩
    rw [Function.iterate_succ_apply, show 4 ^ (m + 1) * n = 4 ^ m * (4 * n) by ring, h4,
      (renorm_window106_iterate_iff_of h1 w).mpr hw n, Function.iterate_succ_apply]

/-- **The orbit of the pair stays.** -/
theorem rule106Stays_pair : Rule106Stays (pairLattice {0}) :=
  fun n => (orbit_joint n).1.2.2

/-- **The identity is met with content at the pair**: the orbit of the pair stays, and at
`m = 1`, `n = 6` both sides of the identity are the pair lattice of `{0, 1}`, cells `0`, `1`, `6`
and `7`, while the sixth iterate of the pair has cells `0`, `1`, `3` and `4` set. -/
theorem renorm_pow_window106_iterate_nonvacuous :
    Rule106Stays (pairLattice {0}) ∧
      window106^[24] (renorm (pairLattice {0})) = pairLattice {0, 1} ∧
      renorm (window106^[6] (pairLattice {0})) = pairLattice {0, 1} ∧
      (∀ j, window106^[6] (pairLattice {0}) j = if j ∈ ({0, 1, 3, 4} : Finset ℕ) then 1 else 0) ∧
      (∀ j, pairLattice {0, 1} j = if j ∈ ({0, 1, 6, 7} : Finset ℕ) then 1 else 0) := by
  have h24 : window106^[24] (pairLattice {0}) = pairLattice {0, 1} := by
    have := rule106Step24 {0}
    simpa using this
  have hr : renorm (window106^[6] (pairLattice {0})) = pairLattice {0, 1} := by
    rw [← h24, show (24 : ℕ) = 4 * 6 by norm_num]
    exact ((orbit_joint 6).2).symm
  have o6 : window106^[6] (pairLattice {0}) = blockLattice 12 {0, 1, 3, 4} {0} := by
    rw [orbit_block 6 (by decide)]
    rw [show (blockStep 12)^[6] ({0, 1} : Finset ℕ) = {0, 1, 3, 4} from by decide]
  refine ⟨rule106Stays_pair, ?_, hr, fun j => ?_, fun j => ?_⟩
  · rw [renorm_pair, h24]
  · rw [o6]
    by_cases hj : j < 12
    · interval_cases j <;> decide +kernel
    · rw [blockLattice_big (by omega), ite_eq_right]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  · unfold pairLattice
    apply if_congr _ rfl rfl
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- **The run condition at the start is not enough for the tower**: at the window whose set cells
are `0`, `1`, `2`, `3` and `5`, the run condition holds, its successor fails it (a run of two at
cells `4` and `5`), and the two sides of the identity at `m = 1`, `n = 2` differ at cell `12`,
clear on the left and set on the right. -/
theorem not_renorm_window106_eight (w : ℕ → ZMod 2)
    (hw : ∀ j, w j = if j ∈ ({0, 1, 2, 3, 5} : Finset ℕ) then 1 else 0) :
    Rule106Runs w ∧ ¬ Rule106Runs (window106 w) ∧
      window106^[8] (renorm w) 12 = 0 ∧ renorm (window106^[2] w) 12 = 1 := by
  obtain rfl : w = fun j => if j ∈ ({0, 1, 2, 3, 5} : Finset ℕ) then 1 else 0 := funext hw
  refine ⟨?_, fun h => ?_, by decide +kernel, by decide +kernel⟩
  · intro j h0 h1 h2
    by_cases hj : j < 8
    · interval_cases j <;> revert h0 h1 h2 <;> decide
    · exfalso
      have hn : ¬ (j + 1 = 0 ∨ j + 1 = 1 ∨ j + 1 = 2 ∨ j + 1 = 3 ∨ j + 1 = 5) := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton, hn, ite_false] at h1
      exact absurd h1 (by decide)
  · have := h 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    exact absurd this (by decide)

/-! ## The two statements, proved -/

private theorem classZ_ex_of_runs {w : ℕ → ZMod 2} (hw : Rule106Runs w) : ClassZ (ex w) := by
  intro k h0 h1 h2
  by_cases hk : k < -1
  · rw [ex_neg _ (by omega)] at h1
    exact absurd h1 (by decide)
  · by_cases hk' : k = -1
    · omega
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
      rw [ex_natCast] at h0
      rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, ex_natCast] at h1
      rw [show ((j : ℤ) + 2) = ((j + 2 : ℕ) : ℤ) by push_cast; ring, ex_natCast] at h2
      have := hw j h0 h1 h2
      omega

/-- **One step renormalizes at every window with the run condition**: four steps of `window106`
after the renormalization equal the renormalization after one step, with no condition on the
cells `0` and `1`. -/
theorem renorm_window106_four_of_runs {w : ℕ → ZMod 2} (hw : Rule106Runs w) :
    window106^[4] (renorm w) = renorm (window106 w) := by
  funext q
  have h := local_four_all (classZ_ex_of_runs hw) q
  rw [← ex_natCast (window106^[4] (renorm w)) q, ← ex_natCast (renorm (window106 w)) q,
    ex_iterate, ex_renorm, ex_renorm, ex_window106]
  exact h

/-- **The renormalization and up to three steps keep the run condition**, at every window with
the run condition. -/
theorem rule106RunsRenorm : Rule106RunsRenorm := by
  intro w hw r hr j h0 h1 h2
  have hc := classZ_iterate (classZ_ex_of_runs hw) hr
  rw [← ex_renorm, ← ex_iterate] at hc
  have := hc j (by rw [ex_natCast]; exact h0)
    (by rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, ex_natCast]; exact h1)
    (by rw [show ((j : ℤ) + 2) = ((j + 2 : ℕ) : ℤ) by push_cast; ring, ex_natCast]; exact h2)
  omega

/-- The earliest violation of the run condition, with the condition holding below it on the
window extended by clear cells. -/
private theorem exists_first_violation {w : ℕ → ZMod 2} (hn : ¬ Rule106Runs w) :
    ∃ j : ℕ, (w j = 0 ∧ w (j + 1) = 1 ∧ w (j + 2) = 1 ∧ (j + 1) % 3 ≠ 0) ∧
      ∀ k : ℤ, k < j → ex w k = 0 → ex w (k + 1) = 1 → ex w (k + 2) = 1 → (k + 1) % 3 = 0 := by
  classical
  have hex : ∃ j : ℕ, w j = 0 ∧ w (j + 1) = 1 ∧ w (j + 2) = 1 ∧ (j + 1) % 3 ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hn hne
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro k hk h0 h1 h2
  by_cases hk1 : k < -1
  · rw [ex_neg _ (by omega)] at h1
    exact absurd h1 (by decide)
  · by_cases hk2 : k = -1
    · omega
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
      rw [ex_natCast] at h0
      rw [show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring, ex_natCast] at h1
      rw [show ((i : ℤ) + 2) = ((i + 2 : ℕ) : ℤ) by push_cast; ring, ex_natCast] at h2
      by_contra hm
      exact Nat.find_min hex (show i < Nat.find hex by omega) ⟨h0, h1, h2, by omega⟩

set_option synthInstance.maxSize 1000 in
private theorem local_bad_one (G : ℤ → ZMod 2)
    (c : ∀ k : ℤ, k < 0 → G k = 0 → G (k + 1) = 1 → G (k + 2) = 1 → (k + 1) % 3 = 0)
    (g0 : G 0 = 0) (g1 : G 1 = 1) (g2 : G 2 = 1) :
    stepZ^[4] (renormZ G) 6 ≠ renormZ (stepZ G) 6 := by
  have c3 := c (-5) (by norm_num)
  have c4 := c (-4) (by norm_num)
  have c5 := c (-3) (by norm_num)
  have c6 := c (-2) (by norm_num)
  have c7 := c (-1) (by norm_num)
  simp only [stepZ, renormZ, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    Int.reduceAdd, Int.reduceSub, Int.reduceMod, Int.reduceDiv, Int.reduceNeg, ↓reduceIte]
    at c3 c4 c5 c6 c7 ⊢
  clear c
  all_goals generalize G (-5) = x0 at *
  all_goals generalize G (-4) = x1 at *
  all_goals generalize G (-3) = x2 at *
  all_goals generalize G (-2) = x3 at *
  all_goals generalize G (-1) = x4 at *
  all_goals generalize G 0 = x5 at *
  all_goals generalize G 1 = x6 at *
  all_goals generalize G 2 = x7 at *
  all_goals generalize G 3 = x8 at *
  all_goals generalize G 4 = x9 at *
  all_goals revert c3 c4 c5 c6 c7 g0 g1 g2
  all_goals revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
  all_goals decide +kernel

set_option synthInstance.maxSize 1000 in
private theorem local_bad_two (G : ℤ → ZMod 2)
    (c : ∀ k : ℤ, k < 1 → G k = 0 → G (k + 1) = 1 → G (k + 2) = 1 → (k + 1) % 3 = 0)
    (g1 : G 1 = 0) (g2 : G 2 = 1) (g3 : G 3 = 1) :
    stepZ^[4] (renormZ G) 7 ≠ renormZ (stepZ G) 7 := by
  have c3 := c (-5) (by norm_num)
  have c4 := c (-4) (by norm_num)
  have c5 := c (-3) (by norm_num)
  have c6 := c (-2) (by norm_num)
  have c7 := c (-1) (by norm_num)
  have c8 := c 0 (by norm_num)
  simp only [stepZ, renormZ, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    Int.reduceAdd, Int.reduceSub, Int.reduceMod, Int.reduceDiv, Int.reduceNeg, ↓reduceIte]
    at c3 c4 c5 c6 c7 c8 ⊢
  clear c
  all_goals generalize G (-5) = x0 at *
  all_goals generalize G (-4) = x1 at *
  all_goals generalize G (-3) = x2 at *
  all_goals generalize G (-2) = x3 at *
  all_goals generalize G (-1) = x4 at *
  all_goals generalize G 0 = x5 at *
  all_goals generalize G 1 = x6 at *
  all_goals generalize G 2 = x7 at *
  all_goals generalize G 3 = x8 at *
  all_goals generalize G 4 = x9 at *
  all_goals generalize G 5 = x10 at *
  all_goals revert c3 c4 c5 c6 c7 c8 g1 g2 g3
  all_goals revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  all_goals decide +kernel

/-- A difference of the two sides at the shifted window is a difference at the original. -/
private theorem ne_of_local {w : ℕ → ZMod 2} (a r : ℕ)
    (h : stepZ^[4] (renormZ (shiftZ (3 * (a : ℤ)) (ex w))) r ≠
      renormZ (stepZ (shiftZ (3 * (a : ℤ)) (ex w))) r) :
    window106^[4] (renorm w) ≠ renorm (window106 w) := by
  intro e
  apply h
  rw [stepZ_renormZ_shift, stepZ_shift, renormZ_shift]
  simp only [shiftZ]
  have := congrFun e (6 * a + r)
  rw [← ex_natCast (window106^[4] (renorm w)) _, ← ex_natCast (renorm (window106 w)) _,
    ex_iterate, ex_renorm, ex_renorm, ex_window106] at this
  push_cast at this
  exact this

/-- **One step renormalizes exactly on the run condition**: four steps of `window106` after the
renormalization equal the renormalization after one step if and only if every run of two or more
set cells starts at a multiple of `3`. -/
theorem rule106RenormIff : Rule106RenormIff := by
  intro w
  refine ⟨fun h => ?_, fun hr => renorm_window106_four_of_runs hr⟩
  by_contra hn
  obtain ⟨j, ⟨b0, b1, b2, b3⟩, hmin⟩ := exists_first_violation hn
  have hcases : (j + 1) % 3 = 1 ∨ (j + 1) % 3 = 2 := by omega
  rcases hcases with hc | hc
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, j = 3 * a := ⟨(j + 1) / 3, by omega⟩
    refine ne_of_local a 6 (local_bad_one _ ?_ ?_ ?_ ?_) h
    · intro k hk h0 h1 h2
      simp only [shiftZ] at h0 h1 h2
      rw [show 3 * (a : ℤ) + (k + 1) = 3 * a + k + 1 by ring] at h1
      rw [show 3 * (a : ℤ) + (k + 2) = 3 * a + k + 2 by ring] at h2
      have := hmin (3 * a + k) (by push_cast; omega) h0 h1 h2
      omega
    · simp only [shiftZ]
      rw [show 3 * (a : ℤ) + 0 = ((3 * a : ℕ) : ℤ) by push_cast; ring, ex_natCast]
      exact b0
    · simp only [shiftZ]
      rw [show 3 * (a : ℤ) + 1 = ((3 * a + 1 : ℕ) : ℤ) by push_cast; ring, ex_natCast]
      exact b1
    · simp only [shiftZ]
      rw [show 3 * (a : ℤ) + 2 = ((3 * a + 2 : ℕ) : ℤ) by push_cast; ring, ex_natCast]
      exact b2
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, j = 3 * a + 1 := ⟨(j + 1) / 3, by omega⟩
    refine ne_of_local a 7 (local_bad_two _ ?_ ?_ ?_ ?_) h
    · intro k hk h0 h1 h2
      simp only [shiftZ] at h0 h1 h2
      rw [show 3 * (a : ℤ) + (k + 1) = 3 * a + k + 1 by ring] at h1
      rw [show 3 * (a : ℤ) + (k + 2) = 3 * a + k + 2 by ring] at h2
      have := hmin (3 * a + k) (by push_cast; omega) h0 h1 h2
      omega
    · simp only [shiftZ]
      rw [show 3 * (a : ℤ) + 1 = ((3 * a + 1 : ℕ) : ℤ) by push_cast; ring, ex_natCast]
      exact b0
    · simp only [shiftZ]
      rw [show 3 * (a : ℤ) + 2 = ((3 * a + 1 + 1 : ℕ) : ℤ) by push_cast; ring, ex_natCast]
      exact b1
    · simp only [shiftZ]
      rw [show 3 * (a : ℤ) + 3 = ((3 * a + 1 + 2 : ℕ) : ℤ) by push_cast; ring, ex_natCast]
      exact b2

/-- **Along an orbit, with no hypothesis left**: four steps commute with the renormalization at
every `n` exactly when the orbit of the window stays. -/
theorem renorm_window106_iterate_iff (w : ℕ → ZMod 2) :
    (∀ n, window106^[4 * n] (renorm w) = renorm (window106^[n] w)) ↔ Rule106Stays w :=
  renorm_window106_iterate_iff_of rule106RenormIff w

/-- **The renormalization of a staying window stays**, with no hypothesis left. -/
theorem rule106Stays_renorm {w : ℕ → ZMod 2} (hw : Rule106Stays w) :
    Rule106Stays (renorm w) :=
  rule106Stays_renorm_of rule106RenormIff rule106RunsRenorm hw

/-- **Rule `106` is its own next level, with no hypothesis left**: at every scale `m`, the
`m`-fold renormalization of a staying window stays, and `4 ^ m * n` steps of it equal the
`m`-fold renormalization of the `n`-th iterate. -/
theorem renorm_pow_window106_iterate {w : ℕ → ZMod 2} (hw : Rule106Stays w) (m n : ℕ) :
    Rule106Stays (renorm^[m] w) ∧
      window106^[4 ^ m * n] (renorm^[m] w) = renorm^[m] (window106^[n] w) :=
  renorm_pow_window106_iterate_of rule106RenormIff rule106RunsRenorm hw m n

/-- **The backward direction has content**: at the window with cells `0`, `2` and `3` set, the
run at `2` starts off phase, the run condition fails, and the two sides of the identity differ at
cell `7`, clear on the left and set on the right; at the window with cells `0`, `3` and `4` set,
the run at `3` starts on phase, the run condition holds, and the identity holds. -/
theorem rule106RenormIff_nonvacuous (w v : ℕ → ZMod 2)
    (hw : ∀ j, w j = if j ∈ ({0, 2, 3} : Finset ℕ) then 1 else 0)
    (hv : ∀ j, v j = if j ∈ ({0, 3, 4} : Finset ℕ) then 1 else 0) :
    ¬ Rule106Runs w ∧ window106^[4] (renorm w) 7 = 0 ∧ renorm (window106 w) 7 = 1 ∧
      Rule106Runs v ∧ window106^[4] (renorm v) = renorm (window106 v) := by
  obtain rfl : w = fun j => if j ∈ ({0, 2, 3} : Finset ℕ) then 1 else 0 := funext hw
  obtain rfl : v = fun j => if j ∈ ({0, 3, 4} : Finset ℕ) then 1 else 0 := funext hv
  have hr : Rule106Runs (fun j => if j ∈ ({0, 3, 4} : Finset ℕ) then 1 else 0) := by
    intro j h0 h1 h2
    by_cases hj : j < 5
    · interval_cases j <;> revert h0 h1 h2 <;> decide
    · exfalso
      have hn : ¬ (j + 1 = 0 ∨ j + 1 = 3 ∨ j + 1 = 4) := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton, hn, ite_false] at h1
      exact absurd h1 (by decide)
  refine ⟨fun h => ?_, by decide +kernel, by decide +kernel, hr,
    rule106RenormIff _ |>.mpr hr⟩
  have := h 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide)

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_window106_iterate_iff_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_window106_iterate_iff_of

set_option linter.style.longLine false in
/-- info: 'ECA.rule106Stays_renorm_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106Stays_renorm_of

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_pow_window106_iterate_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_pow_window106_iterate_of

set_option linter.style.longLine false in
/-- info: 'ECA.rule106Stays_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106Stays_pair

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_pow_window106_iterate_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_pow_window106_iterate_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_renorm_window106_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_renorm_window106_eight

set_option linter.style.longLine false in
/-- info: 'ECA.rule106RenormIff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106RenormIff

set_option linter.style.longLine false in
/-- info: 'ECA.rule106RunsRenorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106RunsRenorm

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_window106_iterate_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_window106_iterate_iff

set_option linter.style.longLine false in
/-- info: 'ECA.rule106Stays_renorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106Stays_renorm

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_pow_window106_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_pow_window106_iterate

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_window106_four_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_window106_four_of_runs

set_option linter.style.longLine false in
/-- info: 'ECA.rule106RenormIff_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106RenormIff_nonvacuous

end ECA
