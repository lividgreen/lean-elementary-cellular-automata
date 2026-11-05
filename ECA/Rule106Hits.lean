module

public import ECA.Rule106Level
import all ECA.Rule106
import all ECA.Rule106Level

/-!
# Rule `106` against a hit: the level reading at every host time
([RuleSpace] §5)

The level reading at height `m` samples a window at the cells `renormCell^[m] j`.
A hit at a cell `c` is the window plus a single set cell at `c`.
This file shows that the reading is blind to the phase of the host, that it follows the host's
level step at every host time, and that a hit is seen or unseen according to whether it lands on a
sampled cell.

## Main results

* `window106_iterate_renorm_renormCell` — at every window and every `r < 4`, `r` steps after the
  renormalization, read at the sampled cell `renormCell j`, return the cell `j` of the window:
  the phase of the host is invisible to the reading;
  `not_window106_four_renorm_renormCell` — four steps are too many.
* `window106_iterate_renorm_pow_renormCell` — on a staying window, at every height `m` and every
  host time `t`, the reading of `window106^[t]` of the `m`-fold renormalization at the sampled cells
  is the reading of the window after `t / 4 ^ m` steps;
  `not_window106_iterate_renorm_renormCell_eight` — the staying hypothesis is needed.
* `window106_iterate_add_single` — a hit at `c` changes no cell below `c` and changes the cell `c`,
  at every window and every time; `window106_iterate_add_single_renormCell_ne` — a hit on a sampled
  cell is seen at every time.
* `renormCell_ne_two_five` — cells `2` and `5` are not sampled; `window106_unseen_hit` — the hit at
  cell `2` on the renormalized successor of the pair is unseen at every level step;
  `window106_seen_hit` — the hit at cell `5` on the renormalized third iterate of the pair is seen
  at level step one.
-/

@[expose] public section

namespace ECA

private theorem local_phase (G : ℤ → ZMod 2) (r : ℕ) (hr : r < 4) :
    stepZ^[r] (renormZ G) 0 = G 0 ∧ stepZ^[r] (renormZ G) 1 = G 1 ∧
      stepZ^[r] (renormZ G) 4 = G 2 := by
  interval_cases r <;>
  simp only [stepZ, renormZ, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    Int.reduceAdd, Int.reduceSub, Int.reduceMod, Int.reduceDiv, Int.reduceNeg,
    Int.reduceEq, ↓reduceIte]
  all_goals try simp only [and_self]
  all_goals generalize G (-3) = x0
  all_goals generalize G (-2) = x1
  all_goals generalize G (-1) = x2
  all_goals generalize G 0 = x3
  all_goals generalize G 1 = x4
  all_goals generalize G 2 = x5
  all_goals revert x0 x1 x2 x3 x4 x5
  all_goals decide +kernel

/-- **The reading is blind to the phase of the host**: at every window, `r < 4` steps after the
renormalization, read at the sampled cell `renormCell j`, return the cell `j` of the window. -/
theorem window106_iterate_renorm_renormCell (w : ℕ → ZMod 2) {r : ℕ} (hr : r < 4) (j : ℕ) :
    window106^[r] (renorm w) (renormCell j) = w j := by
  obtain ⟨a, p, hp, rfl⟩ : ∃ a p : ℕ, p < 3 ∧ j = 3 * a + p := ⟨j / 3, j % 3, by omega, by omega⟩
  have e : ex w = shiftZ (3 * (-(a : ℤ))) (fun k => ex w (3 * a + k)) := by
    funext k; simp only [shiftZ]; congr 1; ring
  have key := stepZ_renormZ_shift r (-(a : ℤ)) (fun k => ex w (3 * a + k))
  rw [← e] at key
  have lp := local_phase (fun k => ex w (3 * a + k)) r hr
  have hl : window106^[r] (renorm w) (renormCell (3 * a + p)) =
      stepZ^[r] (renormZ (ex w)) ((renormCell (3 * a + p) : ℕ) : ℤ) := by
    rw [← ex_natCast (window106^[r] (renorm w)), ex_iterate, ex_renorm]
  rw [hl, key]
  simp only [shiftZ]
  interval_cases p
  · have : ((renormCell (3 * a + 0) : ℕ) : ℤ) = 6 * a + 0 := by unfold renormCell; push_cast; omega
    rw [this, show 6 * -(a : ℤ) + (6 * a + 0) = 0 by ring, lp.1, ← ex_natCast w]
    push_cast; ring_nf
  · have : ((renormCell (3 * a + 1) : ℕ) : ℤ) = 6 * a + 1 := by unfold renormCell; push_cast; omega
    rw [this, show 6 * -(a : ℤ) + (6 * a + 1) = 1 by ring, lp.2.1, ← ex_natCast w]
    push_cast; ring_nf
  · have : ((renormCell (3 * a + 2) : ℕ) : ℤ) = 6 * a + 4 := by unfold renormCell; push_cast; omega
    rw [this, show 6 * -(a : ℤ) + (6 * a + 4) = 4 by ring, lp.2.2, ← ex_natCast w]
    push_cast; ring_nf

/-- **Four steps are too many for the phase**: four steps after the renormalization of the pair,
read at the sampled cell `renormCell 2`, differ from the cell `2` of the pair. -/
theorem not_window106_four_renorm_renormCell :
    window106^[4] (renorm (pairLattice {0})) (renormCell 2) ≠ pairLattice {0} 2 := by
  decide +kernel

/-- **The reading at every host time**: on a staying window, at every height `m` and every host
time `t`, the cell `renormCell^[m] j` of `t` steps of the `m`-fold renormalization is the cell `j`
of the window after `t / 4 ^ m` steps. -/
theorem window106_iterate_renorm_pow_renormCell {w : ℕ → ZMod 2} (hw : Rule106Stays w)
    (m t j : ℕ) :
    window106^[t] (renorm^[m] w) (renormCell^[m] j) = window106^[t / 4 ^ m] w j := by
  induction m generalizing t j with
  | zero => simp
  | succ m ih =>
    have hV : Rule106Stays (renorm^[m] w) := (renorm_pow_window106_iterate hw m 0).1
    obtain ⟨u, s, hs, rfl⟩ : ∃ u s : ℕ, s < 4 ∧ t = s + 4 * u :=
      ⟨t / 4, t % 4, by omega, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_add_apply,
      (renorm_window106_iterate_iff (renorm^[m] w)).mpr hV u,
      window106_iterate_renorm_renormCell _ hs, ih u j]
    have e : (s + 4 * u) / 4 ^ (m + 1) = u / 4 ^ m := by
      rw [pow_succ, mul_comm (4 ^ m) 4, ← Nat.div_div_eq_div_mul,
        show (s + 4 * u) / 4 = u by omega]
    rw [e]

/-- **The staying hypothesis is needed for the reading at every host time**: at the window with
cells `0`, `1`, `2`, `3` and `5` set, eight steps after the renormalization, read at the sampled
cell `renormCell 6 = 12`, differ from the cell `6` of the window after two steps. -/
theorem not_window106_iterate_renorm_renormCell_eight (w : ℕ → ZMod 2)
    (hw : ∀ j, w j = if j ∈ ({0, 1, 2, 3, 5} : Finset ℕ) then 1 else 0) :
    window106^[8] (renorm w) (renormCell 6) ≠ window106^[2] w 6 := by
  have h := not_renorm_window106_eight w hw
  have e : renormCell 6 = 12 := by decide
  have e2 := renorm_renormCell (window106^[2] w) 6
  rw [e] at e2 ⊢
  rw [← e2, h.2.2.1, h.2.2.2]
  decide

/-- **A hit at a cell of a window changes that cell and nothing below it**, at every window and
every time. -/
theorem window106_iterate_add_single (w : ℕ → ZMod 2) (c n : ℕ) :
    (∀ j < c, window106^[n] (w + Pi.single c 1) j = window106^[n] w j) ∧
      window106^[n] (w + Pi.single c 1) c = window106^[n] w c + 1 := by
  induction n with
  | zero =>
    refine ⟨fun j hj => ?_, ?_⟩
    · simp [Nat.ne_of_lt hj]
    · simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have key : ∀ j ≤ c,
        (if 2 ≤ j then window106^[n] (w + Pi.single c 1) (j - 2) else 0) *
          (if 1 ≤ j then window106^[n] (w + Pi.single c 1) (j - 1) else 0) =
        (if 2 ≤ j then window106^[n] w (j - 2) else 0) *
          (if 1 ≤ j then window106^[n] w (j - 1) else 0) := by
      intro j hj
      have a1 : 2 ≤ j → window106^[n] (w + Pi.single c 1) (j - 2) = window106^[n] w (j - 2) :=
        fun h => h1 _ (by omega)
      have a2 : 1 ≤ j → window106^[n] (w + Pi.single c 1) (j - 1) = window106^[n] w (j - 1) :=
        fun h => h1 _ (by omega)
      by_cases b1 : 2 ≤ j <;> by_cases b2 : 1 ≤ j <;> simp [b1, b2, a1, a2]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [window106]
      rw [h1 j hj, key j hj.le]
    · simp only [window106]
      rw [h2, key c le_rfl]
      ring

/-- **A hit on a sampled cell is seen at every time**, at every window. -/
theorem window106_iterate_add_single_renormCell_ne (v : ℕ → ZMod 2) (m j n : ℕ) :
    window106^[n] (v + Pi.single (renormCell^[m] j) 1) (renormCell^[m] j) ≠
      window106^[n] v (renormCell^[m] j) := by
  rw [(window106_iterate_add_single v _ n).2]
  generalize window106^[n] v (renormCell^[m] j) = x
  revert x
  decide

/-- **Cells `2` and `5` are not sampled** by the cell map. -/
theorem renormCell_ne_two_five (j : ℕ) : renormCell j ≠ 2 ∧ renormCell j ≠ 5 := by
  unfold renormCell
  split_ifs <;> omega

/-- The pair has no set cell from `2` on. -/
private theorem pairLattice_zero_ge {i : ℕ} (h : 2 ≤ i) : pairLattice {0} i = 0 := by
  unfold pairLattice
  split_ifs with hc
  · simp only [Finset.mem_singleton] at hc
    omega
  · rfl

/-- The successor of the pair is the window with cells `0`, `1` and `2` set. -/
private theorem window106_pair_apply (j : ℕ) :
    window106 (pairLattice {0}) j = if j ∈ ({0, 1, 2} : Finset ℕ) then 1 else 0 := by
  by_cases hj : j < 8
  · interval_cases j <;> decide +kernel
  · have h2 : j ∉ ({0, 1, 2} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    simp only [window106, pairLattice_zero_ge (by omega : 2 ≤ j),
      pairLattice_zero_ge (by omega : 2 ≤ j - 2), h2, ite_false, ite_self, zero_mul, add_zero]

/-- A hit at cell `2` on the renormalized successor of the pair is the fifth iterate of the pair. -/
private theorem renorm_window106_pair_add_single :
    renorm (window106 (pairLattice {0})) + Pi.single 2 1 = window106^[5] (pairLattice {0}) := by
  funext i
  rw [(renorm_window106_four_nonvacuous).2.1 i]
  by_cases hi : i < 24
  · simp only [renorm, window106_pair_apply, Pi.add_apply]
    interval_cases i <;> decide +kernel
  · have hn : i ∉ ({0, 1, 2, 4} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have h2 : i ≠ 2 := by omega
    have hz : ∀ x, 12 ≤ x → window106 (pairLattice {0}) x = 0 := fun x hx => by
      rw [window106_pair_apply, ite_eq_right_iff]
      intro hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    have h3 : renorm (window106 (pairLattice {0})) i = 0 := by
      simp only [renorm]
      split_ifs <;> first | rfl | (apply hz; omega)
    simp [h3, hn, h2]

/-- **A hit off the sampled cells is unseen at every level step**: the renormalized successor of
the pair, with a hit at cell `2`, and without it, read at the sampled cells after `4 * k` steps,
agree. The hit shifts the host by one step. -/
theorem window106_unseen_hit (k j : ℕ) :
    window106^[4 * k] (renorm (window106 (pairLattice {0})) + Pi.single 2 1) (renormCell j) =
      window106^[4 * k] (renorm (window106 (pairLattice {0}))) (renormCell j) := by
  have hs : Rule106Stays (window106 (pairLattice {0})) := fun n => by
    rw [← Function.iterate_succ_apply]; exact rule106Stays_pair _
  rw [renorm_window106_pair_add_single, (renorm_window106_iterate_iff _).mpr hs k,
    renorm_renormCell, ← Function.iterate_add_apply,
    show 4 * k + 5 = 1 + 4 * (k + 1) by ring, Function.iterate_add_apply,
    (orbit_joint (k + 1)).2, window106_iterate_renorm_renormCell _ (by norm_num : 1 < 4),
    ← Function.iterate_succ_apply]

/-- **A hit on a sampled cell is seen at level step one**: the renormalized third iterate of the
pair, with a hit at cell `5` and without it, read at the sampled cell `renormCell 4 = 7` after four
steps, differ. -/
theorem window106_seen_hit :
    window106^[4] (renorm (window106^[3] (pairLattice {0})) + Pi.single 5 1) (renormCell 4) ≠
      window106^[4] (renorm (window106^[3] (pairLattice {0}))) (renormCell 4) := by
  decide +kernel

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_renorm_renormCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_renorm_renormCell

set_option linter.style.longLine false in
/-- info: 'ECA.not_window106_four_renorm_renormCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_window106_four_renorm_renormCell

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_renorm_pow_renormCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_renorm_pow_renormCell

set_option linter.style.longLine false in
/-- info: 'ECA.not_window106_iterate_renorm_renormCell_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_window106_iterate_renorm_renormCell_eight

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_add_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_add_single

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_add_single_renormCell_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_add_single_renormCell_ne

set_option linter.style.longLine false in
/-- info: 'ECA.renormCell_ne_two_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renormCell_ne_two_five

set_option linter.style.longLine false in
/-- info: 'ECA.window106_unseen_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_unseen_hit

set_option linter.style.longLine false in
/-- info: 'ECA.window106_seen_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_seen_hit

end ECA
