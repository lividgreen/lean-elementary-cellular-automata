module

public import ECA.Rule106
public import ErgodicTheory.EdgePeriods
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Rule `106`'s window map as a triangular system: the periods of its prefixes
([RuleSpace] §5)

Rule `106` acts on the window of a state, read from its leftmost set cell, by the window map of
Proposition 5.22, `window106`: cell `j` of the image is `w j + w (j - 2) * w (j - 1)`, a cell
below `0` being clear. Cell `j` is rewritten as itself plus a function of the cells below `j`, so
the window map is a triangular system over the two-element field. The engine for such systems
is the classical package's, `EdgePeriods` in `ErgodicTheory/EdgePeriods.lean`: for a start `w`,
the cells below `m` return at a least positive time, the prefix period, and the prefix period at
width `m + 1` is the period at width `m` or twice it, the cell `m` gaining one over a period
exactly at a doubling. This module is the instance at `window106` and a corollary of it. Rowland
(2006, §4) lists rule `106` by name among the right bijective rules at which the prefix periods
are powers of two, so the instance restates his sentence at the window map; the corollary, the
copies test, is stated here.

For a start `w` and a state `c` that agrees with `w` below the width `m` and differs from it at
cell `m`, reached by some iterate of the window map on the cells below `m + 1`, the period at
width `m + 1` is the doubling of the period at width `m`, and the time is an odd multiple of the
period at width `m`. A state is never reached sooner than this: it is on the orbit of `w`, below
that width, only after the cells below `m` have gone round an odd number of times. The statements
are about the window map; the link from an orbit of the rule to its window is Proposition 5.22's.

## Main results

* `readBelow106` / `readsBelow_readBelow106` / `window106_eq_triangularStep` — the product of cells
  `j - 2` and `j - 1`, the fact that it reads below `j`, and the window map as the triangular step
  of it.
* `prefixPeriod106` — the prefix period of the window map at a start `w` and a width `m`.
* `window106_iterate_eq_of_add_prefixPeriod106` / `prefixPeriod106_succ_eq_or_eq_two_mul` /
  `prefixPeriod106_eq_two_pow` / `window106_iterate_apply_add_prefixPeriod106_of_eq_two_mul` — the
  engine's statements at the window map: the cells below `m` repeat with the period, the period at
  width `m + 1` is the period at width `m` or twice it, every period is a power of two, and at a
  doubling the cell `m` gains one over a period.
* `prefixPeriod106_succ_eq_two_mul_of_agree` / `mod_two_mul_prefixPeriod106_eq_of_agree` — **the
  copies test**: a state agreeing with the start below the width `m`, differing from it at cell
  `m` and reached on the cells below `m + 1` forces the doubling at width `m + 1`, and the time
  leaves remainder the period at width `m` on division by twice that period;
  `mod_two_mul_prefixPeriod106_eq_of_agree_nonvacuous` — the three hypotheses at once, at the
  start with cells `0` to `4` set, width `3` and time `2`.
-/

@[expose] public section

namespace ECA

/-! ## The window map as a triangular system -/

/-- **Rule `106`'s read below**: the product of cells `j − 2` and `j − 1`, a cell below `0`
clear. -/
def readBelow106 : ℕ → (ℕ → ZMod 2) → ZMod 2 :=
  fun j w => (if 2 ≤ j then w (j - 2) else 0) * (if 1 ≤ j then w (j - 1) else 0)

theorem readsBelow_readBelow106 : EdgePeriods.ReadsBelow readBelow106 := by
  intro j u v h
  unfold readBelow106
  congr 1
  · split_ifs with h2
    · exact h (j - 2) (by omega)
    · rfl
  · split_ifs with h1
    · exact h (j - 1) (by omega)
    · rfl

theorem window106_eq_triangularStep : window106 = EdgePeriods.triangularStep readBelow106 :=
  rfl

/-! ## The prefix periods of the window map -/

/-- **The prefix period of rule `106`'s window map** at a start `w` and a width `m`. -/
noncomputable def prefixPeriod106 (w : ℕ → ZMod 2) (m : ℕ) : ℕ :=
  EdgePeriods.prefixPeriod readsBelow_readBelow106 w m

/-- **The cells below `m` repeat with the prefix period** of the window map. -/
theorem window106_iterate_eq_of_add_prefixPeriod106 (w : ℕ → ZMod 2) (m t : ℕ) :
    ∀ i, i < m → window106^[t + prefixPeriod106 w m] w i = window106^[t] w i := by
  rw [window106_eq_triangularStep]
  exact EdgePeriods.iterate_eq_of_add_prefixPeriod readsBelow_readBelow106 w m t

/-- **The dichotomy** at the window map: the prefix period at width `m + 1` is the period at width
`m` or twice it. -/
theorem prefixPeriod106_succ_eq_or_eq_two_mul (w : ℕ → ZMod 2) (m : ℕ) :
    prefixPeriod106 w (m + 1) = prefixPeriod106 w m ∨
      prefixPeriod106 w (m + 1) = 2 * prefixPeriod106 w m :=
  EdgePeriods.prefixPeriod_succ_eq_or_eq_two_mul readsBelow_readBelow106 w m

/-- **Every prefix period of the window map is a power of two.** -/
theorem prefixPeriod106_eq_two_pow (w : ℕ → ZMod 2) (m : ℕ) :
    ∃ k : ℕ, prefixPeriod106 w m = 2 ^ k :=
  EdgePeriods.prefixPeriod_eq_two_pow readsBelow_readBelow106 w m

/-- **The complement** at a doubling: the cell `m` after one prefix period of the cells below it is
the complement of the cell before, at every time. -/
theorem window106_iterate_apply_add_prefixPeriod106_of_eq_two_mul (w : ℕ → ZMod 2) (m : ℕ)
    (h : prefixPeriod106 w (m + 1) = 2 * prefixPeriod106 w m) (t : ℕ) :
    window106^[t + prefixPeriod106 w m] w m = window106^[t] w m + 1 := by
  rw [window106_eq_triangularStep]
  exact EdgePeriods.apply_add_prefixPeriod_of_eq_two_mul readsBelow_readBelow106 w m h t

/-! ## The copies test -/

/-- Over `k` prefix periods of the cells below `m`, the cell `m` is unmoved when the period does not
grow. -/
private theorem window106_iterate_apply_mul_prefixPeriod106_of_eq (w : ℕ → ZMod 2) (m : ℕ)
    (h : prefixPeriod106 w (m + 1) = prefixPeriod106 w m) (k : ℕ) :
    window106^[k * prefixPeriod106 w m] w m = w m := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_mul, Nat.one_mul, window106_eq_triangularStep]
      rw [window106_eq_triangularStep] at ih
      exact (EdgePeriods.apply_add_prefixPeriod_of_eq readsBelow_readBelow106 w m h _).trans ih

/-- Over `k` prefix periods of the cells below `m`, the cell `m` has gained `k` when the period
doubles. -/
private theorem window106_iterate_apply_mul_prefixPeriod106_of_eq_two_mul (w : ℕ → ZMod 2)
    (m : ℕ) (h : prefixPeriod106 w (m + 1) = 2 * prefixPeriod106 w m) (k : ℕ) :
    window106^[k * prefixPeriod106 w m] w m = w m + (k : ZMod 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_mul, Nat.one_mul,
        window106_iterate_apply_add_prefixPeriod106_of_eq_two_mul w m h, ih, Nat.cast_succ,
        add_assoc]

/-- A state agreeing with the start below `m` and reached on the cells below `m + 1` is reached at
a multiple of the prefix period at width `m`. -/
private theorem prefixPeriod106_dvd_of_agree {w c : ℕ → ZMod 2} {m t : ℕ}
    (hb : ∀ i, i < m → c i = w i) (ht : ∀ i, i < m + 1 → window106^[t] w i = c i) :
    prefixPeriod106 w m ∣ t := by
  unfold prefixPeriod106
  rw [window106_eq_triangularStep] at ht
  refine EdgePeriods.prefixPeriod_dvd_of_return readsBelow_readBelow106 w m ?_
  intro i hi
  rw [ht i (Nat.lt_succ_of_lt hi), hb i hi]

/-- **The copies test, the doubling**: a state `c` agreeing with the start `w` below the width `m`
and differing from it at cell `m`, reached by an iterate of the window map on the cells below
`m + 1`, forces the prefix period at width `m + 1` to be twice the period at width `m`. -/
theorem prefixPeriod106_succ_eq_two_mul_of_agree {w c : ℕ → ZMod 2} {m t : ℕ}
    (hb : ∀ i, i < m → c i = w i) (hm : c m ≠ w m)
    (ht : ∀ i, i < m + 1 → window106^[t] w i = c i) :
    prefixPeriod106 w (m + 1) = 2 * prefixPeriod106 w m := by
  obtain ⟨k, hk⟩ := prefixPeriod106_dvd_of_agree hb ht
  rcases prefixPeriod106_succ_eq_or_eq_two_mul w m with h | h
  · exfalso
    apply hm
    rw [← ht m (Nat.lt_succ_self m), hk, Nat.mul_comm]
    exact window106_iterate_apply_mul_prefixPeriod106_of_eq w m h k
  · exact h

/-- **The copies test, the time**: under the same hypotheses the time is an odd multiple of the
prefix period at width `m`, so it leaves remainder that period on division by twice it. -/
theorem mod_two_mul_prefixPeriod106_eq_of_agree {w c : ℕ → ZMod 2} {m t : ℕ}
    (hb : ∀ i, i < m → c i = w i) (hm : c m ≠ w m)
    (ht : ∀ i, i < m + 1 → window106^[t] w i = c i) :
    t % (2 * prefixPeriod106 w m) = prefixPeriod106 w m := by
  have hdouble := prefixPeriod106_succ_eq_two_mul_of_agree hb hm ht
  have hQ : 0 < prefixPeriod106 w m := by
    unfold prefixPeriod106
    exact EdgePeriods.prefixPeriod_pos readsBelow_readBelow106 w m
  obtain ⟨k, hk⟩ := prefixPeriod106_dvd_of_agree hb ht
  have hcell : c m = w m + (k : ZMod 2) := by
    rw [← ht m (Nat.lt_succ_self m), hk, Nat.mul_comm]
    exact window106_iterate_apply_mul_prefixPeriod106_of_eq_two_mul w m hdouble k
  have hk1 : (k : ZMod 2) = 1 := by
    rcases Nat.even_or_odd k with he | ho
    · exact (hm (by rw [hcell, ZMod.natCast_eq_zero_iff_even.mpr he, add_zero])).elim
    · exact ZMod.natCast_eq_one_iff_odd.mpr ho
  obtain ⟨j, hj⟩ := ZMod.natCast_eq_one_iff_odd.mp hk1
  have ht' : t = prefixPeriod106 w m + 2 * prefixPeriod106 w m * j := by
    rw [hk, hj]; ring
  rw [ht', Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- **The three hypotheses of the copies test at once**: the start with cells `0` to `4` set, the
state with cells `0` to `2` set, the width `3` and the time `2`. The state agrees with the start
below cell `3`, differs from it at cell `3`, and is the second iterate of the window map on the
cells below `4`. -/
theorem mod_two_mul_prefixPeriod106_eq_of_agree_nonvacuous :
    (∀ i, i < 3 → (fun j : ℕ => if j < 3 then (1 : ZMod 2) else 0) i =
        (fun j : ℕ => if j < 5 then (1 : ZMod 2) else 0) i) ∧
      (fun j : ℕ => if j < 3 then (1 : ZMod 2) else 0) 3 ≠
        (fun j : ℕ => if j < 5 then (1 : ZMod 2) else 0) 3 ∧
      ∀ i, i < 3 + 1 → window106^[2] (fun j : ℕ => if j < 5 then (1 : ZMod 2) else 0) i =
        (fun j : ℕ => if j < 3 then (1 : ZMod 2) else 0) i :=
  ⟨by decide, by decide, by decide⟩

end ECA

/-- info: 'ECA.readsBelow_readBelow106' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.readsBelow_readBelow106

/-- info: 'ECA.window106_eq_triangularStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_eq_triangularStep

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_eq_of_add_prefixPeriod106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_eq_of_add_prefixPeriod106

set_option linter.style.longLine false in
/-- info: 'ECA.prefixPeriod106_succ_eq_or_eq_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.prefixPeriod106_succ_eq_or_eq_two_mul

set_option linter.style.longLine false in
/-- info: 'ECA.prefixPeriod106_eq_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.prefixPeriod106_eq_two_pow

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_apply_add_prefixPeriod106_of_eq_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_apply_add_prefixPeriod106_of_eq_two_mul

set_option linter.style.longLine false in
/-- info: 'ECA.prefixPeriod106_succ_eq_two_mul_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.prefixPeriod106_succ_eq_two_mul_of_agree

set_option linter.style.longLine false in
/-- info: 'ECA.mod_two_mul_prefixPeriod106_eq_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.mod_two_mul_prefixPeriod106_eq_of_agree

set_option linter.style.longLine false in
/-- info: 'ECA.mod_two_mul_prefixPeriod106_eq_of_agree_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.mod_two_mul_prefixPeriod106_eq_of_agree_nonvacuous
