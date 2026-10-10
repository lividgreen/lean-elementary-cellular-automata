/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.RationalRayRule90
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorization.Basic

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Late disjoint pairs on the ray, at every speed strictly between 0 and 1
([RuleSpace] §4 Proposition 4.4)

This file carries the arithmetic of the second condition of `RationalRayRule90`, the late
disjoint pairs on the ray (`LateDisjointOnRay`). It is proved at every speed `p / q` with
`0 < p` and `p < q`, the speed strictly between 0 and 1, in three cases: both terms odd; the
sum `p + q` odd with `3 p < q`; the sum odd with `q < 3 p`. A speed whose terms are both even
reduces to a smaller one. With the first and third conditions of `RationalRayRule90`, the ray of
rule `90` from the single seed is then not eventually periodic at every such speed, from every
cell. No cellular automaton appears in the statements of the arithmetic: the content is pure
arithmetic on `ℕ` and `ℤ`. Registered as [RuleSpace] §5 Proposition 5.1, row RS-11.

The argument has two ingredients. The ray `OnRay` is a strip between two lines in the plane of
pairs (`onRay_iff`). A pair with no shared binary digit on the strip is found at one offset
(`exists_disjoint_onRay_of_odd`: a single-bit hit for a negative offset), and is then pushed past
any step by adding a high copy of a zero pair, a pair of naturals with no shared binary digit
lying exactly on the line of the strip (`exists_zero_pair`, `and_add_shift_eq_zero`).
For odd sum with the speed below one third the pairs are instead taken with first member a
power of two (`onRay_of_dvd`), the offset of the strip being fixed by a residue in a window
(`exists_pow_residue_lt`) and the exponent advanced by multiples of the totient of the sum.
For odd sum with the speed above one third the pair found at one offset has the top binary digit
in its first member (`exists_top_disjoint_onRay`), and is pushed past any step by moving that
digit up by a multiple of the totient of the sum while the second member gains a number that
keeps the strip's quantity fixed (`and_pump_top`).

## Main results

* `onRay_iff` — the ray is the strip `0 ≤ (q + p) b - (q - p) a + q e < q`.
* `exists_zero_pair` — for both terms of the speed odd and `p < q`, a zero pair exists: a
  positive `A` and a `B` with no shared binary digit and `(q + p) B = (q - p) A`;
  `exists_zero_pair_guard` shows the oddness is needed (at `p = 1`, `q = 2` none exists).
* `and_add_shift_eq_zero` — adding a high copy of a pair with no shared binary digit to a low
  pair with none keeps the digits disjoint.
* `exists_single_bit_hit` — a single-bit hit: a power of two `2 ^ r` and a natural `a` with
  bit `r` of `a` zero and `P 2 ^ r - D a` in the window `[w, w + D)`.
* `exists_disjoint_onRay_of_odd` — for both terms of the speed odd, every offset has a pair with
  no shared binary digit on the ray.
* `lateDisjointOnRay_of_odd` — **the second condition holds where both terms of the speed are
  odd and `p < q`**, at every offset; `lateDisjointOnRay_of_odd_nonvacuous` meets the three
  hypotheses at once.
* `onRay_of_dvd` — pairs whose first member is a multiple of a power of two lie on the ray when
  a divisibility and two bounds hold.
* `exists_pow_residue_lt` — for `0 < p` and `3 p < q`, some power of two puts the residue
  `(x - 2 ^ K (q - p)) % (q + p)` below `q`.
* `lateDisjointOnRay_of_three_mul_lt` — **the second condition holds for `0 < p`, `3 p < q` and
  the sum `p + q` odd**, at every offset; `lateDisjointOnRay_of_three_mul_lt_nonvacuous` meets
  the three hypotheses at once.
* `and_pump_top` — moving the top digit of the first member of a pair with no shared binary
  digit up by `n` places, while adding a number below `2 ^ n` shifted above the second member's
  digits, keeps the digits disjoint.
* `exists_single_bit_hit_top` — a single-bit hit with the top digit in the first member.
* `exists_top_disjoint_onRay` — for `0 < p` and `p < q < 3 p`, every offset has a pair with no
  shared binary digit on the ray whose first member has its top digit above the second.
* `lateDisjointOnRay_of_lt_three_mul` — **the second condition holds for `p < q < 3 p` and the
  sum `p + q` odd**, at every offset; `lateDisjointOnRay_of_lt_three_mul_nonvacuous` meets the
  hypotheses at once.
* `lateDisjointOnRay` — **the second condition holds at every speed strictly between 0 and 1**,
  at every offset: strong induction on `p + q`, halving a speed whose terms are both even.
* `exists_late_one_observedRationalRay_f90_single` and
  `not_eventuallyPeriodic_observedRationalRay_f90_single` — **the ray of rule 90 from the single
  seed reads a one past every step and is not eventually periodic, at every speed strictly
  between 0 and 1 and from every cell**; the `_nonvacuous` statement meets both hypotheses at
  speed `1 / 2`; a statement at each end of the speed's range, speed zero and speed one from
  cell `0`, shows the range is needed: there the ray is eventually periodic.
-/

@[expose] public section

namespace RationalRayNinety

/-! ## Piece 1: the strip -/

/-- **The ray is a strip**: `OnRay p q e a b` holds exactly when
`0 ≤ (q + p) b - (q - p) a + q e < q`. -/
theorem onRay_iff (p q : ℕ) (hq : 0 < q) (e : ℤ) (a b : ℕ) :
    OnRay p q e a b ↔
      0 ≤ ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + q * e ∧
        ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + q * e < q := by
  unfold OnRay
  set m : ℕ := p * (a + b) / q with hm
  have h1 : q * m ≤ p * (a + b) := Nat.mul_div_le _ _
  have h2 : p * (a + b) < q * (m + 1) := Nat.lt_mul_div_succ _ hq
  have h1' : (q : ℤ) * m ≤ p * (a + b) := by exact_mod_cast h1
  have h2' : (p : ℤ) * (a + b) < q * (m + 1) := by exact_mod_cast h2
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  constructor
  · intro h
    have hm' : (m : ℤ) = a - b - e := by linarith
    rw [hm'] at h1' h2'
    constructor <;> nlinarith
  · rintro ⟨l, u⟩
    have h3 : (q : ℤ) * ((a : ℤ) - b - e - m) < q * 1 := by nlinarith
    have h4 : (q : ℤ) * ((m : ℤ) - (a - b - e)) < q * 1 := by nlinarith
    have h5 := lt_of_mul_lt_mul_left h3 hq'.le
    have h6 := lt_of_mul_lt_mul_left h4 hq'.le
    omega

/-! ## Piece 2: the zero pair and the pump -/

/-- two naturals summing to `2 ^ m - 1` share no binary digit -/
private theorem and_eq_zero_of_add_eq_two_pow_sub_one (m : ℕ) :
    ∀ A B : ℕ, A + B = 2 ^ m - 1 → A &&& B = 0 := by
  induction m with
  | zero =>
      intro A B h
      have hA : A = 0 := by simp at h; omega
      have hB : B = 0 := by simp at h; omega
      subst hA hB; rfl
  | succ m ih =>
      intro A B h
      have hp : 0 < 2 ^ m := by positivity
      rw [pow_succ] at h
      have hAB : A % 2 = 0 ∧ B % 2 = 1 ∨ A % 2 = 1 ∧ B % 2 = 0 := by omega
      have hih := ih (A / 2) (B / 2) (by omega)
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and]
      cases i with
      | zero =>
          rw [Nat.zero_testBit, Nat.testBit_zero, Nat.testBit_zero]
          rcases hAB with h | h <;> simp [h.1, h.2]
      | succ i =>
          have := congrArg (fun n => n.testBit i) hih
          simp only [Nat.testBit_and, Nat.zero_testBit] at this
          rw [Nat.zero_testBit, Nat.testBit_succ, Nat.testBit_succ]
          exact this

/-- **A zero pair**: where both terms of the speed are odd and `p < q`, there is a positive `A`
and a `B` with no shared binary digit and `(q + p) B = (q - p) A`. -/
theorem exists_zero_pair (p q : ℕ) (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : p < q) :
    ∃ A B : ℕ, 0 < A ∧ A &&& B = 0 ∧ ((q : ℤ) + p) * B = ((q : ℤ) - p) * A := by
  have hcop : Nat.Coprime 2 q := by
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hq)
  have hmod := Nat.ModEq.pow_totient hcop
  have hm0 : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
  set m := Nat.totient q with hm
  have hdvd : q ∣ 2 ^ m - 1 := by
    have := (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hmod.symm
    exact this
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < 2 ^ m - 1 := by
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm0
    omega
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; omega
    · exact h
  have hsum : (q + p) / 2 * k + (q - p) / 2 * k = 2 ^ m - 1 := by
    rw [hk, ← Nat.add_mul]
    congr 1
    omega
  refine ⟨(q + p) / 2 * k, (q - p) / 2 * k, ?_,
    and_eq_zero_of_add_eq_two_pow_sub_one m _ _ hsum, ?_⟩
  · apply Nat.mul_pos _ hk0
    omega
  · have hX : (q : ℤ) + p = 2 * (((q + p) / 2 : ℕ) : ℤ) := by omega
    have hY : (q : ℤ) - p = 2 * (((q - p) / 2 : ℕ) : ℤ) := by omega
    rw [Nat.cast_mul, Nat.cast_mul, hX, hY]
    ring

/-- adding a high copy of a pair with no shared binary digit to a low pair with none keeps the
two digit sets disjoint -/
theorem and_add_shift_eq_zero (a b A B M : ℕ) (ha : a < 2 ^ M) (hb : b < 2 ^ M)
    (hab : a &&& b = 0) (hAB : A &&& B = 0) : (a + 2 ^ M * A) &&& (b + 2 ^ M * B) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [add_comm a, add_comm b, Nat.testBit_and, Nat.testBit_two_pow_mul_add A ha,
    Nat.testBit_two_pow_mul_add B hb, Nat.zero_testBit]
  have h1 := congrArg (fun n => n.testBit i) hab
  have h2 := congrArg (fun n => n.testBit (i - M)) hAB
  simp only [Nat.testBit_and, Nat.zero_testBit] at h1 h2
  split_ifs <;> simp_all

/-- **The oddness is load-bearing for a zero pair**: at `p = 1`, `q = 2` no zero pair exists,
since `A = 3 B` and `3 B` shares the lowest set binary digit of `B`. -/
theorem exists_zero_pair_guard :
    ¬ ∃ A B : ℕ, 0 < A ∧ A &&& B = 0 ∧ ((2 : ℤ) + 1) * B = ((2 : ℤ) - 1) * A := by
  rintro ⟨A, B, hA, hAB, h⟩
  have hA3 : A = 3 * B := by omega
  have hB : B ≠ 0 := by omega
  obtain ⟨s, m, hm, hBm⟩ := Nat.exists_eq_two_pow_mul_odd hB
  have hAm : A = 2 ^ s * (3 * m) := by rw [hA3, hBm]; ring
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have hbit := congrArg (fun n => n.testBit s) hAB
  simp only [Nat.testBit_and, Nat.zero_testBit] at hbit
  rw [hAm, hBm, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos s), Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)]
    at hbit
  have : (3 * m) % 2 = 1 := by omega
  simp [this, hm2] at hbit

/-! ## Piece 3: the single-bit hit -/

/-- **A single-bit hit**: for `0 < D < P` and `D < w`, some power of two `2 ^ r` and some `a`
with bit `r` of `a` zero have `P 2 ^ r - D a` in the window `[w, w + D)`. -/
theorem exists_single_bit_hit (P D w : ℕ) (hD : 0 < D) (hPD : D < P) (hw : D < w) :
    ∃ r a : ℕ, a &&& 2 ^ r = 0 ∧ D * a ≤ P * 2 ^ r ∧
      w ≤ P * 2 ^ r - D * a ∧ P * 2 ^ r - D * a < w + D := by
  set j := (P - 1) / (2 * D) with hj
  set k := 2 * j with hk
  have hj1 : j * (2 * D) ≤ P - 1 := Nat.div_mul_le_self _ _
  have hj2 : P - 1 < (j + 1) * (2 * D) := by
    have := Nat.lt_mul_div_succ (P - 1) (show 0 < 2 * D by omega)
    rw [Nat.mul_comm] at this; exact this
  set U := P - k * D with hU
  have hkD : k * D = j * (2 * D) := by rw [hk]; ring
  have hU1 : 1 ≤ U := by omega
  have hU2 : U ≤ 2 * D := by
    have : (j + 1) * (2 * D) = j * (2 * D) + 2 * D := by ring
    omega
  have hUP : U + k * D = P := by omega
  have hex : ∃ r, w ≤ U * 2 ^ r := by
    refine ⟨w, ?_⟩
    have := Nat.lt_two_pow_self (n := w)
    nlinarith
  classical
  set r := Nat.find hex with hr
  have hr1 : w ≤ U * 2 ^ r := Nat.find_spec hex
  have hr2 : U * 2 ^ r < 2 * w := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0]; omega
    · have := Nat.find_min hex (show r - 1 < r by omega)
      have e : U * 2 ^ r = 2 * (U * 2 ^ (r - 1)) := by
        rw [← Nat.sub_add_cancel h0, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      omega
  have hPr : w ≤ P * 2 ^ r := by
    have : U * 2 ^ r ≤ P * 2 ^ r := Nat.mul_le_mul_right _ (by omega)
    omega
  set a := (P * 2 ^ r - w) / D with ha
  have ha1 : D * a ≤ P * 2 ^ r - w := Nat.mul_div_le _ _
  have ha2 : P * 2 ^ r - w < D * (a + 1) := Nat.lt_mul_div_succ _ hD
  have hPe : P * 2 ^ r = U * 2 ^ r + k * D * 2 ^ r := by
    rw [← hUP]; ring
  have hlo : k * 2 ^ r ≤ a := by
    rw [ha, Nat.le_div_iff_mul_le hD]
    have : k * 2 ^ r * D = k * D * 2 ^ r := by ring
    omega
  have hhi : a < (k + 1) * 2 ^ r := by
    have h3 : U * 2 ^ r ≤ 2 * (D * 2 ^ r) := by
      have := Nat.mul_le_mul_right (2 ^ r) hU2
      linarith
    rw [ha, Nat.div_lt_iff_lt_mul hD]
    have e1 : (k + 1) * 2 ^ r * D = k * D * 2 ^ r + D * 2 ^ r := by ring
    omega
  have hdiv : a / 2 ^ r = k := Nat.div_eq_of_lt_le hlo hhi
  refine ⟨r, a, ?_, ?_, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : r = i
    · subst hi
      rw [Nat.testBit_eq_decide_div_mod_eq, hdiv, hk]
      have : 2 * j % 2 = 0 := by omega
      simp [this]
    · simp [hi]
  · rw [Nat.mul_add] at ha2
    omega
  · rw [Nat.mul_add] at ha2
    omega
  · rw [Nat.mul_add] at ha2
    omega

/-! ## Piece 4: one pair on the ray, and the case theorem -/

/-- **One pair on the ray**: for both terms of the speed odd and `p < q`, every offset `e` has a
pair with no shared binary digit on the ray. A positive offset is hit with `b = 0`, a negative
one by a single-bit hit, and offset zero by the pair `(0, 0)`. -/
theorem exists_disjoint_onRay_of_odd (p q : ℕ) (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : p < q)
    (e : ℤ) : ∃ a b : ℕ, a &&& b = 0 ∧ OnRay p q e a b := by
  have hq0 : 0 < q := by omega
  have hq0' : (0 : ℤ) < q := by exact_mod_cast hq0
  rcases lt_trichotomy e 0 with he | he | he
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, e = -(n : ℤ) := ⟨e.natAbs, by omega⟩
    have hn0 : 0 < n := by omega
    have hqn : q ≤ q * n := Nat.le_mul_of_pos_right q hn0
    obtain ⟨r, a, hdis, h1, h2, h3⟩ := exists_single_bit_hit ((q + p) / 2) ((q - p) / 2)
      ((q * n + 1) / 2) (by omega) (by omega) (by omega)
    refine ⟨a, 2 ^ r, hdis, ?_⟩
    rw [onRay_iff p q hq0]
    have hX : (q : ℤ) + p = 2 * (((q + p) / 2 : ℕ) : ℤ) := by omega
    have hY : (q : ℤ) - p = 2 * (((q - p) / 2 : ℕ) : ℤ) := by omega
    have hqn' : ((q * n : ℕ) : ℤ) = q * n := by push_cast; ring
    have h1' : (((q - p) / 2 : ℕ) : ℤ) * a ≤ (((q + p) / 2 : ℕ) : ℤ) * 2 ^ r := by
      exact_mod_cast h1
    have h2' : (((q * n + 1) / 2 : ℕ) : ℤ) ≤ (((q + p) / 2 : ℕ) : ℤ) * 2 ^ r -
        (((q - p) / 2 : ℕ) : ℤ) * a := by
      have := Nat.cast_le (α := ℤ) |>.mpr h2
      push_cast [Nat.cast_sub h1] at this
      exact this
    have h3' : (((q + p) / 2 : ℕ) : ℤ) * 2 ^ r - (((q - p) / 2 : ℕ) : ℤ) * a <
        (((q * n + 1) / 2 : ℕ) : ℤ) + (((q - p) / 2 : ℕ) : ℤ) := by
      have := Nat.cast_lt (α := ℤ) |>.mpr h3
      push_cast [Nat.cast_sub h1] at this
      exact this
    have hw : 2 * (((q * n + 1) / 2 : ℕ) : ℤ) ≤ ((q * n : ℕ) : ℤ) + 1 := by omega
    have hw' : ((q * n : ℕ) : ℤ) ≤ 2 * (((q * n + 1) / 2 : ℕ) : ℤ) := by omega
    have hD : 2 * (((q - p) / 2 : ℕ) : ℤ) = q - p := by omega
    have hpq' : (p : ℤ) ≥ 1 := by omega
    rw [hqn'] at hw hw'
    rw [hn]
    push_cast
    rw [hX, hY]
    constructor <;> linarith
  · subst he
    refine ⟨0, 0, rfl, ?_⟩
    rw [onRay_iff p q hq0]
    simpa using hq0'
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, e = (n : ℤ) := ⟨e.natAbs, by omega⟩
    have hcp : 0 < q - p := by omega
    refine ⟨q * n / (q - p), 0, Nat.and_zero _, ?_⟩
    rw [onRay_iff p q hq0]
    set a := q * n / (q - p) with ha
    have h1 : (q - p) * a ≤ q * n := Nat.mul_div_le _ _
    have h2 : q * n < (q - p) * (a + 1) := Nat.lt_mul_div_succ _ hcp
    have hc : (((q - p : ℕ)) : ℤ) = (q : ℤ) - p := Nat.cast_sub hpq.le
    have h1' : ((q : ℤ) - p) * a ≤ q * n := by rw [← hc]; exact_mod_cast h1
    have h2' : (q : ℤ) * n < ((q : ℤ) - p) * (a + 1) := by rw [← hc]; exact_mod_cast h2
    have hp1 : (1 : ℤ) ≤ p := by omega
    rw [hn]
    push_cast
    constructor <;> nlinarith

/-- **The second condition where both terms of the speed are odd**: for `p` and `q` odd with
`p < q`, at every offset `e`, past every step some pair with no shared binary digit lies on the
ray. The pair found at the offset is pushed past the step by adding a high copy of a zero pair,
which changes the strip's quantity by zero. -/
theorem lateDisjointOnRay_of_odd (p q : ℕ) (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : p < q)
    (e : ℤ) : LateDisjointOnRay p q e := by
  intro T
  obtain ⟨a, b, hab, hon⟩ := exists_disjoint_onRay_of_odd p q hp hq hpq e
  obtain ⟨A, B, hA, hAB, hz⟩ := exists_zero_pair p q hp hq hpq
  have hq0 : 0 < q := by omega
  set M := a + b + T with hM
  have haM : a < 2 ^ M := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := M))
  have hbM : b < 2 ^ M := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := M))
  have hTM : T ≤ 2 ^ M := le_trans (by omega) (Nat.lt_two_pow_self (n := M)).le
  refine ⟨a + 2 ^ M * A, b + 2 ^ M * B, and_add_shift_eq_zero a b A B M haM hbM hab hAB, ?_, ?_⟩
  · have : 2 ^ M * 1 ≤ 2 ^ M * A := Nat.mul_le_mul_left _ hA
    omega
  · rw [onRay_iff p q hq0] at hon ⊢
    have key : ((q : ℤ) + p) * ((b + 2 ^ M * B : ℕ) : ℤ)
        - ((q : ℤ) - p) * ((a + 2 ^ M * A : ℕ) : ℤ) + q * e =
          ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + q * e := by
      push_cast
      linear_combination (2 ^ M : ℤ) * hz
    rw [key]
    exact hon

/-- **Joint satisfiability**: both terms of the speed odd, `p < q`, and the second condition at
speed `1 / 3` from offset `-1`. -/
theorem lateDisjointOnRay_of_odd_nonvacuous :
    1 % 2 = 1 ∧ 3 % 2 = 1 ∧ 1 < 3 ∧ LateDisjointOnRay 1 3 (-1) :=
  ⟨by decide, by decide, by decide, lateDisjointOnRay_of_odd 1 3 (by decide) (by decide)
    (by decide) (-1)⟩

/-! ## Odd sum with the speed below one third -/

/-! ### Piece 1: the left-edge family -/

/-- **A family of pairs on the ray**: pairs whose first member is a multiple `j * 2 ^ K` of a
power of two. When the strip's offset `c` puts `c + q e` in `[0, q)` and the number
`c + 2 ^ K (q - p) j` is divisible by the sum of the speed's terms and lies in
`[0, 2 ^ K (q + p))`, some `b` with no binary digit shared with `j * 2 ^ K` makes the pair
lie on the ray. -/
theorem onRay_of_dvd (p q : ℕ) (hpq : p < q) (e : ℤ) (j K : ℕ) (c : ℤ)
    (h0 : 0 ≤ c + q * e) (h1 : c + q * e < q)
    (hdvd : ((q : ℤ) + p) ∣ c + 2 ^ K * (((q : ℤ) - p) * j))
    (hlo : 0 ≤ c + 2 ^ K * (((q : ℤ) - p) * j))
    (hhi : c + 2 ^ K * (((q : ℤ) - p) * j) < 2 ^ K * ((q : ℤ) + p)) :
    ∃ b : ℕ, (j * 2 ^ K) &&& b = 0 ∧ OnRay p q e (j * 2 ^ K) b := by
  have hq0 : 0 < q := by omega
  have hs : (0 : ℤ) < (q : ℤ) + p := by positivity
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 ≤ m := by
    by_contra h
    push Not at h
    nlinarith
  have hm1 : m < 2 ^ K := by
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, m = b := ⟨m.toNat, by omega⟩
  have hb : b < 2 ^ K := by exact_mod_cast hm1
  refine ⟨b, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < K
    · have : (j * 2 ^ K).testBit i = false := by
        rw [Nat.mul_comm]
        rw [Nat.testBit_two_pow_mul]
        simp [hi]
      simp [this]
    · have : b.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num)
          (by omega)))
      simp [this]
  · rw [onRay_iff p q hq0]
    push_cast
    constructor <;> nlinarith

/-! ### Piece 2: a residue in the window -/

/-- **A residue in the window**: for `0 < p` and `3 p < q`, some power of two `2 ^ K` has
`(x - 2 ^ K (q - p)) % (q + p)` below `q`. Otherwise every residue lies in `[q, q + p)`, the
successive differences are doubled at each step, hence bounded only if zero, and then the sum
of the speed's terms would divide their difference. -/
theorem exists_pow_residue_lt (p q : ℕ) (hp : 0 < p) (h3 : 3 * p < q) (x : ℤ) :
    ∃ K : ℕ, (x - 2 ^ K * ((q : ℤ) - p)) % ((q : ℤ) + p) < q := by
  by_contra hcon
  push Not at hcon
  set s : ℤ := (q : ℤ) + p with hs
  set t : ℤ := (q : ℤ) - p with ht
  have hs0 : 0 < s := by omega
  have ht0 : 0 < t := by omega
  have hts : t < s := by omega
  have hps : 3 * (p : ℤ) < s := by omega
  set ρ : ℕ → ℤ := fun K => (x - 2 ^ K * t) % s with hρ
  set u : ℕ → ℤ := fun K => (x - 2 ^ K * t) / s with hu
  have hdec : ∀ K, x - 2 ^ K * t = s * u K + ρ K := fun K =>
    (Int.mul_ediv_add_emod _ _).symm
  have hρlo : ∀ K, (q : ℤ) ≤ ρ K := fun K => hcon K
  have hρhi : ∀ K, ρ K < s := fun K => Int.emod_lt_of_pos _ hs0
  set D : ℕ → ℤ := fun K => ρ (K + 1) - ρ K with hD
  have hDb : ∀ K, -(p : ℤ) < D K ∧ D K < p := fun K => by
    have := hρlo K; have := hρhi K; have := hρlo (K + 1); have := hρhi (K + 1)
    simp only [hD]
    omega
  have hDe : ∀ K, D K = -(2 ^ K * t) - s * (u (K + 1) - u K) := fun K => by
    have h1 := hdec K
    have h2 := hdec (K + 1)
    simp only [hD]
    rw [pow_succ] at h2
    linarith
  have hdbl : ∀ K, D (K + 1) = 2 * D K := fun K => by
    have e1 := hDe K
    have e2 := hDe (K + 1)
    have b1 := hDb K
    have b2 := hDb (K + 1)
    set m : ℤ := u (K + 2) - u (K + 1) - 2 * (u (K + 1) - u K) with hm
    have hm' : D (K + 1) - 2 * D K = -(s * m) := by
      rw [e1, e2, hm]; rw [pow_succ]; ring
    have : m = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · nlinarith
      · nlinarith
    rw [this] at hm'
    linarith
  have hpow : ∀ K, D K = 2 ^ K * D 0 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih => rw [hdbl, ih, pow_succ]; ring
  have hD0 : D 0 = 0 := by
    by_contra hne
    have hb := hDb p
    rw [hpow p] at hb
    have hp2 : (p : ℤ) < 2 ^ p := by exact_mod_cast Nat.lt_two_pow_self (n := p)
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith [hb.1]
    · nlinarith [hb.2]
  have h0 := hDe 0
  rw [hD0] at h0
  simp only [pow_zero, one_mul] at h0
  set w := u 1 - u 0
  have : s * w = -t := by linarith
  rcases lt_trichotomy w 0 with h | h | h
  · nlinarith
  · rw [h] at this; omega
  · nlinarith

/-! ### Piece 3: the case theorem -/

/-- **The second condition for odd sum with the speed below one third**: for `0 < p`,
`3 p < q` and the sum `p + q` odd, at every offset `e`, past every step some pair with no shared
binary digit lies on the ray. The pairs found are of the family whose first member is a power of
two: a residue in the window fixes the strip's offset, and the power of two is then advanced by
multiples of the totient of the odd sum, which keeps the divisibility and lets the bounds hold.
The conclusion holds beyond these hypotheses, which mark this proof's route and not the
statement's boundary, so no refuting instance is kept. -/
theorem lateDisjointOnRay_of_three_mul_lt (p q : ℕ) (hp : 0 < p) (h3 : 3 * p < q)
    (hodd : (p + q) % 2 = 1) (e : ℤ) : LateDisjointOnRay p q e := by
  intro T
  have hq0 : 0 < q := by omega
  obtain ⟨K₀, hK₀⟩ := exists_pow_residue_lt p q hp h3 (q * e)
  set s : ℤ := (q : ℤ) + p with hs
  set t : ℤ := (q : ℤ) - p with ht
  set ρ : ℤ := ((q : ℤ) * e - 2 ^ K₀ * t) % s with hρ
  have hs0 : 0 < s := by omega
  have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ hs0.ne'
  set c : ℤ := -(q * e) + ρ with hc
  have hcop : Nat.Coprime 2 (q + p) := by
    apply Nat.coprime_two_left.mpr
    rw [Nat.odd_iff]; omega
  have hmod := Nat.ModEq.pow_totient hcop
  set n := Nat.totient (q + p) with hn
  have hn0 : 0 < n := Nat.totient_pos.mpr (by omega)
  have hmodZ : (2 : ℤ) ^ n ≡ 1 [ZMOD s] := by
    have := (Nat.modEq_iff_dvd.mp hmod)
    rw [Int.modEq_iff_dvd]
    simpa [hs] using this
  set i := T + c.natAbs + 1 with hi
  set K := K₀ + n * i with hK
  have hKi : i ≤ K := by nlinarith
  have hbig : i < 2 ^ K := lt_of_le_of_lt hKi (Nat.lt_two_pow_self (n := K))
  have hbigZ : (i : ℤ) < 2 ^ K := by exact_mod_cast hbig
  have hdvd0 : s ∣ c + 2 ^ K₀ * t := by
    refine ⟨-(((q : ℤ) * e - 2 ^ K₀ * t) / s), ?_⟩
    have := Int.mul_ediv_add_emod ((q : ℤ) * e - 2 ^ K₀ * t) s
    rw [hc]
    linarith
  have hpowK : (2 : ℤ) ^ K ≡ 2 ^ K₀ [ZMOD s] := by
    have h1 := (hmodZ.pow i).mul_left (2 ^ K₀)
    rw [one_pow, mul_one, ← pow_mul, ← pow_add] at h1
    exact h1
  have hdvd : s ∣ c + 2 ^ K * (t * ((1 : ℕ) : ℤ)) := by
    have : s ∣ 2 ^ K * t - 2 ^ K₀ * t := by
      have := (Int.modEq_iff_dvd.mp hpowK.symm)
      obtain ⟨k, hk⟩ := this
      exact ⟨k * t, by linear_combination t * hk⟩
    have h2 := dvd_add hdvd0 this
    simpa [add_assoc, mul_one] using (by
      convert h2 using 1; ring : s ∣ c + 2 ^ K * t) |>.trans (by simp)
  have habs : (c.natAbs : ℤ) = |c| := Int.natCast_natAbs c
  have hcle : -(c.natAbs : ℤ) ≤ c := by rw [habs]; exact neg_abs_le c
  have hcle' : c ≤ c.natAbs := by rw [habs]; exact le_abs_self c
  have hi' : (i : ℤ) = T + c.natAbs + 1 := by rw [hi]; push_cast; ring
  have hlo : 0 ≤ c + 2 ^ K * (t * ((1 : ℕ) : ℤ)) := by
    push_cast
    have : (1 : ℤ) ≤ t := by omega
    nlinarith
  have hhi : c + 2 ^ K * (t * ((1 : ℕ) : ℤ)) < 2 ^ K * s := by
    push_cast
    have : (1 : ℤ) ≤ p := by exact_mod_cast hp
    have e2 : s = t + 2 * p := by rw [hs, ht]; ring
    rw [e2]
    nlinarith
  obtain ⟨b, hb1, hb2⟩ := onRay_of_dvd p q (by omega) e 1 K c (by rw [hc]; linarith)
    (by rw [hc]; linarith) hdvd hlo hhi
  refine ⟨1 * 2 ^ K, b, hb1, ?_, hb2⟩
  have hT : T ≤ i := by omega
  have : T ≤ 2 ^ K := by
    have : (T : ℤ) ≤ 2 ^ K := by have : (T : ℤ) ≤ i := by exact_mod_cast hT
                                 linarith
    exact_mod_cast this
  omega

/-- **Joint satisfiability**: `0 < 1`, `3 * 1 < 4`, the sum `1 + 4` odd, and the second
condition at speed `1 / 4` from offset zero. -/
theorem lateDisjointOnRay_of_three_mul_lt_nonvacuous :
    0 < 1 ∧ 3 * 1 < 4 ∧ (1 + 4) % 2 = 1 ∧ LateDisjointOnRay 1 4 0 :=
  ⟨by decide, by decide, by decide,
    lateDisjointOnRay_of_three_mul_lt 1 4 (by decide) (by decide) (by decide) 0⟩

/-! ## Odd sum with the speed above one third -/

/-! ### Piece 1: the pump at the top digit -/

private theorem and_sub_top' (M a b : ℕ) (h1 : 2 ^ M ≤ a) (h2 : a < 2 ^ (M + 1))
    (h : a &&& b = 0) (hb : b < 2 ^ M) : (a - 2 ^ M) &&& b = 0 := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le' h1
  have ha' : a' < 2 ^ M := by rw [pow_succ] at h2; omega
  have hor := Nat.two_pow_add_eq_or_of_lt ha' 1
  rw [mul_one, add_comm] at hor
  rw [hor] at h
  rw [Nat.add_sub_cancel]
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun n => n.testBit i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at this ⊢
  by_cases hi : i = M
  · subst hi
    simp [Nat.testBit_eq_false_of_lt hb]
  · simp [Ne.symm hi] at this
    simpa using this

/-- **The pump at the top digit**: moving the top binary digit of the first member of a pair with
no shared binary digit up by `n` places, and adding to the second member the number `C` below
`2 ^ n` shifted to sit just above the second member's digits, keeps the two digit sets disjoint:
below the top the old pair, then only `C`, then only the moved digit. -/
theorem and_pump_top (a b M n C : ℕ) (ha0 : 2 ^ M ≤ a) (ha1 : a < 2 ^ (M + 1)) (hb : b < 2 ^ M)
    (hab : a &&& b = 0) (hC : C < 2 ^ n) :
    (a - 2 ^ M + 2 ^ (M + n)) &&& (b + 2 ^ M * C) = 0 := by
  have hdis := and_sub_top' M a b ha0 ha1 hab hb
  have ha' : a - 2 ^ M < 2 ^ M := by rw [pow_succ] at ha1; omega
  have hCn : (2 ^ n) &&& C = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : n = i
    · subst hi
      simp [Nat.testBit_lt_two_pow hC]
    · simp [hi]
  have := and_add_shift_eq_zero (a - 2 ^ M) b (2 ^ n) C M ha' hb hdis hCn
  rw [pow_add]
  exact this

/-! ### Piece 2: the single-bit hit with the top digit in the first member -/

/-- **A single-bit hit with the top digit in the first member**: for `0 < D`, `2 D < P` and
`P - 2 ⌊(P - 1) / (2 D)⌋ D < 2 w`, some power of two `2 ^ r` and some `a` with bit `r` of `a` zero
and `2 ^ (r + 1) ≤ a` have `P 2 ^ r - D a` in the window `[w, w + D)`. -/
theorem exists_single_bit_hit_top (P D w : ℕ) (hD : 0 < D) (h2 : 2 * D < P)
    (hw : P - 2 * ((P - 1) / (2 * D)) * D < 2 * w) :
    ∃ r a : ℕ, a &&& 2 ^ r = 0 ∧ 2 ^ (r + 1) ≤ a ∧ D * a ≤ P * 2 ^ r ∧
      w ≤ P * 2 ^ r - D * a ∧ P * 2 ^ r - D * a < w + D := by
  set j := (P - 1) / (2 * D) with hj
  set k := 2 * j with hk
  have hj1 : j * (2 * D) ≤ P - 1 := Nat.div_mul_le_self _ _
  have hj2 : P - 1 < (j + 1) * (2 * D) := by
    have := Nat.lt_mul_div_succ (P - 1) (show 0 < 2 * D by omega)
    rw [Nat.mul_comm] at this; exact this
  have hjpos : 1 ≤ j := by
    by_contra hcon
    have : j = 0 := by omega
    rw [this] at hj2
    omega
  set U := P - k * D with hU
  have hkD : k * D = j * (2 * D) := by rw [hk]; ring
  have hU1 : 1 ≤ U := by omega
  have hU2 : U ≤ 2 * D := by
    have : (j + 1) * (2 * D) = j * (2 * D) + 2 * D := by ring
    omega
  have hUP : U + k * D = P := by omega
  have hwU : U < 2 * w := by
    have : 2 * j * D = k * D := by rw [hk]
    omega
  have hex : ∃ r, w ≤ U * 2 ^ r := by
    refine ⟨w, ?_⟩
    have := Nat.lt_two_pow_self (n := w)
    nlinarith
  classical
  set r := Nat.find hex with hr
  have hr1 : w ≤ U * 2 ^ r := Nat.find_spec hex
  have hr2 : U * 2 ^ r < 2 * w := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0]; omega
    · have := Nat.find_min hex (show r - 1 < r by omega)
      have e : U * 2 ^ r = 2 * (U * 2 ^ (r - 1)) := by
        rw [← Nat.sub_add_cancel h0, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      omega
  have hPr : w ≤ P * 2 ^ r := by
    have : U * 2 ^ r ≤ P * 2 ^ r := Nat.mul_le_mul_right _ (by omega)
    omega
  set a := (P * 2 ^ r - w) / D with ha
  have ha1 : D * a ≤ P * 2 ^ r - w := Nat.mul_div_le _ _
  have ha2 : P * 2 ^ r - w < D * (a + 1) := Nat.lt_mul_div_succ _ hD
  have hPe : P * 2 ^ r = U * 2 ^ r + k * D * 2 ^ r := by
    rw [← hUP]; ring
  have hlo : k * 2 ^ r ≤ a := by
    rw [ha, Nat.le_div_iff_mul_le hD]
    have : k * 2 ^ r * D = k * D * 2 ^ r := by ring
    omega
  have hhi : a < (k + 1) * 2 ^ r := by
    have h3 : U * 2 ^ r ≤ 2 * (D * 2 ^ r) := by
      have := Nat.mul_le_mul_right (2 ^ r) hU2
      linarith
    rw [ha, Nat.div_lt_iff_lt_mul hD]
    have e1 : (k + 1) * 2 ^ r * D = k * D * 2 ^ r + D * 2 ^ r := by ring
    omega
  have hdiv : a / 2 ^ r = k := Nat.div_eq_of_lt_le hlo hhi
  refine ⟨r, a, ?_, ?_, ?_, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : r = i
    · subst hi
      rw [Nat.testBit_eq_decide_div_mod_eq, hdiv, hk]
      have : 2 * j % 2 = 0 := by omega
      simp [this]
    · simp [hi]
  · have : 2 * 2 ^ r ≤ k * 2 ^ r := Nat.mul_le_mul_right _ (by omega)
    rw [pow_succ]
    omega
  · rw [Nat.mul_add] at ha2
    omega
  · rw [Nat.mul_add] at ha2
    omega
  · rw [Nat.mul_add] at ha2
    omega

/-! ### Piece 3: a pair with the top digit in its first member, on every fast ray -/

/-- **A pair with the top digit in its first member, on every fast ray**: for `0 < p` and
`p < q < 3 p`, at every offset `e`, some pair `(a, b)` with no shared binary digit lies on the
ray, where `a` has its top binary digit at position `M` and `b` lies below `2 ^ M`. A positive
offset is hit with `b = 0`, an offset at or below zero by a single-bit hit with the top digit in
the first member. -/
theorem exists_top_disjoint_onRay (p q : ℕ) (hp : 0 < p) (hpq : p < q) (h3 : q < 3 * p) (e : ℤ) :
    ∃ a b M : ℕ, a &&& b = 0 ∧ 2 ^ M ≤ a ∧ a < 2 ^ (M + 1) ∧ b < 2 ^ M ∧ OnRay p q e a b := by
  have hq0 : 0 < q := by omega
  have hq0' : (0 : ℤ) < q := by exact_mod_cast hq0
  rcases lt_or_ge 0 e with he | he
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, e = (n : ℤ) := ⟨e.natAbs, by omega⟩
    have hn0 : 0 < n := by omega
    have hcp : 0 < q - p := by omega
    set a := q * n / (q - p) with ha
    have h1 : (q - p) * a ≤ q * n := Nat.mul_div_le _ _
    have h2 : q * n < (q - p) * (a + 1) := Nat.lt_mul_div_succ _ hcp
    have hqn : q ≤ q * n := Nat.le_mul_of_pos_right q hn0
    have ha0 : 0 < a := by
      by_contra hcon
      have : a = 0 := Nat.eq_zero_of_not_pos hcon
      rw [this] at h2
      simp at h2
      omega
    refine ⟨a, 0, Nat.log 2 a, Nat.and_zero _, Nat.pow_log_le_self 2 (by omega),
      Nat.lt_pow_succ_log_self (by norm_num) _, by positivity, ?_⟩
    rw [onRay_iff p q hq0]
    have hc : (((q - p : ℕ)) : ℤ) = (q : ℤ) - p := Nat.cast_sub hpq.le
    have h1' : ((q : ℤ) - p) * a ≤ q * n := by rw [← hc]; exact_mod_cast h1
    have h2' : (q : ℤ) * n < ((q : ℤ) - p) * (a + 1) := by rw [← hc]; exact_mod_cast h2
    have hp1 : (1 : ℤ) ≤ p := by omega
    rw [hn]
    push_cast
    constructor <;> nlinarith
  · -- offset at or below zero
    obtain ⟨n, hn⟩ : ∃ n : ℕ, e = -(n : ℤ) := ⟨e.natAbs, by omega⟩
    have hD : 0 < q - p := by omega
    have h2D : 2 * (q - p) < q + p := by omega
    set w : ℕ := if n = 0 then p else q * n with hwdef
    have hwU : (q + p) - 2 * ((q + p - 1) / (2 * (q - p))) * (q - p) < 2 * w := by
      set j := (q + p - 1) / (2 * (q - p)) with hj
      have hj1 : j * (2 * (q - p)) ≤ q + p - 1 := Nat.div_mul_le_self _ _
      have hj2 : q + p - 1 < (j + 1) * (2 * (q - p)) := by
        have := Nat.lt_mul_div_succ (q + p - 1) (show 0 < 2 * (q - p) by omega)
        rw [Nat.mul_comm] at this; exact this
      have hjk : 2 * j * (q - p) = j * (2 * (q - p)) := by ring
      have hjk' : (j + 1) * (2 * (q - p)) = j * (2 * (q - p)) + 2 * (q - p) := by ring
      by_cases hn0 : n = 0
      · have hw : w = p := by rw [hwdef]; simp [hn0]
        rw [hw]
        by_cases hq2 : q < 2 * p
        · omega
        · have hj1' : j = 1 := by
            apply Nat.div_eq_of_lt_le
            · omega
            · omega
          rw [hj1']
          omega
      · have hw : w = q * n := by rw [hwdef]; simp [hn0]
        have : q ≤ q * n := Nat.le_mul_of_pos_right q (by omega)
        rw [hw]
        omega
    obtain ⟨r, a, hdis, htop, h1, h2, h3⟩ :=
      exists_single_bit_hit_top (q + p) (q - p) w hD h2D hwU
    have hM : Nat.log 2 a ≥ r + 1 := by
      apply Nat.le_log_of_pow_le (by norm_num) htop
    have hapos : 0 < a := lt_of_lt_of_le (by positivity) htop
    refine ⟨a, 2 ^ r, Nat.log 2 a, hdis, Nat.pow_log_le_self 2 (by omega),
      Nat.lt_pow_succ_log_self (by norm_num) _, ?_, ?_⟩
    · exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega)) le_rfl
    · rw [onRay_iff p q hq0]
      have hc : (((q - p : ℕ)) : ℤ) = (q : ℤ) - p := Nat.cast_sub hpq.le
      have h1' : (((q - p : ℕ)) : ℤ) * a ≤ ((q + p : ℕ) : ℤ) * 2 ^ r := by
        exact_mod_cast h1
      have h2' : (w : ℤ) ≤ ((q + p : ℕ) : ℤ) * 2 ^ r - ((q - p : ℕ) : ℤ) * a := by
        have := Nat.cast_le (α := ℤ) |>.mpr h2
        push_cast [Nat.cast_sub h1] at this ⊢
        exact this
      have h3' : ((q + p : ℕ) : ℤ) * 2 ^ r - ((q - p : ℕ) : ℤ) * a < w + ((q - p : ℕ) : ℤ) := by
        have := Nat.cast_lt (α := ℤ) |>.mpr h3
        push_cast [Nat.cast_sub h1] at this ⊢
        exact this
      rw [hc] at h1' h2' h3'
      push_cast at h1' h2' h3'
      have hp1 : (1 : ℤ) ≤ p := by omega
      by_cases hn0 : n = 0
      · have hw : (w : ℤ) = p := by rw [hwdef]; simp [hn0]
        rw [hw] at h2' h3'
        rw [hn, hn0]
        push_cast
        constructor <;> nlinarith
      · have hw : (w : ℤ) = q * n := by rw [hwdef]; simp [hn0]
        rw [hw] at h2' h3'
        rw [hn]
        push_cast
        constructor <;> nlinarith

/-! ### Piece 4: the fast rays of odd sum -/

/-- **The second condition for odd sum with the speed above one third and below one**: for
`0 < p`, `p < q < 3 p` and the sum `p + q` odd, at every offset `e`, past every step some pair
with no shared binary digit lies on the ray. A pair with the top digit in its first member is
taken at the offset; its top digit is then moved up by a multiple `n` of the totient of the odd
sum, and the second member gains the number `C` below `2 ^ n` that keeps the strip's quantity
fixed. -/
theorem lateDisjointOnRay_of_lt_three_mul (p q : ℕ) (hp : 0 < p) (hpq : p < q) (h3 : q < 3 * p)
    (hodd : (p + q) % 2 = 1) (e : ℤ) : LateDisjointOnRay p q e := by
  intro T
  have hq0 : 0 < q := by omega
  obtain ⟨a, b, M, hab, ha0, ha1, hb, hon⟩ := exists_top_disjoint_onRay p q hp hpq h3 e
  have hcop : Nat.Coprime 2 (q + p) := by
    apply Nat.coprime_two_left.mpr
    rw [Nat.odd_iff]; omega
  have hmod := Nat.ModEq.pow_totient hcop
  set φ := Nat.totient (q + p) with hφ
  have hφ0 : 0 < φ := Nat.totient_pos.mpr (by omega)
  set n := φ * (T + 1) with hn
  have hnT : T + 1 ≤ n := by nlinarith
  have hmodn : 2 ^ n ≡ 1 [MOD q + p] := by
    have := hmod.pow (T + 1)
    rw [one_pow, ← pow_mul] at this
    exact this
  have hdvd : (q + p) ∣ 2 ^ n - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hmodn.symm
  obtain ⟨c0, hc0⟩ := hdvd
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  set C := (q - p) * c0 with hC
  have hCn : C < 2 ^ n := by
    have : (q - p) * c0 ≤ (q + p) * c0 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hTn : T < 2 ^ n := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := n)).le
  have hpow : 2 ^ n ≤ 2 ^ (M + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hMpos : 2 ^ M ≤ a := ha0
  refine ⟨a - 2 ^ M + 2 ^ (M + n), b + 2 ^ M * C,
    and_pump_top a b M n C ha0 ha1 hb hab hCn, by omega, ?_⟩
  rw [onRay_iff p q hq0] at hon ⊢
  have hcz : ((2 ^ n - 1 : ℕ) : ℤ) = 2 ^ n - 1 := by
    rw [Nat.cast_sub hpos]; push_cast; ring
  have hc0z : (2 : ℤ) ^ n - 1 = ((q : ℤ) + p) * c0 := by
    rw [← hcz, hc0]; push_cast; ring
  have key : ((q : ℤ) + p) * ((b + 2 ^ M * C : ℕ) : ℤ)
      - ((q : ℤ) - p) * ((a - 2 ^ M + 2 ^ (M + n) : ℕ) : ℤ) + q * e =
        ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + q * e := by
    have hcast : ((a - 2 ^ M + 2 ^ (M + n) : ℕ) : ℤ) = a - 2 ^ M + 2 ^ (M + n) := by
      push_cast [Nat.cast_sub hMpos]; ring
    rw [hcast]
    have hCz : (C : ℤ) = ((q : ℤ) - p) * c0 := by
      rw [hC, Nat.cast_mul, Nat.cast_sub hpq.le]
    push_cast
    rw [hCz, pow_add]
    linear_combination (-(2 ^ M * ((q : ℤ) - p))) * hc0z
  rw [key]
  exact hon

/-- **Joint satisfiability**: `0 < 1`, `1 < 2`, `2 < 3 * 1`, the sum `1 + 2` odd, and the second
condition at speed `1 / 2` from offset zero. -/
theorem lateDisjointOnRay_of_lt_three_mul_nonvacuous :
    0 < 1 ∧ 1 < 2 ∧ 2 < 3 * 1 ∧ (1 + 2) % 2 = 1 ∧ LateDisjointOnRay 1 2 0 :=
  ⟨by decide, by decide, by decide, by decide,
    lateDisjointOnRay_of_lt_three_mul 1 2 (by decide) (by decide) (by decide) (by decide) 0⟩

/-! ## Every speed strictly between 0 and 1 -/

/-- **The second condition at every speed strictly between 0 and 1**: for `0 < p` and `p < q`,
at every offset `e`, past every step some pair with no shared binary digit lies on the ray.
By strong induction on `p + q`: when both terms are even the speed reduces to a smaller one,
when both are odd the case of odd terms applies, and otherwise the sum is odd, the speed is not
`1 / 3` because four times the numerator is even, and the case above one third or the case
below it applies. -/
theorem lateDisjointOnRay (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    LateDisjointOnRay p q e := by
  suffices h : ∀ n p q : ℕ, p + q = n → 0 < p → p < q → LateDisjointOnRay p q e from
    h _ p q rfl hp hpq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p q hn hp hpq
    by_cases hpe : p % 2 = 0
    · by_cases hqe : q % 2 = 0
      · obtain ⟨p', rfl⟩ : ∃ p', p = 2 * p' := ⟨p / 2, by omega⟩
        obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
        have := ih (p' + q') (by omega) p' q' rfl (by omega) (by omega)
        intro T
        obtain ⟨a, b, hab, hT, hon⟩ := this T
        refine ⟨a, b, hab, hT, ?_⟩
        unfold OnRay at hon ⊢
        rw [show 2 * p' * (a + b) = 2 * (p' * (a + b)) by ring,
          Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
        exact hon
      · have hodd : (p + q) % 2 = 1 := by omega
        rcases lt_trichotomy q (3 * p) with h | h | h
        · exact lateDisjointOnRay_of_lt_three_mul p q hp hpq h hodd e
        · omega
        · exact lateDisjointOnRay_of_three_mul_lt p q hp h hodd e
    · by_cases hqe : q % 2 = 0
      · have hodd : (p + q) % 2 = 1 := by omega
        rcases lt_trichotomy q (3 * p) with h | h | h
        · exact lateDisjointOnRay_of_lt_three_mul p q hp hpq h hodd e
        · omega
        · exact lateDisjointOnRay_of_three_mul_lt p q hp h hodd e
      · exact lateDisjointOnRay_of_odd p q (by omega) (by omega) hpq e

/-! ## The rays of rule 90 from the single seed, unconditionally -/

open ExtremeTapWidth EndpointClasses
open ObservedColumn (observedRationalRay hq90)

/-- **A one past every step on every ray strictly between speed 0 and speed 1**: for `0 < p` and
`p < q`, from every cell `e`, the ray of rule 90 from the single seed reads `1` past every
step. -/
theorem exists_late_one_observedRationalRay_f90_single (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (e : ℤ) : ∀ T : ℕ, ∃ t, T ≤ t ∧
      observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1 :=
  exists_late_one_observedRationalRay_f90_single_of p q e oneOfDisjoint
    (lateDisjointOnRay p q hp hpq e)

/-- **The ray of rule 90 from the single seed is not eventually periodic at any speed strictly
between 0 and 1**: for `0 < p` and `p < q`, from every cell `e`. The three conditions of the
parent hold: a one at every disjoint pair, late disjoint pairs on the ray, and late zero runs. -/
theorem not_eventuallyPeriodic_observedRationalRay_f90_single (p q : ℕ) (hp : 0 < p)
    (hpq : p < q) (e : ℤ) :
    ¬ GrowingComposite.EventuallyPeriodic
      (observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_observedRationalRay_f90_single_of p q e oneOfDisjoint
    (lateDisjointOnRay p q hp hpq e) (lateZeroRuns p q hpq e)

/-- **Joint satisfiability**: `0 < 1`, `1 < 2`, and the ray at speed `1 / 2` from cell zero is
not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f90_single_nonvacuous :
    0 < 1 ∧ 1 < 2 ∧ ¬ GrowingComposite.EventuallyPeriodic
      (observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 0) :=
  ⟨by decide, by decide,
    not_eventuallyPeriodic_observedRationalRay_f90_single 1 2 (by decide) (by decide) 0⟩

/-- **Speed zero is load-bearing**: at speed zero from cell `0` the ray is the center column, `1`
at step zero and `0` at every later step, so it is eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f90_single_guard_zero :
    GrowingComposite.EventuallyPeriodic
      (observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1 0) := by
  rw [ObservedColumn.observedRationalRay_zero, ObservedColumn.observedColumn_f90_single]
  refine ⟨1, 1, by norm_num, fun u hu => ?_⟩
  have h1 : u ≠ 0 := by omega
  simp [h1]

/-- **Speed one is load-bearing**: at speed one from cell `0` the ray reads `1` at every step, so
it is eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f90_single_guard_one :
    GrowingComposite.EventuallyPeriodic
      (observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 1 0) := by
  have hone : ∀ t : ℕ,
      observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 1 0 t
        = 1 := by
    intro t
    have h := oneOfDisjoint t 0 (by simp)
    unfold observedRationalRay
    simp only [add_zero, Nat.cast_zero, sub_zero] at h
    simpa using h
  exact ⟨1, 0, by norm_num, fun u _ => by rw [hone, hone]⟩

end RationalRayNinety

/-- info: 'RationalRayNinety.onRay_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.onRay_iff

/-- info: 'RationalRayNinety.exists_zero_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_zero_pair

/-- info: 'RationalRayNinety.and_add_shift_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.and_add_shift_eq_zero

/-- info: 'RationalRayNinety.exists_zero_pair_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_zero_pair_guard

/-- info: 'RationalRayNinety.exists_single_bit_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_single_bit_hit

/-- info: 'RationalRayNinety.exists_disjoint_onRay_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_disjoint_onRay_of_odd

/-- info: 'RationalRayNinety.lateDisjointOnRay_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateDisjointOnRay_of_odd

/-- info: 'RationalRayNinety.lateDisjointOnRay_of_odd_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateDisjointOnRay_of_odd_nonvacuous

/-- info: 'RationalRayNinety.onRay_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.onRay_of_dvd

/-- info: 'RationalRayNinety.exists_pow_residue_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_pow_residue_lt

/-- info: 'RationalRayNinety.lateDisjointOnRay_of_three_mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateDisjointOnRay_of_three_mul_lt

/-- info: 'RationalRayNinety.lateDisjointOnRay_of_three_mul_lt_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateDisjointOnRay_of_three_mul_lt_nonvacuous

/-- info: 'RationalRayNinety.and_pump_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.and_pump_top

/-- info: 'RationalRayNinety.exists_single_bit_hit_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_single_bit_hit_top

/-- info: 'RationalRayNinety.exists_top_disjoint_onRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_top_disjoint_onRay

/-- info: 'RationalRayNinety.lateDisjointOnRay_of_lt_three_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateDisjointOnRay_of_lt_three_mul

/-- info: 'RationalRayNinety.lateDisjointOnRay_of_lt_three_mul_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateDisjointOnRay_of_lt_three_mul_nonvacuous

/-- info: 'RationalRayNinety.lateDisjointOnRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.lateDisjointOnRay

/-- info: 'RationalRayNinety.exists_late_one_observedRationalRay_f90_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.exists_late_one_observedRationalRay_f90_single

/-- info: 'RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single

/-- info: 'RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single_nonvacuous

/-- info: 'RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single_guard_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single_guard_zero

/-- info: 'RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single_guard_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayNinety.not_eventuallyPeriodic_observedRationalRay_f90_single_guard_one
