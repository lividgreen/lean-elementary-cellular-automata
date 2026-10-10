/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.RationalRayRule90
-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Rule 90 from a two-cell seed: the ray of speed one third from cell one reads zero
([RuleSpace] §5 Propositions 5.2 and 5.3)

`[RuleSpace] §5 Proposition 5.1` is stated for rule `90` from the single seed (`RationalRayRule90`).
This file shows that hypothesis is load-bearing. Registered as [RuleSpace] §5 Proposition 5.2, row
RS-12, and at every speed `1 / (2 ^ m - 1)` as [RuleSpace] §5 Proposition 5.3, row RS-13. One
step of rule `90` sends the seed at cell `1` to the two-cell seed at cells `0` and `2`, so the orbit
of that two-cell seed is the single seed's orbit one step later, moved one cell right
(`f90_pair_iterate_apply`). The ray of speed `1 / 3` from cell `1` then reads, at step `t`, the
single seed at step `t + 1` and cell `⌊t / 3⌋`: at two of three steps the sum of step and cell is
odd and the value is `0` by parity (`f90_single_apply_eq_zero_of_odd`), and at the third the step
and cell are `a + b` and `a - b` for a pair `a`, `b` that shares a binary digit.

"Leaf" is file-local vocabulary: the one condition on which the parent below rests is a named
proposition.

* **A zero at every pair sharing a binary digit** (`ZeroOfShared`): when `a` and `b` share a
  binary digit, rule `90` from the single seed reads `0` at cell `a - b` at step `a + b`. It is
  the converse of `RationalRayNinety.oneOfDisjoint`, stated here as a hypothesis.

## Main results

* `tableRule_f90_single_one` — one step of rule `90` sends the seed at cell `1` to the seed at
  cells `0` and `2`.
* `f90_pair_iterate_apply` — the orbit of the two-cell seed is the single seed's orbit one step
  later, moved one cell right.
* `f90_single_apply_eq_zero_of_odd` — the single seed's orbit reads `0` where step plus cell is
  odd.
* `observedRationalRay_f90_pair_eq_zero_of` — **the parent**: given `ZeroOfShared`, the ray of
  speed `1 / 3` from cell `1` from the two-cell seed reads `0` at every step.
* `eventuallyPeriodic_observedRationalRay_f90_pair_of` — that ray is eventually periodic.
* `zeroOfShared` — the condition holds: the converse half of the digit criterion
  `PascalColumns.step_rule90_single_eq_one_iff`, as for `oneOfDisjoint`.
* `observedRationalRay_f90_pair_eq_zero`, `eventuallyPeriodic_observedRationalRay_f90_pair` —
  the parent and its consequence with the condition discharged.
-/

@[expose] public section

namespace RationalRaySeeds

open ExtremeTapWidth EndpointClasses
open ObservedColumn (observedRationalRay hq90)

/-- **A zero at every pair sharing a binary digit**: when `a` and `b` share a binary digit, rule
90 from the single seed reads `0` at cell `a - b` at step `a + b`. The converse of
`RationalRayNinety.oneOfDisjoint`. -/
def ZeroOfShared : Prop :=
  ∀ a b : ℕ, a &&& b ≠ 0 →
    ((tableRule f90 hq90)^[a + b] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) ((a : ℤ) - b) = 0

/-- One step of rule 90 sends the seed at cell `1` to the seed at cells `0` and `2`. -/
theorem tableRule_f90_single_one :
    tableRule f90 hq90 (Finsupp.single (1 : ℤ) (1 : ZMod 2))
      = Finsupp.single (0 : ℤ) 1 + Finsupp.single (2 : ℤ) 1 := by
  ext i
  rw [tableRule_apply]
  simp only [f90, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h0 : i = 0
  · subst h0; simp
  by_cases h2 : i = 2
  · subst h2; simp
  by_cases e1 : (1 : ℤ) = i - 1
  · omega
  by_cases e2 : (1 : ℤ) = i + 1
  · omega
  simp [e1, e2, Ne.symm h0, Ne.symm h2]

/-- A translated seed has the translated orbit. -/
private theorem iterate_translate (t : ℕ) :
    ∀ (s s' : ℤ →₀ ZMod 2), (∀ x, s' x = s (x - 1)) →
      ∀ x, ((tableRule f90 hq90)^[t] s') x = ((tableRule f90 hq90)^[t] s) (x - 1) := by
  induction t with
  | zero => intro s s' h x; exact h x
  | succ t ih =>
    intro s s' h x
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine ih _ _ ?_ x
    intro y
    rw [tableRule_apply, tableRule_apply, h, h, h]
    congr 2
    ring_nf

/-- The orbit of the two-cell seed is the single seed's orbit one step later, moved one cell
right: its value at cell `x` is the single seed's at cell `x - 1`. -/
theorem f90_pair_iterate_apply (t : ℕ) (x : ℤ) :
    ((tableRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (2 : ℤ) 1)) x
      = ((tableRule f90 hq90)^[t + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (x - 1) := by
  rw [← tableRule_f90_single_one, ← Function.iterate_succ_apply]
  refine iterate_translate (t + 1) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
    (Finsupp.single (1 : ℤ) (1 : ZMod 2)) ?_ x
  intro y
  simp only [Finsupp.single_apply]
  by_cases h : y = 1
  · subst h; simp
  · have : ¬ (0 : ℤ) = y - 1 := by omega
    simp [this, Ne.symm h]

/-- The single seed's orbit reads `0` where step plus cell is odd. -/
theorem f90_single_apply_eq_zero_of_odd (t : ℕ) (x : ℤ) (h : ¬ 2 ∣ ((t : ℤ) + x)) :
    ((tableRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x = 0 := by
  induction t generalizing x with
  | zero =>
    have hx : x ≠ 0 := by intro h0; subst h0; simp at h
    simp [Ne.symm hx]
  | succ t ih =>
    rw [Function.iterate_succ_apply', tableRule_apply]
    have h1 := ih (x - 1) (by push_cast at h ⊢; omega)
    have h2 := ih (x + 1) (by push_cast at h ⊢; omega)
    simp [f90, h1, h2]

private theorem exists_shared_bit (c : ℕ) (hc : 0 < c) :
    ∃ j, (2 * c - 1).testBit j = true ∧ c.testBit j = true := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases Nat.even_or_odd' c with ⟨d, rfl | rfl⟩
    · have hd : 0 < d := by omega
      obtain ⟨j, hj1, hj2⟩ := ih d (by omega) hd
      refine ⟨j + 1, ?_, ?_⟩
      · have : 2 * (2 * d) - 1 = 2 * (2 * d - 1) + 1 := by omega
        rw [this, Nat.testBit_succ]
        have e : (2 * (2 * d - 1) + 1) / 2 = 2 * d - 1 := by omega
        rw [e]; exact hj1
      · rw [Nat.testBit_succ]; simpa using hj2
    · refine ⟨0, ?_, ?_⟩
      · have : 2 * (2 * d + 1) - 1 = 2 * (2 * d) + 1 := by omega
        rw [this]; simp
      · simp

private theorem and_ne_zero_two_mul_sub (c : ℕ) (hc : 0 < c) : (2 * c - 1) &&& c ≠ 0 := by
  obtain ⟨j, h1, h2⟩ := exists_shared_bit c hc
  intro h
  have := congrArg (fun z => z.testBit j) h
  simp [Nat.testBit_and, h1, h2] at this

/-- Given `ZeroOfShared`, the ray of speed `1 / 3` from cell `1` from the two-cell seed reads `0`
at every step. Rests on `[RuleSpace] §5 Proposition 5.1`'s single-seed hypothesis being
load-bearing: from this seed the ray is constant. -/
theorem observedRationalRay_f90_pair_eq_zero_of (h : ZeroOfShared) (t : ℕ) :
    observedRationalRay (tableRule f90 hq90)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (2 : ℤ) 1) 1 3 1 t = 0 := by
  unfold observedRationalRay
  rw [f90_pair_iterate_apply]
  have hx : ((1 * t / 3 : ℕ) : ℤ) = ((t / 3 : ℕ) : ℤ) := by simp
  rw [hx, show (1 : ℤ) + ((t / 3 : ℕ) : ℤ) - 1 = ((t / 3 : ℕ) : ℤ) by ring]
  have hr : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · apply f90_single_apply_eq_zero_of_odd
    push_cast; omega
  · have key := h (2 * (t / 3) + 1) (t / 3 + 1)
      (by
        have := and_ne_zero_two_mul_sub (t / 3 + 1) (by omega)
        rwa [show 2 * (t / 3 + 1) - 1 = 2 * (t / 3) + 1 by omega] at this)
    have e1 : 2 * (t / 3) + 1 + (t / 3 + 1) = t + 1 := by omega
    have e2 : ((2 * (t / 3) + 1 : ℕ) : ℤ) - ((t / 3 + 1 : ℕ) : ℤ) = ((t / 3 : ℕ) : ℤ) := by
      push_cast; ring
    rwa [e1, e2] at key
  · apply f90_single_apply_eq_zero_of_odd
    push_cast; omega

/-- Given `ZeroOfShared`, the ray of speed `1 / 3` from cell `1` from the two-cell seed is
eventually periodic: it is constantly `0`. -/
theorem eventuallyPeriodic_observedRationalRay_f90_pair_of (h : ZeroOfShared) :
    GrowingComposite.EventuallyPeriodic
      (observedRationalRay (tableRule f90 hq90)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (2 : ℤ) 1) 1 3 1) :=
  ⟨1, 0, one_pos, fun u _ => by
    rw [observedRationalRay_f90_pair_eq_zero_of h, observedRationalRay_f90_pair_eq_zero_of h]⟩

/-- **A zero at every pair sharing a binary digit**: when `a` and `b` share a binary digit, rule 90
from the single seed reads `0` at cell `a - b` at step `a + b`. The converse of
`RationalRayNinety.oneOfDisjoint`, so that with it the single seed's value at cell `a - b`, step
`a + b` is `1` exactly when the two share no binary digit. -/
theorem zeroOfShared : ZeroOfShared := by
  intro a b hab
  have h : ¬ ((LocalRuleColumns.step LocalRuleColumns.rule90)^[a + b]
      (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) ((a : ℤ) - b) = 1 := fun h1 =>
    hab ((PascalColumns.step_rule90_single_eq_one_iff a b).mp h1)
  have e := congrFun (ObservedColumn.coe_tableRule_iterate f90 hq90 (a + b)
    (Finsupp.single (0 : ℤ) (1 : ZMod 2))) ((a : ℤ) - b)
  rw [Finsupp.single_eq_pi_single] at e
  have hz : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
  exact e.trans (hz _ h)

/-- From the two-cell seed, the ray of speed `1 / 3` from cell `1` reads `0` at every step. This
shows the single-seed hypothesis of `[RuleSpace] §5 Proposition 5.1` load-bearing: from this seed
the ray is constant. -/
theorem observedRationalRay_f90_pair_eq_zero (t : ℕ) :
    observedRationalRay (tableRule f90 hq90)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (2 : ℤ) 1) 1 3 1 t = 0 :=
  observedRationalRay_f90_pair_eq_zero_of zeroOfShared t

/-- From the two-cell seed, the ray of speed `1 / 3` from cell `1` is eventually periodic, being
constantly `0`. This shows the single-seed hypothesis of `[RuleSpace] §5 Proposition 5.1`
load-bearing. -/
theorem eventuallyPeriodic_observedRationalRay_f90_pair :
    GrowingComposite.EventuallyPeriodic
      (observedRationalRay (tableRule f90 hq90)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (2 : ℤ) 1) 1 3 1) :=
  eventuallyPeriodic_observedRationalRay_f90_pair_of zeroOfShared

/-- Arithmetic on naturals: if `a` is not divisible by `2 ^ k`, then `a` and `a - a / 2 ^ k` share a
binary digit. The sum `a + (a - a / 2 ^ k)` and difference `a / 2 ^ k` are the step and cell of a
zero of rule 90 from the single seed at every speed `1 / (2 ^ m - 1)`
(`[RuleSpace] §5 Proposition 5.3`). -/
theorem and_sub_div_two_pow_ne_zero (k a : ℕ) (ha : a % 2 ^ k ≠ 0) :
    a &&& (a - a / 2 ^ k) ≠ 0 := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  by_cases hlt : a < 2 ^ k
  · rw [Nat.div_eq_of_lt hlt, Nat.sub_zero, Nat.and_self]
    rintro rfl
    simp at ha
  · have hlt := not_lt.mp hlt
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨h, hlo, hhi⟩ : ∃ h, 2 ^ h ≤ a ∧ a < 2 ^ (h + 1) :=
      ⟨Nat.log 2 a, Nat.pow_log_le_self 2 ha0, Nat.lt_pow_succ_log_self (by norm_num) _⟩
    have hkh : k ≤ h := by
      have h1 : 2 ^ k < 2 ^ (h + 1) := lt_of_le_of_lt hlt hhi
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
      omega
    obtain ⟨p, rfl⟩ : ∃ p, h = p + k := ⟨h - k, by omega⟩
    obtain ⟨a', hape⟩ : ∃ a', a = 2 ^ (p + k) + a' := ⟨a - 2 ^ (p + k), by omega⟩
    have ha'lt : a' < 2 ^ (p + k) := by rw [pow_succ] at hhi; omega
    have hpk : 2 ^ (p + k) = 2 ^ k * 2 ^ p := by rw [pow_add]; ring
    have hkpos : 0 < 2 ^ k := by positivity
    have hdiv : a / 2 ^ k = 2 ^ p + a' / 2 ^ k := by
      rw [hape, hpk, Nat.mul_add_div hkpos]
    have hmod : a' % 2 ^ k ≠ 0 := by
      intro h0
      apply ha
      rw [hape, hpk, Nat.mul_add_mod]
      exact h0
    have ha'le : a' / 2 ^ k ≤ a' := Nat.div_le_self _ _
    have ha'a : a' < a := by have : 0 < 2 ^ (p + k) := by positivity
                             omega
    obtain ⟨r, hr⟩ : ∃ r, 2 ^ k = r + 1 := ⟨2 ^ k - 1, by omega⟩
    have e : 2 ^ k * 2 ^ p = 2 ^ p * r + 2 ^ p := by rw [hr]; ring
    have hb : a - a / 2 ^ k = 2 ^ p * r + (a' - a' / 2 ^ k) := by
      rw [hdiv, hape, hpk, e]
      omega
    have hrb : r = 2 ^ k - 1 := by omega
    have ih' := ih a' ha'a hmod
    generalize hb' : a' - a' / 2 ^ k = b' at hb ih'
    intro hand
    -- `b` lacks the top bit of `a`, so `b < 2 ^ (p + k)`
    have hbt : a - a / 2 ^ k < 2 ^ (p + k) := by
      by_contra hcon
      have hcon := not_lt.mp hcon
      have hble : a - a / 2 ^ k ≤ a := Nat.sub_le _ _
      obtain ⟨b'', hb''⟩ : ∃ b'', a - a / 2 ^ k = 2 ^ (p + k) + b'' :=
        ⟨a - a / 2 ^ k - 2 ^ (p + k), by omega⟩
      have hb''lt : b'' < 2 ^ (p + k) := by rw [pow_succ] at hhi; omega
      have ta : a.testBit (p + k) = true := by
        rw [hape, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha'lt]; rfl
      have tb : (a - a / 2 ^ k).testBit (p + k) = true := by
        rw [hb'', Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hb''lt]; rfl
      have := congrArg (fun z => z.testBit (p + k)) hand
      simp only [Nat.testBit_and, ta, tb] at this
      simp at this
    have hb'lt : b' < 2 ^ p := by
      rw [hb, hpk, e] at hbt
      omega
    -- `b` holds the bits `p, …, p + k - 1`
    have hbbit : ∀ j, j < k → (a - a / 2 ^ k).testBit (p + j) = true := by
      intro j hj
      have hnl : ¬ (p + j < p) := by omega
      rw [hb, Nat.testBit_two_pow_mul_add r hb'lt]
      simp only [hnl, ↓reduceIte]
      rw [show p + j - p = j by omega, hrb, Nat.testBit_two_pow_sub_one]
      simp [hj]
    have habit : ∀ j, j < k → a.testBit (p + j) = false := by
      intro j hj
      have := congrArg (fun z => z.testBit (p + j)) hand
      simp only [Nat.testBit_and, hbbit j hj, Nat.zero_testBit] at this
      simpa using this
    -- hence `a' < 2 ^ p`
    have hep : a' / 2 ^ p = 0 := by
      have hlt2 : a' / 2 ^ p < 2 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        rw [hpk] at ha'lt
        linarith
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.zero_testBit]
      by_cases hj : j < k
      · have h1 := habit j hj
        have hsplit : a = 2 ^ p * (2 ^ k + a' / 2 ^ p) + a' % 2 ^ p := by
          have h3 := Nat.div_add_mod a' (2 ^ p)
          rw [hape, hpk, mul_add]
          rw [Nat.mul_comm (2 ^ k) (2 ^ p)]
          omega
        have hnl : ¬ (p + j < p) := by omega
        rw [hsplit, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))] at h1
        simp only [hnl, ↓reduceIte] at h1
        rw [show p + j - p = j by omega, Nat.testBit_two_pow_add_gt hj] at h1
        exact h1
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt2 (Nat.pow_le_pow_right (by norm_num)
          (by omega)))
    have ha'p : a' < 2 ^ p := by
      rwa [Nat.div_eq_zero_iff_lt (by positivity)] at hep
    apply ih'
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < p
    · have h1 := congrArg (fun z => z.testBit i) hand
      simp only [Nat.testBit_and, Nat.zero_testBit] at h1
      have ea : a = 2 ^ p * 2 ^ k + a' := by rw [hape, hpk, Nat.mul_comm]
      have ta : a.testBit i = a'.testBit i := by
        rw [ea, Nat.testBit_two_pow_mul_add _ ha'p]
        simp only [hi, ↓reduceIte]
      have tb : (a - a / 2 ^ k).testBit i = b'.testBit i := by
        rw [hb, Nat.testBit_two_pow_mul_add _ hb'lt]
        simp only [hi, ↓reduceIte]
      rw [ta, tb] at h1
      exact h1
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha'p (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp

/-- The single seed's orbit reads `0` along the line of cells `⌊(s - 1) / (2 ^ m - 1)⌋` at step
`s ≥ 1`, for every `m ≥ 2` (`[RuleSpace] §5 Proposition 5.3`): at an even remainder by parity, at an
odd one because step and cell are the sum and difference of two numbers sharing a binary digit. -/
theorem f90_single_apply_zeroLine (m s : ℕ) (hm : 2 ≤ m) (hs : 1 ≤ s) :
    ((tableRule f90 hq90)^[s] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
      (((s - 1) / (2 ^ m - 1) : ℕ) : ℤ) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  obtain ⟨W, hW⟩ : ∃ W, W = 2 ^ k := ⟨_, rfl⟩
  have hW2 : 2 ≤ W := by
    rw [hW]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2m : 2 ^ (k + 1) = 2 * W := by rw [pow_succ, ← hW]; ring
  have hq : 2 ^ (k + 1) - 1 = 2 * W - 1 := by rw [h2m]
  rw [hq]
  obtain ⟨q, hqd⟩ : ∃ q, q = 2 * W - 1 := ⟨_, rfl⟩
  rw [← hqd]
  have hqpos : 0 < q := by omega
  obtain ⟨n, hn⟩ : ∃ n, n = (s - 1) / q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = (s - 1) % q := ⟨_, rfl⟩
  have hrq : r < q := by rw [hr]; exact Nat.mod_lt _ hqpos
  have hdm : q * n + r = s - 1 := by rw [hn, hr]; exact Nat.div_add_mod _ _
  have hqn : q * n + n = 2 * (W * n) := by
    calc q * n + n = (q + 1) * n := by ring
      _ = 2 * (W * n) := by rw [show q + 1 = 2 * W by omega]; ring
  rw [← hn]
  rcases Nat.even_or_odd' r with ⟨c, hc | hc⟩
  · apply f90_single_apply_eq_zero_of_odd
    intro hdv
    have : 2 ∣ s + n := by exact_mod_cast hdv
    omega
  · -- odd remainder: `r = 2 c + 1`, `u = c + 1`
    have hcW : c + 1 < W := by omega
    have hWn : n ≤ W * n := Nat.le_mul_of_pos_left n (by omega)
    obtain ⟨a, ha⟩ : ∃ a, a = W * n + (c + 1) := ⟨_, rfl⟩
    have hmod : a % 2 ^ k = c + 1 := by
      rw [← hW, ha, Nat.mul_add_mod, Nat.mod_eq_of_lt hcW]
    have hdiv : a / 2 ^ k = n := by
      rw [← hW, ha, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hcW, add_zero]
    have hsh := and_sub_div_two_pow_ne_zero k a (by rw [hmod]; omega)
    rw [hdiv] at hsh
    have hz := zeroOfShared a (a - n) hsh
    have e1 : a + (a - n) = s := by omega
    have e2 : ((a : ℤ) - ((a - n : ℕ) : ℤ)) = (n : ℤ) := by
      have : n ≤ a := by omega
      push_cast [this]; ring
    rw [e1, e2] at hz
    exact hz

/-- The statement of `f90_single_apply_zeroLine` is satisfiable at `m = 2`, `s = 1`. -/
theorem f90_single_apply_zeroLine_nonvacuous :
    2 ≤ 2 ∧ 1 ≤ 1 ∧
      ((tableRule f90 hq90)^[1] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (((1 - 1) / (2 ^ 2 - 1) : ℕ) : ℤ) = 0 :=
  ⟨le_rfl, le_rfl, f90_single_apply_zeroLine 2 1 le_rfl le_rfl⟩

/-- From the two-cell seed, the ray of speed `1 / (2 ^ m - 1)` from cell `1` reads `0` at every
step, for every `m ≥ 2` (`[RuleSpace] §5 Proposition 5.3`); the case `m = 2` is
`observedRationalRay_f90_pair_eq_zero`. -/
theorem observedRationalRay_f90_pair_eq_zero_pow (m t : ℕ) (hm : 2 ≤ m) :
    observedRationalRay (tableRule f90 hq90)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (2 : ℤ) 1) 1 (2 ^ m - 1) 1 t = 0 := by
  unfold observedRationalRay
  rw [f90_pair_iterate_apply]
  have hx : (1 : ℤ) + ((1 * t / (2 ^ m - 1) : ℕ) : ℤ) - 1
      = (((t + 1 - 1) / (2 ^ m - 1) : ℕ) : ℤ) := by
    simp
  rw [hx]
  exact f90_single_apply_zeroLine m (t + 1) hm (by omega)

/-- A translated seed has the translated orbit, for a shift by any integer. -/
private theorem iterate_translate_int (c : ℤ) (t : ℕ) :
    ∀ (s s' : ℤ →₀ ZMod 2), (∀ x, s' x = s (x - c)) →
      ∀ x, ((tableRule f90 hq90)^[t] s') x = ((tableRule f90 hq90)^[t] s) (x - c) := by
  induction t with
  | zero => intro s s' h x; exact h x
  | succ t ih =>
    intro s s' h x
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine ih _ _ ?_ x
    intro y
    rw [tableRule_apply, tableRule_apply, h, h, h]
    congr 2 <;> ring

/-- The zero lines are the rays they empty: from the single seed at cell `-j` advanced
`(2 ^ m - 1) j + 1` steps, the ray of speed `1 / (2 ^ m - 1)` from cell `0` reads `0` at every
step (`[RuleSpace] §5 Proposition 5.3`). -/
theorem observedRationalRay_f90_zeroLine (m j t : ℕ) (hm : 2 ≤ m) :
    observedRationalRay (tableRule f90 hq90)
      ((tableRule f90 hq90)^[(2 ^ m - 1) * j + 1] (Finsupp.single (-(j : ℤ)) (1 : ZMod 2)))
      1 (2 ^ m - 1) 0 t = 0 := by
  unfold observedRationalRay
  rw [← Function.iterate_add_apply]
  rw [iterate_translate_int (-(j : ℤ)) _ (Finsupp.single (0 : ℤ) (1 : ZMod 2))
    (Finsupp.single (-(j : ℤ)) (1 : ZMod 2)) ?_]
  · have hq : 0 < 2 ^ m - 1 := by
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    have hx : (0 : ℤ) + ((1 * t / (2 ^ m - 1) : ℕ) : ℤ) - -(j : ℤ)
        = (((t + (2 ^ m - 1) * j + 1 - 1) / (2 ^ m - 1) : ℕ) : ℤ) := by
      rw [show t + (2 ^ m - 1) * j + 1 - 1 = t + (2 ^ m - 1) * j by omega,
        Nat.add_mul_div_left _ _ hq, one_mul]
      push_cast; ring
    rw [hx]
    exact f90_single_apply_zeroLine m _ hm (by omega)
  · intro y
    simp only [Finsupp.single_apply]
    have : ((0 : ℤ) = y - -(j : ℤ)) ↔ (-(j : ℤ) = y) := by omega
    simp only [this]

end RationalRaySeeds

/-- info: 'RationalRaySeeds.tableRule_f90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.tableRule_f90_single_one

/-- info: 'RationalRaySeeds.f90_pair_iterate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.f90_pair_iterate_apply

/-- info: 'RationalRaySeeds.f90_single_apply_eq_zero_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.f90_single_apply_eq_zero_of_odd

/-- info: 'RationalRaySeeds.observedRationalRay_f90_pair_eq_zero_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.observedRationalRay_f90_pair_eq_zero_of

/-- info: 'RationalRaySeeds.eventuallyPeriodic_observedRationalRay_f90_pair_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.eventuallyPeriodic_observedRationalRay_f90_pair_of

/-- info: 'RationalRaySeeds.zeroOfShared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.zeroOfShared

/-- info: 'RationalRaySeeds.observedRationalRay_f90_pair_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.observedRationalRay_f90_pair_eq_zero

/-- info: 'RationalRaySeeds.eventuallyPeriodic_observedRationalRay_f90_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.eventuallyPeriodic_observedRationalRay_f90_pair

/-- info: 'RationalRaySeeds.and_sub_div_two_pow_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.and_sub_div_two_pow_ne_zero

/-- info: 'RationalRaySeeds.f90_single_apply_zeroLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.f90_single_apply_zeroLine

/-- info: 'RationalRaySeeds.f90_single_apply_zeroLine_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.f90_single_apply_zeroLine_nonvacuous

/-- info: 'RationalRaySeeds.observedRationalRay_f90_pair_eq_zero_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.observedRationalRay_f90_pair_eq_zero_pow

/-- info: 'RationalRaySeeds.observedRationalRay_f90_zeroLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRaySeeds.observedRationalRay_f90_zeroLine
