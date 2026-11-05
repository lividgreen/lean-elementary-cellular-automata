module

public import ECA.RationalRayRule90
public import ECA.ObservedColumn
public import ECA.EndpointClasses
public import ErgodicTheory.LocalRuleColumns

/-!
# Rays of rule `150` from the single seed
([RuleSpace] §5, transferring Proposition 5.1)

[RuleSpace] §5 Proposition 5.1 makes every ray of rule `90` from the single seed at a speed
strictly between rest and one not eventually periodic, by a one past every step and zero runs of
every length past every step. This file proves the two conditions for rule `150`, whose rule
`f a b c = a + b + c` is linear: zero runs of every length past every step at every speed
strictly between rest and one, and a one past every step at every such speed, by cases on the
speed `p / q` in lowest terms: above one half, below one third, a denominator that is not a power
of two, and a dyadic speed from one third to one half. So the rays of rule `150` from the single
seed are not eventually periodic at every speed strictly between rest and one, from every cell
([RuleSpace] §5 Propositions 5.33, 5.35 and 5.36).
The route is the two-power identity of a linear rule: `2 ^ j` steps of rule `150` read the three
cells at distance `0` and `2 ^ j`, which makes the center column a one at every step and the
column at cell `2 ^ k` a one throughout the steps `[2 ^ k, 2 ^ (k + 1))`; below speed one third
the front cell of step `s` gives the ones at the step `2 ^ k + s`; the row at step
`2 ^ m - 1` reads modulo three, which gives the ones off the powers of two; and at a dyadic speed
the rows at the steps `2 ^ k - 1` and `3 * 2 ^ m - 1` read modulo three, which gives the ones that
the rows `2 ^ k - 1` alone miss at some cells.

## Main results

* `hq150` — rule `150` is quiescent; `iterate_two_pow_f150` — `2 ^ j` steps of rule `150` in one
  identity, a sum of three cells.
* `f150_single_apply_zero` — the center column of rule `150` from the single seed reads `1` at
  every step; `f150_single_apply_two_pow` — the column at cell `2 ^ k` reads `1` at every step of
  `[2 ^ k, 2 ^ (k + 1))`.
* `exists_late_one_observedRationalRay_f150_single` — a ray of speed `p / q` with
  `p < q < 2 * p` reads a one past every step, at the cell `2 ^ k` for a large `k`.
* `lateZeroRuns_f150` — a ray of speed `p / q` with `0 < p < q` reads zero runs of every length
  past every step, at a large power of two.
* `not_eventuallyPeriodic_observedRationalRay_f150_single` — **a ray of rule `150` from the single
  seed at a speed `p / q` with `p < q < 2 * p` is not eventually periodic**, from every cell;
  `not_eventuallyPeriodic_observedRationalRay_f150_single_nonvacuous` meets the speed
  hypotheses at speed `2 / 3`.
* `exists_late_one_observedRationalRay_f150_single_of_three_mul_lt` — a ray of speed `p / q` with
  `0 < p` and `3 * p < q` reads a one past every step, at the cell `t - 2 ^ k` of the step `t`.
* `not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt` — **a ray of rule `150`
  from the single seed at a speed `p / q` with `0 < p` and `3 * p < q` is not eventually
  periodic**, from every cell;
  `not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt_nonvacuous` meets the
  speed hypotheses at speed `1 / 4`.
* `not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt_or_lt_two_mul` — both
  ranges in one statement.
* `f150_single_two_pow_sub_one` — the row of rule `150` at step `2 ^ m - 1` reads `0` at the cell
  `x` exactly when `3` divides `2 ^ m - |x|`, for `|x| < 2 ^ m`.
* `exists_two_pow_sub_ray_mod_three_ne` — at a coprime speed `p / q` with `0 < p < q` and `q` not a
  power of two, `3` fails to divide `2 ^ k - (e + p * (2 ^ k - 1) / q)` at arbitrarily large `k`;
  `exists_two_pow_sub_ray_mod_three_ne_guard` — **guard**: at the dyadic speed `7 / 16` from cell
  `1` it divides at every `k ≥ 4`.
* `exists_late_one_observedRationalRay_f150_single_of_not_pow_two` — a ray of such a speed reads a
  one past every step, at the step `2 ^ k - 1`.
* `not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two` — **a ray of rule `150`
  from the single seed at a coprime speed `p / q` with `0 < p < q` and `q` not a power of two is
  not eventually periodic**, from every cell;
  `not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two_nonvacuous` meets the
  hypotheses at speed `2 / 5`, between one third and one half.
* `not_eventuallyPeriodic_observedRationalRay_f150_single_of_coprime` — the three ranges in one
  statement: a coprime speed with `q` not a power of two, or `3 * p < q`, or `q < 2 * p`.
* `f150_single_three_mul_two_pow_sub_one` — the row of rule `150` at step `3 * 2 ^ m - 1` reads
  `0` at the cell `x` exactly when `3` divides `2 ^ m - |x - 2 ^ (m + 1)|`, for
  `|x - 2 ^ (m + 1)| < 2 ^ m`.
* `exists_late_one_observedRationalRay_f150_single_of_dyadic` — a ray of speed `p / 2 ^ r` with
  `p` odd and `2 * p ≤ 2 ^ r < 3 * p` reads a one past every step, at a step `2 ^ k - 1` or
  `3 * 2 ^ m - 1`.
* `not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt` — **a ray of rule `150` from the
  single seed at every speed `p / q` with `0 < p < q` is not eventually periodic**, from every
  cell; `not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt_nonvacuous` meets the
  hypotheses at speed `7 / 16` from cell `1`, where every row `2 ^ k - 1` misses.
* `observedRationalRay_f150_single_guard_zero` and `observedRationalRay_f150_single_guard_one` —
  **guards**: at speed zero and at speed one from cell `0` the ray reads `1` at every step, so
  it is eventually periodic.
* `card_ones_observedRationalRay_f150_single_half_guard` — **guard**: the ray of speed `1 / 2`
  from cell `1` reads `1` at eleven of the first sixteen steps, where the ceiling
  `q * F(K + 1)` of [RuleSpace] §5 Proposition 5.5(ii) at `q = 2` and `F(5) = 5` is `10`.
-/

@[expose] public section

namespace ECA

open LocalRule

/-- Rule `150` is quiescent. -/
theorem hq150 : f150 0 0 0 = 0 := by decide

/-! ## Piece 1: the two-power identity -/

/-- **`2 ^ j` steps of rule `150`, in one identity** ([RuleSpace] §5): the iterate reads the sum of
the three cells at distance `2 ^ j` and `0`, the squaring identity of a linear rule over `ZMod 2`
at the taps `(1, 1, 1)`. -/
theorem iterate_two_pow_f150 (j : ℕ) (s : FiniteConfiguration) (i : ℤ) :
    ((finRule f150 hq150)^[2 ^ j] s) i = s (i - 2 ^ j) + s i + s (i + 2 ^ j) := by
  have hf : f150 = fun a b c => (1 : ZMod 2) * a + 1 * b + 1 * c := by
    funext a b c
    simp [f150]
  refine (congrFun (coe_finRule_iterate f150 hq150 (2 ^ j) s) i).trans ?_
  rw [hf]
  rw [LocalRuleColumns.iterate_two_pow_step_linear 1 1 1 j ⇑s i]
  simp

/-- outside the light cone the single seed's orbit under rule `150` is zero -/
private theorem f150_single_apply_eq_zero_of_lt (t : ℕ) (i : ℤ) (h : (t : ℤ) < |i|) :
    ((finRule f150 hq150)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i = 0 := by
  induction t generalizing i with
  | zero =>
      have hi : i ≠ 0 := by
        intro h0; subst h0; simp at h
      simp [Ne.symm hi]
  | succ t ih =>
      rw [Function.iterate_succ_apply', finRule_apply]
      have h1 := ih (i - 1) (by push_cast at h; rw [lt_abs] at h ⊢; omega)
      have h2 := ih i (by push_cast at h; rw [lt_abs] at h ⊢; omega)
      have h3 := ih (i + 1) (by push_cast at h; rw [lt_abs] at h ⊢; omega)
      rw [h1, h2, h3]
      exact hq150

/-- `2 ^ M` further steps split the orbit into three translated copies -/
private theorem f150_iterate_two_pow_add (M t : ℕ) (s : FiniteConfiguration) (i : ℤ) :
    ((finRule f150 hq150)^[2 ^ M + t] s) i =
      ((finRule f150 hq150)^[t] s) (i - 2 ^ M) + ((finRule f150 hq150)^[t] s) i +
        ((finRule f150 hq150)^[t] s) (i + 2 ^ M) := by
  rw [Function.iterate_add_apply, iterate_two_pow_f150]

/-! ## Piece 2: the center column -/

/-- **The center column of rule `150` from the single seed reads `1` at every step**
([RuleSpace] §5): at `t = 2 ^ k + s` with `s < 2 ^ k` the identity reads the cell `0` of step `s`
and two cells outside its light cone. -/
theorem f150_single_apply_zero (t : ℕ) :
    ((finRule f150 hq150)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 1 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · set k : ℕ := Nat.log 2 t with hk
      have h1 : 2 ^ k ≤ t := Nat.pow_log_le_self 2 (by omega)
      have h2 : t < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
      have hs : t - 2 ^ k < 2 ^ k := by rw [pow_succ] at h2; omega
      have hpos : 0 < 2 ^ k := by positivity
      have hlt : t - 2 ^ k < t := by omega
      rw [show t = 2 ^ k + (t - 2 ^ k) by omega, f150_iterate_two_pow_add,
        ih _ hlt]
      have hz : ((t - 2 ^ k : ℕ) : ℤ) < ((2 : ℤ) ^ k) := by exact_mod_cast hs
      rw [f150_single_apply_eq_zero_of_lt _ (0 - 2 ^ k) (by rw [lt_abs]; right; linarith),
        f150_single_apply_eq_zero_of_lt _ (0 + 2 ^ k) (by rw [lt_abs]; left; linarith)]
      decide

/-! ## Piece 3: the column at cell `2 ^ k` -/

/-- **The column of rule `150` from the single seed at cell `2 ^ k` reads `1` throughout the steps
`2 ^ k` to `2 ^ (k + 1) - 1`** ([RuleSpace] §5): the identity at `2 ^ k` steps reads the center
column of the remaining `s < 2 ^ k` steps and two cells outside their light cone. -/
theorem f150_single_apply_two_pow (k s : ℕ) (hs : s < 2 ^ k) :
    ((finRule f150 hq150)^[2 ^ k + s] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (2 ^ k) = 1 := by
  rw [f150_iterate_two_pow_add, sub_self, f150_single_apply_zero]
  have hz : (s : ℤ) < ((2 : ℤ) ^ k) := by exact_mod_cast hs
  rw [f150_single_apply_eq_zero_of_lt _ (2 ^ k) (by rw [lt_abs]; left; linarith),
    f150_single_apply_eq_zero_of_lt _ (2 ^ k + 2 ^ k) (by rw [lt_abs]; left; linarith)]
  decide


/-! ## Piece 4: a one past every step above speed one half -/

/-- **A one past every step on every ray of rule `150` from the single seed at a speed strictly
between one half and one** ([RuleSpace] §5 Proposition 5.1(i) at rule `150`): at the first step
`t` with the ray's cell equal to `2 ^ k`, for `k` large, the step lies in `[2 ^ k, 2 ^ (k + 1))`,
where the column at cell `2 ^ k` reads `1`; the upper end of that interval is where `q < 2 * p` is
spent. -/
theorem exists_late_one_observedRationalRay_f150_single (p q : ℕ) (hpq : p < q)
    (hqp : q < 2 * p) (e : ℤ) :
    ∀ T : ℕ, ∃ t, T ≤ t ∧
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1 := by
  intro T
  have hp : 0 < p := by omega
  set k : ℕ := T + q * e.natAbs + p with hk
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have hXz : (k : ℤ) < 2 ^ k := by exact_mod_cast hlt
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have he2 : e ≤ (e.natAbs : ℤ) := by rw [habs]; exact le_abs_self e
  have hkz : (k : ℤ) = T + q * e.natAbs + p := by rw [hk]; push_cast; ring
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hT0 : (0 : ℤ) ≤ T := by positivity
  have hqe : (q : ℤ) * -(e.natAbs : ℤ) ≤ q * e := mul_le_mul_of_nonneg_left he1 hq0
  have hqe' : (q : ℤ) * e ≤ q * (e.natAbs : ℤ) := mul_le_mul_of_nonneg_left he2 hq0
  have hq1 : (1 : ℤ) ≤ q := by omega
  have hea : (e.natAbs : ℤ) ≤ q * e.natAbs := by
    have : (0 : ℤ) ≤ e.natAbs := by positivity
    nlinarith
  have hm0 : 0 ≤ (2 : ℤ) ^ k - e := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = 2 ^ k - e :=
    ⟨(2 ^ k - e).toNat, Int.toNat_of_nonneg hm0⟩
  obtain ⟨t, rr, hx, hmod⟩ : ∃ t rr : ℕ, p * t + rr = q * m + p - 1 ∧ rr < p :=
    ⟨(q * m + p - 1) / p, (q * m + p - 1) % p, Nat.div_add_mod _ _, Nat.mod_lt _ hp⟩
  have h1 : q * m ≤ p * t := by omega
  have h2 : p * t < q * m + p := by omega
  have hdiv : p * t / q = m := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; exact h1
    · have : (m + 1) * q = q * m + q := by ring
      omega
  have h1z : (q : ℤ) * m ≤ p * t := by exact_mod_cast h1
  have h2z : (p : ℤ) * t < q * m + p := by exact_mod_cast h2
  have hqm : (q : ℤ) * m = q * 2 ^ k - q * e := by rw [hm]; ring
  have hpq' : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
  have hqp' : (q : ℤ) + 1 ≤ 2 * p := by exact_mod_cast hqp
  have hX : (0 : ℤ) ≤ 2 ^ k := by positivity
  have hlow : (p : ℤ) * 2 ^ k ≤ p * t := by
    have : ((p : ℤ) + 1) * 2 ^ k ≤ q * 2 ^ k := mul_le_mul_of_nonneg_right hpq' hX
    nlinarith
  have hhigh : (p : ℤ) * t < p * 2 ^ (k + 1) := by
    have : ((q : ℤ) + 1) * 2 ^ k ≤ 2 * p * 2 ^ k := mul_le_mul_of_nonneg_right hqp' hX
    rw [pow_succ]
    nlinarith
  have hlow' : 2 ^ k ≤ t := by
    have : p * 2 ^ k ≤ p * t := by exact_mod_cast hlow
    exact Nat.le_of_mul_le_mul_left this hp
  have hhigh' : t < 2 ^ (k + 1) := by
    have : p * t < p * 2 ^ (k + 1) := by exact_mod_cast hhigh
    exact Nat.lt_of_mul_lt_mul_left this
  have hTt : T ≤ t := by
    have : T ≤ k := by omega
    exact this.trans (hlt.le.trans hlow')
  refine ⟨t, hTt, ?_⟩
  have hs : t - 2 ^ k < 2 ^ k := by rw [pow_succ] at hhigh'; omega
  have hcell : e + ((p * t / q : ℕ) : ℤ) = 2 ^ k := by rw [hdiv, hm]; ring
  unfold observedRationalRay
  rw [hcell, show t = 2 ^ k + (t - 2 ^ k) by omega]
  have hc := f150_single_apply_two_pow k (t - 2 ^ k) hs
  exact hc

/-! ## Piece 5: late zero runs -/

/-- **Late zero runs at every speed strictly between rest and one**
([RuleSpace] §5 Proposition 5.1(ii) at rule `150`): at a large power of two `2 ^ B` the orbit
splits into three translated copies, and the ray's cell lies outside the light cones of all three
over the next `n` steps, the middle one because `0 < p` carries the cell past `n`. -/
theorem lateZeroRuns_f150 (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ∀ n T : ℕ, ∃ t₀ : ℕ, T ≤ t₀ ∧ ∀ r < n,
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e
        (t₀ + r) = 0 := by
  intro n T
  set B : ℕ := T + n + q * e.natAbs + 2 * q * n + q with hB
  have hlt : B < 2 ^ B := Nat.lt_two_pow_self
  refine ⟨2 ^ B, by omega, ?_⟩
  intro r hr
  unfold observedRationalRay
  rw [f150_iterate_two_pow_add]
  have hk : q * (p * (2 ^ B + r) / q) ≤ p * (2 ^ B + r) := Nat.mul_div_le _ _
  have hk' : p * (2 ^ B + r) < q * (p * (2 ^ B + r) / q + 1) :=
    Nat.lt_mul_div_succ _ (by omega)
  set k : ℕ := p * (2 ^ B + r) / q with hkdef
  have hkz : (q : ℤ) * k ≤ p * (2 ^ B + r) := by exact_mod_cast hk
  have hkz' : (p : ℤ) * (2 ^ B + r) < q * (k + 1) := by exact_mod_cast hk'
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have he2 : e ≤ (e.natAbs : ℤ) := by rw [habs]; exact le_abs_self e
  have hpq' : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
  have hNz : (B : ℤ) < 2 ^ B := by exact_mod_cast hlt
  have hBz : (B : ℤ) = T + n + q * e.natAbs + 2 * q * n + q := by rw [hB]; push_cast; ring
  have hrz : (r : ℤ) < n := by exact_mod_cast hr
  have hp1 : (1 : ℤ) ≤ p := by omega
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hT0 : (0 : ℤ) ≤ T := by positivity
  have hqe : (q : ℤ) * -(e.natAbs : ℤ) ≤ q * e := mul_le_mul_of_nonneg_left he1 hq0
  have hqe' : (q : ℤ) * e ≤ q * (e.natAbs : ℤ) := mul_le_mul_of_nonneg_left he2 hq0
  have hpr : (p : ℤ) * r ≤ q * n := by
    have : (p : ℤ) * r ≤ q * r := mul_le_mul_of_nonneg_right (by omega) hr0
    have : (q : ℤ) * r ≤ q * n := mul_le_mul_of_nonneg_left hrz.le hq0
    omega
  have hq1 : (1 : ℤ) ≤ q := by omega
  have hea : (e.natAbs : ℤ) ≤ q * e.natAbs := by
    have : (0 : ℤ) ≤ e.natAbs := by positivity
    nlinarith
  have hA : (r : ℤ) < e + k + 2 ^ B := by omega
  have hC : (q : ℤ) * r < q * (2 ^ B - (e + k)) := by
    have h1 : (q : ℤ) * (2 ^ B - (e + k)) = q * 2 ^ B - q * e - q * k := by ring
    have h2 : ((p : ℤ) + 1) * 2 ^ B ≤ q * 2 ^ B :=
      mul_le_mul_of_nonneg_right hpq' (by positivity)
    have h3 : (q : ℤ) * r ≤ q * n := mul_le_mul_of_nonneg_left hrz.le hq0
    nlinarith
  have hD : (r : ℤ) < 2 ^ B - (e + k) := lt_of_mul_lt_mul_left hC hq0
  have hM : (q : ℤ) * r < q * (e + k) := by
    have h1 : (q : ℤ) * (e + k) = q * e + q * k := by ring
    have h2 : (1 : ℤ) * (2 ^ B + r) ≤ p * (2 ^ B + r) :=
      mul_le_mul_of_nonneg_right hp1 (by positivity)
    have h3 : (q : ℤ) * r ≤ q * n := mul_le_mul_of_nonneg_left hrz.le hq0
    have h4 : (q : ℤ) * (k + 1) = q * k + q := by ring
    have h5 : (q : ℤ) * n ≤ q * n := le_rfl
    nlinarith
  have hE : (r : ℤ) < e + k := lt_of_mul_lt_mul_left hM hq0
  have z1 := f150_single_apply_eq_zero_of_lt r (e + k - 2 ^ B) (by rw [lt_abs]; right; linarith)
  have z2 := f150_single_apply_eq_zero_of_lt r (e + k + 2 ^ B) (by rw [lt_abs]; left; exact hA)
  have z3 := f150_single_apply_eq_zero_of_lt r (e + k) (by rw [lt_abs]; left; exact hE)
  rw [z1, z2, z3]
  decide

/-! ## The main statement -/

/-- **A ray of rule `150` from the single seed, at a speed `p / q` with `p < q < 2 * p`, from any
cell, is not eventually periodic** ([RuleSpace] §5 Proposition 5.1 at rule `150`): a one past every
step on the ray and zero runs of every length past every step together rule out a period. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single (p q : ℕ) (hpq : p < q)
    (hqp : q < 2 * p) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_of_late_one_of_late_zero_runs _
    (exists_late_one_observedRationalRay_f150_single p q hpq hqp e)
    (lateZeroRuns_f150 p q (by omega) hpq e)

/-- **Joint satisfiability** of the speed hypotheses of the statement on rule `150`: the ray at
speed `2 / 3` from cell zero is not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_nonvacuous :
    2 < 3 ∧ 3 < 2 * 2 ∧
      ¬ DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 2 3 0) :=
  ⟨by decide, by decide,
    not_eventuallyPeriodic_observedRationalRay_f150_single 2 3 (by decide) (by decide) 0⟩

/-! ## Guards -/

/-- **Guard: at speed zero the ray of rule `150` from the single seed at cell `0` reads `1` at
every step**, the center column, so it is eventually periodic; the speed hypothesis
`p < q < 2 * p` is needed. -/
theorem observedRationalRay_f150_single_guard_zero :
    DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1 0) := by
  have hall : ∀ t,
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      0 1 0 t = 1 := by
    intro t
    unfold observedRationalRay
    simpa using f150_single_apply_zero t
  exact ⟨1, 0, one_pos, fun u _ => by rw [hall, hall]⟩

/-- rule `150` from the single seed: the front cell reads `1` and nothing lies beyond it -/
private theorem f150_single_front (t : ℕ) :
    ((finRule f150 hq150)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (t : ℤ) = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', finRule_apply]
    push_cast
    rw [add_sub_cancel_right, ih,
      f150_single_apply_eq_zero_of_lt t ((t : ℤ) + 1)
        (by rw [abs_of_nonneg (by positivity)]; omega),
      f150_single_apply_eq_zero_of_lt t ((t : ℤ) + 1 + 1)
        (by rw [abs_of_nonneg (by positivity)]; omega)]
    decide

/-- **Guard: at speed one the ray of rule `150` from the single seed at cell `0` reads `1` at
every step**, the front, so it is eventually periodic; the speed hypothesis `p < q` is needed. -/
theorem observedRationalRay_f150_single_guard_one :
    DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 1 0) := by
  have hall : ∀ t,
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      1 1 0 t = 1 := by
    intro t
    unfold observedRationalRay
    simpa using f150_single_front t
  exact ⟨1, 0, one_pos, fun u _ => by rw [hall, hall]⟩

/-- a computable evaluation of the orbit by the two-power identity, with a step budget -/
private def orbit150 : ℕ → ℕ → ℤ → ZMod 2
  | 0, _, _ => 0
  | fuel + 1, t, x =>
    if t = 0 then (if x = 0 then 1 else 0)
    else
      orbit150 fuel (t - 2 ^ Nat.log2 t) (x - 2 ^ Nat.log2 t) +
        orbit150 fuel (t - 2 ^ Nat.log2 t) x +
        orbit150 fuel (t - 2 ^ Nat.log2 t) (x + 2 ^ Nat.log2 t)

/-- the evaluation agrees with the orbit once the budget exceeds the step -/
private theorem orbit150_eq (fuel : ℕ) :
    ∀ (t : ℕ), t < fuel → ∀ x : ℤ,
      orbit150 fuel t x = ((finRule f150 hq150)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x := by
  induction fuel with
  | zero => intro t ht; omega
  | succ fuel ih =>
    intro t ht x
    by_cases h0 : t = 0
    · subst h0
      simp only [orbit150, ite_true, Function.iterate_zero, id_eq, Finsupp.single_apply]
      by_cases hx : x = 0
      · simp [hx]
      · simp [hx, Ne.symm hx]
    · have h1 : 2 ^ Nat.log2 t ≤ t := Nat.log2_self_le h0
      have hpos : 0 < 2 ^ Nat.log2 t := by positivity
      have hlt : t - 2 ^ Nat.log2 t < fuel := by omega
      simp only [orbit150, h0, ite_false]
      rw [ih _ hlt, ih _ hlt, ih _ hlt]
      conv_rhs => rw [show t = 2 ^ Nat.log2 t + (t - 2 ^ Nat.log2 t) by omega]
      rw [f150_iterate_two_pow_add]

/-- **Guard: the ray of speed `1 / 2` from cell `1` reads `1` at eleven of the first sixteen
steps** ([RuleSpace] §5 Proposition 5.5(ii)): the ceiling `q * F(K + 1)` of that proposition at
`q = 2` and `F(5) = 5` is `10`, so it fails at rule `150`. -/
theorem card_ones_observedRationalRay_f150_single_half_guard :
    ((Finset.range 16).filter fun t =>
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 1 t
        = 1).card = 11 := by
  have h : ∀ t ∈ Finset.range 16,
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 1 t =
        orbit150 16 t (1 + ((1 * t / 2 : ℕ) : ℤ)) := by
    intro t ht
    rw [orbit150_eq 16 t (Finset.mem_range.mp ht)]
    rfl
  rw [Finset.filter_congr (fun t ht => by rw [h t ht])]
  decide +kernel

/-! ## Piece 6: a one past every step below speed one third -/

/-- **A one past every step on every ray of rule `150` from the single seed at a speed strictly
between rest and one third** ([RuleSpace] §5 Proposition 5.1(i) at rule `150`): at the first step
`t` with `(q - p) * t ≤ q * (2 ^ k + e) < (q - p) * (t + 1)`, for `k` large, the ray's cell is
`t - 2 ^ k`, which is less than half of `2 ^ k`, where `3 * p < q` is spent; the identity at
`2 ^ k` steps then reads the front cell of step `t - 2 ^ k` and two cells outside its light cone. -/
theorem exists_late_one_observedRationalRay_f150_single_of_three_mul_lt (p q : ℕ) (hp : 0 < p)
    (h3 : 3 * p < q) (e : ℤ) :
    ∀ T : ℕ, ∃ t, T ≤ t ∧
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1 := by
  intro T
  obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
  have hd2 : 2 * p + 1 ≤ d := by omega
  have hd0 : 0 < d := by omega
  set k : ℕ := T + 2 * (p + d) * e.natAbs + 1 with hk
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have hXz : (k : ℤ) < 2 ^ k := by exact_mod_cast hlt
  have hX0 : (0 : ℤ) < 2 ^ k := by positivity
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have he2 : e ≤ (e.natAbs : ℤ) := by rw [habs]; exact le_abs_self e
  have hkz : (k : ℤ) = T + 2 * (p + d) * e.natAbs + 1 := by rw [hk]; push_cast; ring
  have hq0 : (0 : ℤ) ≤ (p : ℤ) + d := by positivity
  have hT0 : (0 : ℤ) ≤ T := by positivity
  have hE0 : (0 : ℤ) ≤ e.natAbs := by positivity
  have hqe : ((p : ℤ) + d) * -(e.natAbs : ℤ) ≤ (p + d) * e := mul_le_mul_of_nonneg_left he1 hq0
  have hqe' : ((p : ℤ) + d) * e ≤ (p + d) * e.natAbs := mul_le_mul_of_nonneg_left he2 hq0
  have hqE : (0 : ℤ) ≤ ((p : ℤ) + d) * e.natAbs := by positivity
  have hX : 2 * ((p : ℤ) + d) * e.natAbs < 2 ^ k := by linarith
  have hea : (e.natAbs : ℤ) ≤ (p + d) * e.natAbs := by
    have : (1 : ℤ) ≤ (p : ℤ) + d := by omega
    nlinarith
  have hm0 : 0 ≤ (2 : ℤ) ^ k + e := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = 2 ^ k + e :=
    ⟨(2 ^ k + e).toNat, Int.toNat_of_nonneg hm0⟩
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℕ, d * t ≤ (p + d) * m ∧ (p + d) * m < d * (t + 1) :=
    ⟨(p + d) * m / d, Nat.mul_div_le _ _, Nat.lt_mul_div_succ _ hd0⟩
  have ht1z : (d : ℤ) * t ≤ (p + d) * (2 ^ k + e) := by
    rw [← hm]; exact_mod_cast ht1
  have ht2z : ((p : ℤ) + d) * (2 ^ k + e) < d * (t + 1) := by
    rw [← hm]; exact_mod_cast ht2
  obtain ⟨u, hu1, hu2⟩ : ∃ u : ℕ, (p + d) * u ≤ p * t ∧ p * t < (p + d) * (u + 1) :=
    ⟨p * t / (p + d), Nat.mul_div_le _ _, Nat.lt_mul_div_succ _ (by omega)⟩
  have hdiv : p * t / (p + d) = u := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm u]; exact hu1
    · rw [Nat.mul_comm (u + 1)]; exact hu2
  have hu1z : ((p : ℤ) + d) * u ≤ p * t := by exact_mod_cast hu1
  have hu2z : (p : ℤ) * t < (p + d) * (u + 1) := by exact_mod_cast hu2
  have hmt : ((p : ℤ) + d) * (t - m) ≤ p * t := by rw [hm]; linarith
  have hmt2 : (p : ℤ) * t < (p + d) * (t - m + 1) := by rw [hm]; linarith
  have hu_a : (t : ℤ) - m < u + 1 := lt_of_mul_lt_mul_left (by linarith) hq0
  have hu_b : (u : ℤ) < t - m + 1 := lt_of_mul_lt_mul_left (by linarith) hq0
  have hu : (u : ℤ) = t - m := by omega
  -- the cell offset `s = t - 2 ^ k`
  have hpX : (2 : ℤ) ^ k ≤ p * 2 ^ k := by
    have : (1 : ℤ) ≤ p := by omega
    nlinarith
  have hdX : ((2 * p + 1 : ℕ) : ℤ) * 2 ^ k ≤ d * 2 ^ k :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hd2) hX0.le
  have hpos : (0 : ℤ) < d * (t - 2 ^ k + 1) := by
    push_cast at hdX
    linarith
  have hs0 : (0 : ℤ) ≤ t - 2 ^ k := by
    have := lt_of_mul_lt_mul_left (by linarith : (d : ℤ) * 0 < d * (t - 2 ^ k + 1)) (by positivity)
    omega
  have hs2 : (d : ℤ) * (2 * (t - 2 ^ k)) < d * 2 ^ k := by
    push_cast at hdX
    linarith
  have hs2' : 2 * ((t : ℤ) - 2 ^ k) < 2 ^ k := lt_of_mul_lt_mul_left hs2 (by positivity)
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = t - 2 ^ k :=
    ⟨((t : ℤ) - 2 ^ k).toNat, Int.toNat_of_nonneg hs0⟩
  have ht_eq : t = 2 ^ k + s := by
    have : (t : ℤ) = 2 ^ k + s := by linarith
    exact_mod_cast this
  refine ⟨t, ?_, ?_⟩
  · have : (T : ℤ) ≤ t := by
      have : (T : ℤ) ≤ k := by linarith
      linarith
    exact_mod_cast this
  have hcell : e + ((p * t / (p + d) : ℕ) : ℤ) = s := by rw [hdiv, hu, hs, hm]; ring
  unfold observedRationalRay
  rw [hcell, ht_eq, f150_iterate_two_pow_add]
  have hs3 : 2 * (s : ℤ) < 2 ^ k := by rw [hs]; exact hs2'
  have z1 := f150_single_apply_eq_zero_of_lt s ((s : ℤ) - 2 ^ k)
    (by rw [lt_abs]; right; linarith)
  have z3 := f150_single_apply_eq_zero_of_lt s ((s : ℤ) + 2 ^ k)
    (by rw [lt_abs]; left; linarith)
  rw [z1, z3, f150_single_front s]
  decide

/-- **A ray of rule `150` from the single seed, at a speed `p / q` with `0 < p` and `3 * p < q`,
from any cell, is not eventually periodic** ([RuleSpace] §5 Proposition 5.1 at rule `150`): a one
past every step on the ray and zero runs of every length past every step together rule out a
period. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt (p q : ℕ)
    (hp : 0 < p) (h3 : 3 * p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_of_late_one_of_late_zero_runs _
    (exists_late_one_observedRationalRay_f150_single_of_three_mul_lt p q hp h3 e)
    (lateZeroRuns_f150 p q hp (by omega) e)

/-- **Joint satisfiability** of the speed hypotheses of the statement below speed one third on
rule `150`: the ray at speed `1 / 4` from cell zero is not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt_nonvacuous :
    0 < 1 ∧ 3 * 1 < 4 ∧
      ¬ DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 4 0) :=
  ⟨by decide, by decide,
    not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt 1 4 (by decide)
      (by decide) 0⟩

/-! ## Piece 7: both ranges in one statement -/

/-- **A ray of rule `150` from the single seed, at a speed `p / q` strictly between rest and one
with `3 * p < q` or `q < 2 * p`, from any cell, is not eventually periodic** ([RuleSpace] §5
Proposition 5.1 and Proposition 5.33 at rule `150`): the speeds below one third and above one
half. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt_or_lt_two_mul
    (p q : ℕ) (hp : 0 < p) (hpq : p < q) (h : 3 * p < q ∨ q < 2 * p) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) := by
  rcases h with h | h
  · exact not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt p q hp h e
  · exact not_eventuallyPeriodic_observedRationalRay_f150_single p q hpq h e

/-! ## Piece 8: the row at step `2 ^ m - 1` -/

/-- **The row of rule `150` from the single seed at step `2 ^ m - 1`, read modulo three**
([RuleSpace] §5): the cell `x` with `|x| < 2 ^ m` reads `0` exactly when `3` divides
`2 ^ m - |x|`, and every cell farther out reads `0` by the light cone. At step `2 ^ (m + 1) - 1`
the two-power identity reads the cells `x - 2 ^ m`, `x` and `x + 2 ^ m` of step `2 ^ m - 1`. -/
theorem f150_single_two_pow_sub_one (m : ℕ) (x : ℤ) (hx : x.natAbs < 2 ^ m) :
    ((finRule f150 hq150)^[2 ^ m - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x =
      if (2 ^ m - x.natAbs) % 3 = 0 then 0 else 1 := by
  induction m generalizing x with
  | zero =>
      have hx0 : x = 0 := by simpa using hx
      subst hx0
      simp
  | succ m ih =>
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have h3 : ¬ 3 ∣ 2 ^ m := by
        intro h
        have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
        omega
      have hsplit : 2 ^ (m + 1) - 1 = 2 ^ m + (2 ^ m - 1) := by rw [pow_succ]; omega
      have key : ∀ y : ℤ,
          ((finRule f150 hq150)^[2 ^ m - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) y =
            if y.natAbs < 2 ^ m then (if (2 ^ m - y.natAbs) % 3 = 0 then 0 else 1) else 0 := by
        intro y
        by_cases hy : y.natAbs < 2 ^ m
        · simp only [hy, ↓reduceIte]
          exact ih y hy
        · simp only [hy, ↓reduceIte]
          apply f150_single_apply_eq_zero_of_lt
          have h1 : (y.natAbs : ℤ) = |y| := Int.natCast_natAbs y
          rw [← h1]
          omega
      rw [hsplit, f150_iterate_two_pow_add, key, key, key]
      have hc : (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) := by push_cast; rfl
      rw [hc, pow_succ] at *
      generalize 2 ^ m = a at *
      have e1 := Int.natAbs_eq x
      have e2 := Int.natAbs_eq (x - (a : ℤ))
      have e3 := Int.natAbs_eq (x + (a : ℤ))
      clear ih key hsplit hc
      generalize x.natAbs = u at *
      generalize (x - (a : ℤ)).natAbs = v at *
      generalize (x + (a : ℤ)).natAbs = w at *
      have ha : a % 3 = 1 ∨ a % 3 = 2 := by omega
      have hu : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
      split_ifs <;> first | decide | (exfalso; omega)

/-! ## Piece 9: the remainder lemma -/

/-- one step of the division of `p * (2 ^ k - 1)` by `q`: doubling the dividend and adding `p` -/
private theorem ray_div_mod_step (p q n : ℕ) (hq : 0 < q) (hpq : p < q) :
    (2 * n + p) / q = 2 * (n / q) + (2 * (n % q) + p) / q ∧
      (2 * n + p) % q = (2 * (n % q) + p) % q ∧ (2 * (n % q) + p) / q < 3 := by
  have h1 : n % q < q := Nat.mod_lt _ hq
  have h2 : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have h3 : q * ((2 * (n % q) + p) / q) + (2 * (n % q) + p) % q = 2 * (n % q) + p :=
    Nat.div_add_mod _ q
  have h4 : (2 * (n % q) + p) % q < q := Nat.mod_lt _ hq
  have h5 : 2 * n + p = q * (2 * (n / q) + (2 * (n % q) + p) / q) +
      (2 * (n % q) + p) % q := by
    rw [Nat.mul_add]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [h5, Nat.mul_add_div hq, Nat.div_eq_of_lt h4, Nat.add_zero]
  · rw [h5, Nat.mul_add_mod, Nat.mod_eq_of_lt h4]
  · apply Nat.div_lt_of_lt_mul
    nlinarith

/-- **A remainder lemma for the cells `p * (2 ^ k - 1) / q`** ([RuleSpace] §5): at a speed `p / q`
with `0 < p < q` coprime and `q` not a power of two, for every offset `e` and every bound `K`
there is an index `k ≥ K` at which `3` does not divide `2 ^ k - (e + p * (2 ^ k - 1) / q)`.
Were `3` to divide it at every index from `K` on, the quotients' increments would be one
residue modulo three, the remainders `p * (2 ^ k - 1) % q` would satisfy the doubling recurrence
`f (k + 1) - c = 2 * (f k - c)`, which bounded values force to the constant `c = q - p`, and that
makes `q` divide `p * 2 ^ K`, so `q` a power of two. -/
theorem exists_two_pow_sub_ray_mod_three_ne (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hcop : Nat.Coprime p q) (hq : ∀ r : ℕ, q ≠ 2 ^ r) (e : ℤ) (K : ℕ) :
    ∃ k, K ≤ k ∧ ((2 : ℤ) ^ k - (e + ((p * (2 ^ k - 1) / q : ℕ) : ℤ))) % 3 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hq0 : 0 < q := by omega
  have hrec : ∀ k : ℕ, p * (2 ^ (k + 1) - 1) = 2 * (p * (2 ^ k - 1)) + p := by
    intro k
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by rw [pow_succ]; omega
    rw [h2]
    ring
  -- the step data
  have hstep : ∀ k : ℕ,
      p * (2 ^ (k + 1) - 1) / q = 2 * (p * (2 ^ k - 1) / q) +
        (2 * (p * (2 ^ k - 1) % q) + p) / q ∧
      p * (2 ^ (k + 1) - 1) % q = (2 * (p * (2 ^ k - 1) % q) + p) % q ∧
      (2 * (p * (2 ^ k - 1) % q) + p) / q < 3 := by
    intro k
    rw [hrec k]
    exact ray_div_mod_step p q _ hq0 hpq
  -- the increment is the residue of `e` modulo three
  have hd : ∀ k : ℕ, K ≤ k →
      (((2 * (p * (2 ^ k - 1) % q) + p) / q : ℕ) : ℤ) = e % 3 := by
    intro k hk
    have h1 := hcon k hk
    have h2 := hcon (k + 1) (by omega)
    rw [(hstep k).1] at h2
    have h3 := (hstep k).2.2
    rw [pow_succ] at h2
    generalize (2 ^ k : ℤ) = P at *
    generalize ((2 * (p * (2 ^ k - 1) % q) + p) / q) = d at *
    generalize p * (2 ^ k - 1) / q = A at *
    push_cast at h2
    omega
  -- the remainders
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = (e % 3) * q - p := ⟨_, rfl⟩
  have hf : ∀ k : ℕ, K ≤ k →
      ((p * (2 ^ (k + 1) - 1) % q : ℕ) : ℤ) - c = 2 * (((p * (2 ^ k - 1) % q : ℕ) : ℤ) - c) := by
    intro k hk
    have h1 := hd k hk
    have h2 : q * ((2 * (p * (2 ^ k - 1) % q) + p) / q) +
        (2 * (p * (2 ^ k - 1) % q) + p) % q = 2 * (p * (2 ^ k - 1) % q) + p :=
      Nat.div_add_mod _ q
    rw [(hstep k).2.1]
    have h3 : ((q * ((2 * (p * (2 ^ k - 1) % q) + p) / q) +
        (2 * (p * (2 ^ k - 1) % q) + p) % q : ℕ) : ℤ) =
        ((2 * (p * (2 ^ k - 1) % q) + p : ℕ) : ℤ) := by rw [h2]
    push_cast at h3 h1
    rw [h1] at h3
    rw [hc]
    push_cast
    linarith
  have hfj : ∀ j : ℕ,
      ((p * (2 ^ (K + j) - 1) % q : ℕ) : ℤ) - c =
        2 ^ j * (((p * (2 ^ K - 1) % q : ℕ) : ℤ) - c) := by
    intro j
    induction j with
    | zero => simp
    | succ j ihj =>
        rw [← add_assoc, hf (K + j) (by omega), ihj, pow_succ]
        ring
  -- the remainder is constant
  have hFK : ((p * (2 ^ K - 1) % q : ℕ) : ℤ) = c := by
    by_contra hne
    set g : ℤ := ((p * (2 ^ K - 1) % q : ℕ) : ℤ) - c with hg
    have hg0 : g ≠ 0 := fun h => hne (by omega)
    have hj := hfj (q + c.natAbs)
    have hlt : (p * (2 ^ (K + (q + c.natAbs)) - 1) % q : ℕ) < q := Nat.mod_lt _ hq0
    have hB : ((q + c.natAbs : ℕ) : ℤ) < 2 ^ (q + c.natAbs) := by
      exact_mod_cast Nat.lt_two_pow_self
    generalize (2 : ℤ) ^ (q + c.natAbs) = w at *
    have hcab : c ≤ |c| := le_abs_self c
    have hcab' : -|c| ≤ c := neg_abs_le c
    have hF0 : (0 : ℤ) ≤ ((p * (2 ^ (K + (q + c.natAbs)) - 1) % q : ℕ) : ℤ) := by positivity
    have hFq : ((p * (2 ^ (K + (q + c.natAbs)) - 1) % q : ℕ) : ℤ) < q := by exact_mod_cast hlt
    push_cast at hB
    have hq0' : (0 : ℤ) ≤ q := by positivity
    have habs0 : 0 ≤ |c| := abs_nonneg c
    have hw : 0 < w := by linarith
    rcases lt_or_gt_of_ne hg0 with hn | hpz
    · have h1 : w * g ≤ w * (-1) := mul_le_mul_of_nonneg_left (by omega) hw.le
      linarith
    · have h1 : w * 1 ≤ w * g := mul_le_mul_of_nonneg_left (by omega) hw.le
      linarith
  -- so the remainder is `q - p`
  have hFq : (p * (2 ^ K - 1) % q : ℕ) < q := Nat.mod_lt _ hq0
  have hmod : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
  have hrem : p * (2 ^ K - 1) % q = q - p := by
    have hFz : ((p * (2 ^ K - 1) % q : ℕ) : ℤ) = c := hFK
    rcases hmod with h | h | h <;> rw [h] at hc <;> omega
  have hdiv : q ∣ p * 2 ^ K := by
    have h1 : q * (p * (2 ^ K - 1) / q) + p * (2 ^ K - 1) % q = p * (2 ^ K - 1) :=
      Nat.div_add_mod _ q
    have h2 : p * 2 ^ K = p * (2 ^ K - 1) + p := by
      have h3 : 2 ^ K = (2 ^ K - 1) + 1 := by have := @Nat.one_le_two_pow K; omega
      conv_lhs => rw [h3]
      ring
    refine ⟨p * (2 ^ K - 1) / q + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hdiv2 : q ∣ 2 ^ K := Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdiv
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv2
  exact hq i hi

/-! ## Piece 10: a one past every step off the powers of two -/

/-- **A one past every step on every ray of rule `150` from the single seed at a coprime speed
`p / q` whose denominator is not a power of two** ([RuleSpace] §5 Proposition 5.1(i) at rule
`150`): at a large `k` the ray's cell at step `2 ^ k - 1` lies in `[0, 2 ^ k)`, and the remainder
lemma chooses `k` so that `3` does not divide `2 ^ k` minus that cell, where the row at that step
reads `1`. -/
theorem exists_late_one_observedRationalRay_f150_single_of_not_pow_two (p q : ℕ) (hp : 0 < p)
    (hpq : p < q) (hcop : Nat.Coprime p q) (hq : ∀ r : ℕ, q ≠ 2 ^ r) (e : ℤ) :
    ∀ T : ℕ, ∃ t, T ≤ t ∧
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1 := by
  intro T
  obtain ⟨k, hkK, hk3⟩ := exists_two_pow_sub_ray_mod_three_ne p q hp hpq hcop hq e
    (T + q * e.natAbs + 1)
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  set N : ℕ := 2 ^ k - 1 with hN
  have hNk : k ≤ N := by omega
  have hNT : T ≤ N := by omega
  have hNq : q * e.natAbs ≤ N := by omega
  have hN1 : 2 ^ k = N + 1 := by omega
  set A : ℕ := p * N / q with hA
  have hq0 : 0 < q := by omega
  have hAq : A * q ≤ p * N := Nat.div_mul_le_self _ _
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have he2 : e ≤ (e.natAbs : ℤ) := by rw [habs]; exact le_abs_self e
  -- `e.natAbs ≤ A`
  have hlow : e.natAbs ≤ A := by
    rw [hA, Nat.le_div_iff_mul_le hq0]
    have : e.natAbs * q ≤ N := by rw [Nat.mul_comm]; exact hNq
    nlinarith
  -- `e + A ≤ N`
  have hup : (e + (A : ℤ)) ≤ N := by
    have h1 : (A : ℤ) * q ≤ p * N := by exact_mod_cast hAq
    have h2 : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
    have h3 : ((q : ℤ)) * e.natAbs ≤ N := by exact_mod_cast hNq
    have hN0 : (0 : ℤ) ≤ N := by positivity
    have h4 : (q : ℤ) * (e.natAbs : ℤ) ≤ q * (N - A) := by nlinarith
    have h5 : (e.natAbs : ℤ) ≤ N - A := le_of_mul_le_mul_left h4 (by exact_mod_cast hq0)
    linarith
  have hx0 : 0 ≤ e + (A : ℤ) := by
    have : (e.natAbs : ℤ) ≤ A := by exact_mod_cast hlow
    linarith
  refine ⟨N, hNT, ?_⟩
  have hnat : (e + (A : ℤ)).natAbs < 2 ^ k := by
    have := Int.natAbs_eq (e + (A : ℤ))
    omega
  have hrow := f150_single_two_pow_sub_one k (e + (A : ℤ)) hnat
  unfold observedRationalRay
  rw [← hA, hrow]
  have hk3' : (2 ^ k - (e + (A : ℤ)).natAbs) % 3 ≠ 0 := by
    have hz : ((2 : ℤ) ^ k - (e + (((p * (2 ^ k - 1) / q : ℕ)) : ℤ))) % 3 ≠ 0 := hk3
    rw [← hN, ← hA] at hz
    have hc : (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) := by push_cast; rfl
    rw [hc] at hz
    have := Int.natAbs_eq (e + (A : ℤ))
    omega
  simp only [hk3', ↓reduceIte]

/-! ## The statement off the powers of two -/

/-- **A ray of rule `150` from the single seed, at a coprime speed `p / q` with `0 < p < q` whose
denominator is not a power of two, from any cell, is not eventually periodic** ([RuleSpace] §5
Proposition 5.1 at rule `150`): a one past every step on the ray and zero runs of every length
past every step together rule out a period. This reaches speeds from one third to one half, which
the ranges below one third and above one half leave out. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two (p q : ℕ)
    (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q) (hq : ∀ r : ℕ, q ≠ 2 ^ r) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_of_late_one_of_late_zero_runs _
    (exists_late_one_observedRationalRay_f150_single_of_not_pow_two p q hp hpq hcop hq e)
    (lateZeroRuns_f150 p q hp hpq e)

/-- **Joint satisfiability** of the hypotheses of the statement off the powers of two: the ray at
speed `2 / 5`, between one third and one half, from cell zero is not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two_nonvacuous :
    0 < 2 ∧ 2 < 5 ∧ Nat.Coprime 2 5 ∧ (∀ r : ℕ, 5 ≠ 2 ^ r) ∧
      ¬ DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 2 5 0) := by
  have hq : ∀ r : ℕ, 5 ≠ 2 ^ r := by
    intro r hr
    have hr5 : r < 5 := by
      have : r < 2 ^ r := Nat.lt_two_pow_self
      omega
    interval_cases r <;> simp at hr
  exact ⟨by decide, by decide, by decide, hq,
    not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two 2 5 (by decide)
      (by decide) (by decide) hq 0⟩

/-- **A ray of rule `150` from the single seed, at a coprime speed `p / q` with `0 < p < q`, from
any cell, is not eventually periodic when `q` is not a power of two, or `3 * p < q`, or
`q < 2 * p`** ([RuleSpace] §5 Proposition 5.1, Proposition 5.33 and Proposition 5.35 at rule
`150`): the three ranges of speeds in one statement. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_of_coprime (p q : ℕ) (hp : 0 < p)
    (hpq : p < q) (hcop : Nat.Coprime p q)
    (h : (∀ r : ℕ, q ≠ 2 ^ r) ∨ 3 * p < q ∨ q < 2 * p) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) := by
  rcases h with h | h | h
  · exact not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two p q hp hpq hcop h e
  · exact not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt p q hp h e
  · exact not_eventuallyPeriodic_observedRationalRay_f150_single p q hpq h e

/-- **Guard: the denominator hypothesis of the remainder lemma is needed.** At the dyadic speed
`7 / 16` from cell `1` the quantity `2 ^ k - (1 + 7 * (2 ^ k - 1) / 16)` equals `9 * 2 ^ (k - 4)`,
so `3` divides it at every index from `4` on. -/
theorem exists_two_pow_sub_ray_mod_three_ne_guard :
    ∀ k : ℕ, 4 ≤ k → ((2 : ℤ) ^ k - (1 + ((7 * (2 ^ k - 1) / 16 : ℕ) : ℤ))) % 3 = 0 := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  have hb : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h16 : (2 : ℤ) ^ (j + 4) = 16 * ((2 ^ j : ℕ) : ℤ) := by push_cast; ring
  have hn : (2 : ℕ) ^ (j + 4) = 16 * 2 ^ j := by ring
  rw [h16, hn]
  generalize 2 ^ j = b at *
  omega


/-! ## Piece 11: the row at step `3 * 2 ^ m - 1` -/

/-- **The row of rule `150` from the single seed at step `3 * 2 ^ m - 1`, read modulo three**
([RuleSpace] §5): at a cell `x` with `|x - 2 ^ (m + 1)| < 2 ^ m` the row reads `0` exactly when
`3` divides `2 ^ m - |x - 2 ^ (m + 1)|`. The step is `2 ^ (m + 1)` plus `2 ^ m - 1`, so the
two-power identity reads the cells `x - 2 ^ (m + 1)`, `x` and `x + 2 ^ (m + 1)` of step
`2 ^ m - 1`, the last two outside its light cone. -/
theorem f150_single_three_mul_two_pow_sub_one (m : ℕ) (x : ℤ)
    (hx : (x - 2 ^ (m + 1)).natAbs < 2 ^ m) :
    ((finRule f150 hq150)^[3 * 2 ^ m - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x =
      if (2 ^ m - (x - 2 ^ (m + 1)).natAbs) % 3 = 0 then 0 else 1 := by
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hsplit : 3 * 2 ^ m - 1 = 2 ^ (m + 1) + (2 ^ m - 1) := by rw [pow_succ]; omega
  have hxn : ((x - 2 ^ (m + 1)).natAbs : ℤ) < 2 ^ m := by exact_mod_cast hx
  have habs := Int.natAbs_eq (x - 2 ^ (m + 1))
  have hc : ((2 ^ m - 1 : ℕ) : ℤ) = 2 ^ m - 1 := by
    push_cast [Nat.cast_sub hpos]; ring
  have h2 : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
  rw [hsplit, f150_iterate_two_pow_add]
  have z2 := f150_single_apply_eq_zero_of_lt (2 ^ m - 1) x
    (by rw [hc, lt_abs]; left; omega)
  have z3 := f150_single_apply_eq_zero_of_lt (2 ^ m - 1) (x + 2 ^ (m + 1))
    (by rw [hc, lt_abs]; left; omega)
  rw [z2, z3, f150_single_two_pow_sub_one m (x - 2 ^ (m + 1)) hx]
  simp

/-! ## Piece 12: a one past every step at the dyadic speeds from one third to one half -/

/-- `3` does not divide a power of two -/
private theorem three_not_dvd_two_pow (n : ℕ) : ¬ 3 ∣ 2 ^ n := by
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

/-- the division of `p * (c * (q * Q) - 1)` by `q` -/
private theorem ray_div_mul_pred (p q Q c : ℕ) (hp : 0 < p) (hpq : p ≤ q) (hQ : 0 < Q)
    (hc : 0 < c) : p * (c * (q * Q) - 1) / q = c * (p * Q) - 1 := by
  have hq : 0 < q := by omega
  have hpos1 : 0 < c * (p * Q) := by positivity
  have hpos2 : 0 < c * (q * Q) := by positivity
  obtain ⟨u, hu⟩ : ∃ u, c * (p * Q) = u + 1 := ⟨c * (p * Q) - 1, by omega⟩
  obtain ⟨w, hw⟩ : ∃ w, c * (q * Q) = w + 1 := ⟨c * (q * Q) - 1, by omega⟩
  have hrel : p * (w + 1) = q * (u + 1) := by
    rw [← hw, ← hu]; ring
  have h1 : p * w + p = q * u + q := by nlinarith [hrel]
  rw [hw, hu]
  simp only [Nat.add_sub_cancel]
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm u q]; omega
  · have : (u + 1) * q = q * u + q := by ring
    omega

/-- **A one past every step on every ray of rule `150` from the single seed at a dyadic speed
`p / 2 ^ r` from one third to one half** ([RuleSpace] §5 Proposition 5.1(i) at rule `150`): with
`p` odd and `2 * p ≤ 2 ^ r < 3 * p`, the ray's cell at the step `2 ^ k - 1` is
`e + p * 2 ^ (k - r) - 1` and the row there reads `1` exactly when `3` does not divide
`(2 ^ r - p) * 2 ^ (k - r) - e + 1`, which fails for a large `k` of one parity or of any parity
unless `3` divides both `2 ^ r - p` and `e - 1`; in that case the step `3 * 2 ^ m - 1` is used,
where the row reads `1` because `3` divides neither `p` nor a power of two. -/
theorem exists_late_one_observedRationalRay_f150_single_of_dyadic (p r : ℕ) (hp : p % 2 = 1)
    (h1 : 2 ^ r < 3 * p) (h2 : 2 * p ≤ 2 ^ r) (e : ℤ) :
    ∀ T : ℕ, ∃ t, T ≤ t ∧
      observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p (2 ^ r) e t
        = 1 := by
  intro T
  have hp0 : 0 < p := by omega
  have h3q : ¬ 3 ∣ 2 ^ r := three_not_dvd_two_pow r
  have hpowz : ∀ n : ℕ, ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := fun n => by simp
  generalize hq : 2 ^ r = q at h1 h2 h3q ⊢
  have hq0 : 0 < q := by omega
  obtain ⟨d, hd⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
  have hdp : p ≤ d := by omega
  have hd0 : 0 < d := by omega
  have habsE := Int.natAbs_eq e
  by_cases hc : (3 : ℤ) ∣ (d : ℤ) ∧ (3 : ℤ) ∣ (e - 1)
  · -- the step `3 * 2 ^ m - 1`
    obtain ⟨⟨d', hd'⟩, ⟨e', he'⟩⟩ := hc
    have hd'n : d = 3 * d'.toNat := by omega
    set j : ℕ := T + e.natAbs + 3 with hj
    have hQlt : j < 2 ^ j := Nat.lt_two_pow_self
    generalize hQ : 2 ^ j = Q at hQlt
    have hQpos : 0 < Q := by omega
    have hpow : 2 ^ (r + j) = q * Q := by rw [pow_add, hq, hQ]
    have hpQ : Q ≤ p * Q := Nat.le_mul_of_pos_left Q hp0
    have hqQ : q * Q = p * Q + d * Q := by rw [hd]; ring
    have hb1 : q * Q + Q ≤ 3 * (p * Q) := by
      have := Nat.mul_le_mul_right Q (show q + 1 ≤ 3 * p by omega)
      nlinarith [this]
    have hb2 : 3 * (p * Q) + Q ≤ 2 * (q * Q) := by
      have := Nat.mul_le_mul_right Q (show 3 * p + 1 ≤ 2 * q by omega)
      nlinarith [this]
    have hD3 : d * Q = 3 * (d'.toNat * Q) := by rw [hd'n]; ring
    have hP3 : ¬ 3 ∣ p * Q := by
      intro hdv
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hdv with h | h
      · apply h3q
        rw [hd, hd'n]
        exact Nat.dvd_add h (Dvd.intro _ rfl)
      · rw [← hQ] at h
        exact three_not_dvd_two_pow j h
    have hdiv : p * (3 * (q * Q) - 1) / q = 3 * (p * Q) - 1 :=
      ray_div_mul_pred p q Q 3 hp0 (by omega) hQpos (by norm_num)
    generalize hPd : p * Q = P at *
    generalize hDd : d * Q = D at *
    generalize hRd : q * Q = R at *
    refine ⟨3 * R - 1, ?_, ?_⟩
    · omega
    unfold observedRationalRay
    rw [hdiv]
    have hz : (2 : ℤ) ^ (r + j + 1) = 2 * R := by
      rw [pow_succ, ← hpowz, hpow]; ring
    have hx : (e + ((3 * P - 1 : ℕ) : ℤ) - 2 ^ (r + j + 1)).natAbs < 2 ^ (r + j) := by
      rw [hz]
      have := Int.natAbs_eq (e + ((3 * P - 1 : ℕ) : ℤ) - 2 * R)
      rw [hpow]
      omega
    rw [← hpow, f150_single_three_mul_two_pow_sub_one (r + j) _ hx]
    rw [hz, hpow]
    have := Int.natAbs_eq (e + ((3 * P - 1 : ℕ) : ℤ) - 2 * R)
    split_ifs with hh <;> first | rfl | (exfalso; omega)
  · -- the step `2 ^ k - 1`
    have hex : ∃ j : ℕ, T + e.natAbs + 3 ≤ j ∧
        ¬ (3 : ℤ) ∣ (d : ℤ) * 2 ^ j - e + 1 := by
      by_contra hcon
      push Not at hcon
      have a1 := hcon (T + e.natAbs + 3) le_rfl
      have a2 := hcon (T + e.natAbs + 3 + 1) (by omega)
      rw [pow_succ] at a2
      obtain ⟨Xn, hXn⟩ : ∃ Xn : ℕ, Xn = 2 ^ (T + e.natAbs + 3) := ⟨_, rfl⟩
      have hXz : (2 : ℤ) ^ (T + e.natAbs + 3) = (Xn : ℤ) := by
        rw [hXn]; exact (hpowz _).symm
      have h3 : ¬ 3 ∣ Xn := by rw [hXn]; exact three_not_dvd_two_pow _
      rw [hXz] at a1 a2
      have h4 : (3 : ℤ) ∣ (d : ℤ) * (Xn : ℤ) := by
        have : (d : ℤ) * ((Xn : ℤ) * 2) = 2 * ((d : ℤ) * (Xn : ℤ)) := by ring
        omega
      have h4n : 3 ∣ d * Xn := by exact_mod_cast h4
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h4n with h | h
      · exact hc ⟨by exact_mod_cast h, by omega⟩
      · exact h3 h
    obtain ⟨j, hjJ, hj⟩ := hex
    have hQlt : j < 2 ^ j := Nat.lt_two_pow_self
    have hQz : (((2 ^ j : ℕ)) : ℤ) = (2 : ℤ) ^ j := hpowz j
    have hj' : ¬ (3 : ℤ) ∣ (d : ℤ) * ((2 ^ j : ℕ) : ℤ) - e + 1 := by rw [hQz]; exact hj
    generalize hQ : 2 ^ j = Q at hQlt hj'
    have hQpos : 0 < Q := by omega
    have hpow : 2 ^ (r + j) = q * Q := by rw [pow_add, hq, hQ]
    have hpQ : Q ≤ p * Q := Nat.le_mul_of_pos_left Q hp0
    have hdQ : Q ≤ d * Q := Nat.le_mul_of_pos_left Q hd0
    have hqQ : q * Q = p * Q + d * Q := by rw [hd]; ring
    have hdiv : p * (1 * (q * Q) - 1) / q = 1 * (p * Q) - 1 :=
      ray_div_mul_pred p q Q 1 hp0 (by omega) hQpos one_pos
    rw [one_mul, one_mul] at hdiv
    generalize hPd : p * Q = P at *
    generalize hDd : d * Q = D at *
    generalize hRd : q * Q = R at *
    obtain ⟨xn, hxn⟩ : ∃ xn : ℕ, (xn : ℤ) = e + ((P - 1 : ℕ) : ℤ) :=
      ⟨(e + ((P - 1 : ℕ) : ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨R - 1, by omega, ?_⟩
    unfold observedRationalRay
    rw [hdiv, ← hxn, ← hpow]
    have hxlt : ((xn : ℤ)).natAbs < 2 ^ (r + j) := by
      rw [Int.natAbs_natCast, hpow]; omega
    rw [f150_single_two_pow_sub_one (r + j) _ hxlt]
    rw [Int.natAbs_natCast, hpow]
    split_ifs with hh <;> first | rfl | (exfalso; omega)

/-! ## Piece 13: every speed strictly between rest and one -/

/-- **A ray of rule `150` from the single seed, at every speed `p / q` strictly between rest and
one, from any cell, is not eventually periodic** ([RuleSpace] §5 Proposition 5.1, Proposition 5.33
and Proposition 5.35 and Proposition 5.36 at rule `150`): the ray at `p / q` is the ray at the
reduced fraction; a reduced denominator that is not a power of two is Proposition 5.36, and a
power of two `2 ^ r` has `p` odd, `3 * p ≠ 2 ^ r`, and either `3 * p < 2 ^ r`, or
`2 ^ r < 2 * p`, or `2 * p ≤ 2 ^ r < 3 * p`, the last by the one past every step at the dyadic
speeds and the zero runs of every length. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt (p q : ℕ) (hp : 0 < p)
    (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) := by
  have hg : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp
  obtain ⟨p', q', hcop, hpe, hqe⟩ := Nat.exists_coprime p q
  generalize Nat.gcd p q = g at hg hpe hqe
  have hray : observedRationalRay (finRule f150 hq150)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e =
      observedRationalRay (finRule f150 hq150)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p' q' e := by
    funext t
    unfold observedRationalRay
    have : p * t / q = p' * t / q' := by
      rw [show p * t = p' * t * g by rw [hpe]; ring, hqe, Nat.mul_div_mul_right _ _ hg]
    rw [this]
  rw [hray]
  have hp' : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with h | h
    · rw [h] at hpe; omega
    · exact h
  have hpq' : p' < q' := by
    have : p' * g < q' * g := by rw [← hpe, ← hqe]; exact hpq
    exact Nat.lt_of_mul_lt_mul_right this
  clear hray hpe hqe hpq hp
  by_cases hq : ∀ r : ℕ, q' ≠ 2 ^ r
  · exact not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two p' q' hp' hpq'
      hcop hq e
  · push Not at hq
    obtain ⟨r, rfl⟩ := hq
    have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · rw [h] at hpq'; simp at hpq'; omega
      · exact h
    have hodd : p' % 2 = 1 := by
      by_contra hne
      have h2p : 2 ∣ p' := by omega
      have h2q : 2 ∣ 2 ^ r := dvd_pow_self 2 (by omega)
      have := Nat.dvd_gcd h2p h2q
      rw [hcop] at this
      omega
    have h3 := three_not_dvd_two_pow r
    by_cases hlow : 3 * p' < 2 ^ r
    · exact not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt p' _ hp'
        hlow e
    by_cases hhigh : 2 ^ r < 2 * p'
    · exact not_eventuallyPeriodic_observedRationalRay_f150_single p' _ hpq' hhigh e
    have h3p : 2 ^ r < 3 * p' := by
      have : 2 ^ r ≠ 3 * p' := fun h => h3 ⟨p', h⟩
      omega
    exact not_eventuallyPeriodic_of_late_one_of_late_zero_runs _
      (exists_late_one_observedRationalRay_f150_single_of_dyadic p' r hodd h3p (by omega) e)
      (lateZeroRuns_f150 p' _ hp' hpq' e)

/-- **Joint satisfiability** of the hypotheses of the statement at every speed: the ray at speed
`7 / 16` from cell `1`, a dyadic speed between one third and one half at which the rows `2 ^ k - 1`
all miss, is not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt_nonvacuous :
    0 < 7 ∧ 7 < 16 ∧
      ¬ DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule f150 hq150) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 7 16 1) :=
  ⟨by decide, by decide,
    not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt 7 16 (by decide) (by decide) 1⟩

end ECA

/-- info:
'ECA.hq150' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.hq150

/-- info:
'ECA.iterate_two_pow_f150' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.iterate_two_pow_f150

/-- info:
'ECA.f150_single_apply_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f150_single_apply_zero

/-- info:
'ECA.f150_single_apply_two_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f150_single_apply_two_pow

/-- info:
'ECA.exists_late_one_observedRationalRay_f150_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_late_one_observedRationalRay_f150_single

/-- info:
'ECA.lateZeroRuns_f150' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.lateZeroRuns_f150

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_nonvacuous

/-- info:
'ECA.observedRationalRay_f150_single_guard_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f150_single_guard_zero

/-- info:
'ECA.observedRationalRay_f150_single_guard_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f150_single_guard_one

/-- info:
'ECA.card_ones_observedRationalRay_f150_single_half_guard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_ones_observedRationalRay_f150_single_half_guard

/-- info:
'ECA.exists_late_one_observedRationalRay_f150_single_of_three_mul_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_late_one_observedRationalRay_f150_single_of_three_mul_lt

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt_or_lt_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_three_mul_lt_or_lt_two_mul

set_option linter.style.longLine false in
/-- info: 'ECA.f150_single_two_pow_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f150_single_two_pow_sub_one

set_option linter.style.longLine false in
/-- info: 'ECA.exists_two_pow_sub_ray_mod_three_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_two_pow_sub_ray_mod_three_ne

set_option linter.style.longLine false in
/-- info: 'ECA.exists_late_one_observedRationalRay_f150_single_of_not_pow_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_late_one_observedRationalRay_f150_single_of_not_pow_two

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_not_pow_two_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_coprime

set_option linter.style.longLine false in
/-- info: 'ECA.exists_two_pow_sub_ray_mod_three_ne_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_two_pow_sub_ray_mod_three_ne_guard

set_option linter.style.longLine false in
/-- info: 'ECA.f150_single_three_mul_two_pow_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f150_single_three_mul_two_pow_sub_one

set_option linter.style.longLine false in
/-- info: 'ECA.exists_late_one_observedRationalRay_f150_single_of_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_late_one_observedRationalRay_f150_single_of_dyadic

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f150_single_of_lt_nonvacuous
