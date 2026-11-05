module

public import ECA.RationalRayLines
public import ECA.Doubling

/-!
# Rays of rule `126` from the single seed
([RuleSpace] §5, transferring Proposition 5.1)

[RuleSpace] §5 Proposition 5.1 makes every ray of rule `90` from the single seed at a speed
strictly between rest and one not eventually periodic, by a one past every step and zero runs of
every length past every step. This file transfers it to rule `126`, whose even rows from the
single seed are those of rule `90` doubled toward the center ([RuleSpace] §5 Proposition 5.8): the
cell `y` of rule `126` at step `2 * t` reads the cell `⌈y / 2⌉` of rule `90` at step `t` for
`y ≥ 0` and `⌊y / 2⌋` for `y < 0`. The ones come from the lines of rule `90` ([RuleSpace] §5
Proposition 5.6), whose offset `⌊q' * (e + 1) / 2⌋` carries the halving of the index, and the
zero runs from the splitting of rule `90` at a power of two, so the rays of rule `126` at
every speed strictly between rest and one are not eventually periodic. The center column is a second
instance: it reads a one at the steps `2 ^ j - 1` and zero runs past every step, so it is not
eventually periodic, where rule `90`'s own center column is.

## Main results

* `f126_single_two_mul` — the cell `y` of rule `126` at step `2 * t` is the cell
  `⌈y / 2⌉` (`y ≥ 0`) or `⌊y / 2⌋` (`y < 0`) of rule `90` at step `t`.
* `exists_late_one_observedRationalRay_f126_single` — a ray of speed `p / q` with `0 < p < q`
  reads a one past every step.
* `lateZeroRuns_f126` — a ray of speed `p / q` with `p < q`, the speed zero included, reads zero
  runs of every length past every step.
* `not_eventuallyPeriodic_observedRationalRay_f126_single` — **a ray of rule `126` from the
  single seed at a speed `p / q` with `0 < p < q` is not eventually periodic**, from every
  cell; `not_eventuallyPeriodic_observedRationalRay_f126_single_nonvacuous` meets the speed
  hypotheses at speed `1 / 2`.
* `f126_single_apply_zero_two_pow_sub_one` — the center column reads `1` at the steps `2 ^ j - 1`;
  `not_eventuallyPeriodic_observedRationalRay_f126_single_zero` — **the center column is not
  eventually periodic**, a contrast with rule `90`, whose speed-zero ray from cell `0` is
  eventually periodic.
* `observedRationalRay_f126_single_guard_one` — **guard**: at speed one from cell `0` the ray
  reads `1` at every step, so it is eventually periodic.
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## Piece 1: the closed form at even steps -/

/-- the single seed of rule `90` is symmetric under `i ↦ -i` at every step -/
private theorem finRule_f90_single_apply_neg (t : ℕ) (i : ℤ) :
    ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-i)
      = ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i := by
  induction t generalizing i with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Finsupp.single_apply]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  | succ t ih =>
      rw [Function.iterate_succ_apply', finRule_apply, finRule_apply, f90, f90,
        show -i - 1 = -(i + 1) by ring, show -i + 1 = -(i - 1) by ring, ih (i + 1), ih (i - 1)]
      ring

/-- the index of rule `90` read by the cell `y` of rule `126` at an even step -/
private def halfIndex (y : ℤ) : ℤ := if 0 ≤ y then (y + 1) / 2 else y / 2

/-- two steps of rule `126` on a state doubled with the second pair shifted: pattern one -/
private theorem f126_two_steps_one (a b c : ZMod 2) :
    f126 (f126 a b b) (f126 b b c) (f126 b c c) = a + c := by
  revert a b c; decide

/-- two steps of rule `126` on a doubled state: pattern two -/
private theorem f126_two_steps_two (a b c : ZMod 2) :
    f126 (f126 a a b) (f126 a b b) (f126 b b c) = a + c := by
  revert a b c; decide

/-- the five-cell identity behind the closed form -/
private theorem two_steps_halfIndex (v : ℤ → ZMod 2) (hs : ∀ k, v (-k) = v k)
    (hp : v 1 = 0 ∨ (v 0 = 0 ∧ v 2 = 0)) (y : ℤ) :
    f126 (f126 (v (halfIndex (y - 2))) (v (halfIndex (y - 1))) (v (halfIndex y)))
        (f126 (v (halfIndex (y - 1))) (v (halfIndex y)) (v (halfIndex (y + 1))))
        (f126 (v (halfIndex y)) (v (halfIndex (y + 1))) (v (halfIndex (y + 2))))
      = v (halfIndex y - 1) + v (halfIndex y + 1) := by
  by_cases h2 : 2 ≤ y
  · obtain ⟨m, hm | hm⟩ := Int.even_or_odd' y
    · have e1 : halfIndex (y - 2) = m - 1 := by unfold halfIndex; split_ifs <;> omega
      have e2 : halfIndex (y - 1) = m := by unfold halfIndex; split_ifs <;> omega
      have e3 : halfIndex y = m := by unfold halfIndex; split_ifs <;> omega
      have e4 : halfIndex (y + 1) = m + 1 := by unfold halfIndex; split_ifs <;> omega
      have e5 : halfIndex (y + 2) = m + 1 := by unfold halfIndex; split_ifs <;> omega
      rw [e1, e2, e3, e4, e5]
      exact f126_two_steps_one _ _ _
    · have e1 : halfIndex (y - 2) = m := by unfold halfIndex; split_ifs <;> omega
      have e2 : halfIndex (y - 1) = m := by unfold halfIndex; split_ifs <;> omega
      have e3 : halfIndex y = m + 1 := by unfold halfIndex; split_ifs <;> omega
      have e4 : halfIndex (y + 1) = m + 1 := by unfold halfIndex; split_ifs <;> omega
      have e5 : halfIndex (y + 2) = m + 2 := by unfold halfIndex; split_ifs <;> omega
      rw [e1, e2, e3, e4, e5, show m + 1 - 1 = m by ring, show m + 1 + 1 = m + 2 by ring]
      exact f126_two_steps_two _ _ _
  · by_cases h3 : y ≤ -2
    · obtain ⟨m, hm | hm⟩ := Int.even_or_odd' y
      · have e1 : halfIndex (y - 2) = m - 1 := by unfold halfIndex; split_ifs <;> omega
        have e2 : halfIndex (y - 1) = m - 1 := by unfold halfIndex; split_ifs <;> omega
        have e3 : halfIndex y = m := by unfold halfIndex; split_ifs <;> omega
        have e4 : halfIndex (y + 1) = m := by unfold halfIndex; split_ifs <;> omega
        have e5 : halfIndex (y + 2) = m + 1 := by unfold halfIndex; split_ifs <;> omega
        rw [e1, e2, e3, e4, e5]
        exact f126_two_steps_two _ _ _
      · have e1 : halfIndex (y - 2) = m - 1 := by unfold halfIndex; split_ifs <;> omega
        have e2 : halfIndex (y - 1) = m := by unfold halfIndex; split_ifs <;> omega
        have e3 : halfIndex y = m := by unfold halfIndex; split_ifs <;> omega
        have e4 : halfIndex (y + 1) = m + 1 := by unfold halfIndex; split_ifs <;> omega
        have e5 : halfIndex (y + 2) = m + 1 := by unfold halfIndex; split_ifs <;> omega
        rw [e1, e2, e3, e4, e5]
        exact f126_two_steps_one _ _ _
    · have s1 := hs 1
      have s2 := hs 2
      have hy : y = -1 ∨ y = 0 ∨ y = 1 := by omega
      rcases hy with rfl | rfl | rfl
      · simp only [halfIndex]
        norm_num
        simp only [s1, s2]
        revert hp
        generalize v 0 = a
        generalize v 1 = b
        generalize v 2 = c
        revert a b c
        decide
      · simp only [halfIndex]
        norm_num
        simp only [s1]
        revert hp
        generalize v 0 = a
        generalize v 1 = b
        generalize v 2 = c
        revert a b c
        decide
      · simp only [halfIndex]
        norm_num
        simp only [s1]
        revert hp
        generalize v 0 = a
        generalize v 1 = b
        generalize v 2 = c
        revert a b c
        decide

/-- the closed form at even steps, with the index named -/
private theorem two_mul_halfIndex (t : ℕ) (y : ℤ) :
    ((finRule f126 hq126)^[2 * t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) y =
      ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (halfIndex y) := by
  induction t generalizing y with
  | zero =>
    simp only [halfIndex, mul_zero, Function.iterate_zero, id_eq, Finsupp.single_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  | succ t ih =>
    have hs : ∀ k, ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-k) =
        ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) k :=
      fun k => finRule_f90_single_apply_neg t k
    have hp : ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 0 ∨
        (((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 0 ∧
        ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 2 = 0) := by
      rcases Nat.even_or_odd t with ⟨a, ha⟩ | ⟨a, ha⟩
      · left
        apply f90_single_apply_eq_zero_of_odd
        omega
      · right
        constructor <;> apply f90_single_apply_eq_zero_of_odd <;> omega
    have key := two_steps_halfIndex
      (fun k => ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) k) hs hp y
    have ih' : ∀ z, ((finRule f126 hq126)^[2 * t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) z =
        ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (halfIndex z) :=
      fun z => ih z
    have e : 2 * (t + 1) = 2 * t + 1 + 1 := by ring
    rw [e, Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply' (finRule f90 hq90) t]
    simp only [finRule_apply, ih', sub_add_cancel, add_sub_cancel_right,
      show y - 1 - 1 = y - 2 by ring, show y + 1 + 1 = y + 2 by ring]
    rw [key, f90]

/-- **Rule `126` at even steps from the single seed, in terms of rule `90`**
([RuleSpace] §5 Proposition 5.8): the cell `y` of rule `126` at step `2 * t` reads the cell
`⌈y / 2⌉` of rule `90` at step `t` for `y ≥ 0` and `⌊y / 2⌋` for `y < 0`. -/
theorem f126_single_two_mul (t : ℕ) (y : ℤ) :
    ((finRule f126 hq126)^[2 * t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) y =
      ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (if 0 ≤ y then (y + 1) / 2 else y / 2) :=
  two_mul_halfIndex t y

/-! ## Piece 2: a one past every step -/

/-- the cell index of the closed form against the floor of a line, the arithmetic core -/
private theorem half_index_ray (q : ℤ) (hq : 0 < q) (P D r e : ℤ) (hPD : 2 * P = q * D + r)
    (hr0 : 0 ≤ r) (hrq : r < q) :
    (e + D + 1) / 2 = (P + q * (e + 1) / 2) / q := by
  set E := e + 1 with hE
  have hED : e + D + 1 = E + D := by rw [hE]; ring
  rw [hED]
  have hqW : q * (E + D) = q * E + q * D := by ring
  have hm1 : (q * E) % 2 = ((q % 2) * (E % 2)) % 2 := Int.mul_emod _ _ _
  have hm2 : (q * D) % 2 = ((q % 2) * (D % 2)) % 2 := Int.mul_emod _ _ _
  have hpar : ¬ (r = 0 ∧ (q * E) % 2 = 1 ∧ (E + D) % 2 = 0) := by
    rintro ⟨hr, h1, h2⟩
    rcases Int.emod_two_eq_zero_or_one q with a | a <;>
    rcases Int.emod_two_eq_zero_or_one E with b | b <;>
    rcases Int.emod_two_eq_zero_or_one D with c | c <;>
    simp [a, b, c] at hm1 hm2 <;> omega
  have hqY : q * (E + D) = 2 * (q * ((E + D) / 2)) + q * ((E + D) % 2) := by
    have : E + D = 2 * ((E + D) / 2) + (E + D) % 2 := by omega
    calc q * (E + D) = q * (2 * ((E + D) / 2) + (E + D) % 2) := by rw [← this]
      _ = _ := by ring
  have hk : (E + D) % 2 = 0 ∨ (E + D) % 2 = 1 := by omega
  have hmul : ((E + D) / 2 + 1) * q = q * ((E + D) / 2) + q := by ring
  have hmul' : (E + D) / 2 * q = q * ((E + D) / 2) := by ring
  have hmul : ((E + D) / 2 + 1) * q = q * ((E + D) / 2) + q := by ring
  have hmul' : (E + D) / 2 * q = q * ((E + D) / 2) := by ring
  have hqY' : q * (E + D) = 2 * (q * ((E + D) / 2)) ∧ (E + D) % 2 = 0 ∨
      q * (E + D) = 2 * (q * ((E + D) / 2)) + q ∧ (E + D) % 2 = 1 := by
    rcases hk with k | k
    · left; rw [k] at hqY; simp only [mul_zero, add_zero] at hqY; exact ⟨hqY, k⟩
    · right; rw [k] at hqY; simp only [mul_one] at hqY; exact ⟨hqY, k⟩
  clear hqY hm1 hm2
  symm
  apply le_antisymm
  · have : (P + q * E / 2) / q < (E + D) / 2 + 1 := by
      rw [Int.ediv_lt_iff_lt_mul hq, hmul]
      omega
    omega
  · rw [Int.le_ediv_iff_mul_le hq, hmul']
    omega

/-- **A one past every step on every ray of rule `126` from the single seed at a speed strictly
between rest and one** ([RuleSpace] §5 Proposition 5.1(i) at rule `126`): the speed is reduced to
lowest terms, the line `(p' * s + c) / q'` with `c = ⌊q' * (e + 1) / 2⌋` is not a zero line of
rule `90` ([RuleSpace] §5 Proposition 5.6), so rule `90` reads a one on it past every step, and
the even step `2 * s` of rule `126` reads that cell of rule `90` by `f126_single_two_mul`. -/
theorem exists_late_one_observedRationalRay_f126_single (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (e : ℤ) :
    ∀ T : ℕ, ∃ t, T ≤ t ∧
      observedRationalRay (finRule f126 hq126) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1 := by
  intro T
  have hg : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left _ hp
  have hcop0 := Nat.coprime_div_gcd_div_gcd hg
  obtain ⟨p', hp'⟩ := Nat.gcd_dvd_left p q
  obtain ⟨q', hq'⟩ := Nat.gcd_dvd_right p q
  generalize hgdef : Nat.gcd p q = g at *
  have e1 : p / g = p' := Nat.div_eq_of_eq_mul_right hg hp'
  have e2 : q / g = q' := Nat.div_eq_of_eq_mul_right hg hq'
  rw [e1, e2] at hcop0
  have hp'pos : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with h | h
    · rw [h] at hp'; omega
    · exact h
  have hp'q' : p' < q' := by
    rw [hp', hq'] at hpq
    exact Nat.lt_of_mul_lt_mul_left hpq
  have hrel : ∀ x : ℕ, p * x / q = p' * x / q' := by
    intro x
    rw [hp', hq', mul_assoc, Nat.mul_div_mul_left _ _ hg]
  have hq'pos : 0 < q' := by omega
  set c : ℤ := ((q' : ℤ) * (e + 1)) / 2 with hc
  have hnz : ¬ ZeroLine p' q' c := by
    rintro ⟨-, hc1, m, hm, hqm⟩
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hq3 : 3 ≤ q' := by omega
    have hq3z : (3 : ℤ) ≤ q' := by exact_mod_cast hq3
    have hw : -2 ≤ (q' : ℤ) * (e + 1) ∧ (q' : ℤ) * (e + 1) ≤ -1 := by omega
    rcases le_or_gt 0 (e + 1) with h | h
    · nlinarith [hw.2]
    · nlinarith [hw.1]
  obtain ⟨s, hs, hone⟩ :=
    (exists_late_one_f90_single_onLine_iff p' q' hp'pos hp'q' hcop0 c).mpr hnz
      (T + q' * (e.natAbs + 1))
  refine ⟨2 * s, by omega, ?_⟩
  unfold observedRationalRay
  rw [hrel (2 * s)]
  set D : ℕ := p' * (2 * s) / q' with hD
  set r : ℕ := p' * (2 * s) % q' with hr
  have hDr : q' * D + r = p' * (2 * s) := Nat.div_add_mod _ _
  have hrq : r < q' := Nat.mod_lt _ hq'pos
  have hDbig : 2 * e.natAbs + 1 < D := by
    have h1 : 2 * s ≤ p' * (2 * s) := Nat.le_mul_of_pos_left _ hp'pos
    have h2 : q' * (2 * e.natAbs + 2) < q' * (D + 1) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have hy : 0 ≤ e + (D : ℤ) := by
    have : (2 * e.natAbs + 1 : ℤ) < D := by exact_mod_cast hDbig
    omega
  rw [two_mul_halfIndex]
  unfold halfIndex
  simp only [hy, ↓reduceIte]
  have hdz : (q' : ℤ) * D + r = p' * (2 * s) := by exact_mod_cast hDr
  have key := half_index_ray (q' : ℤ) (by exact_mod_cast hq'pos) ((p' : ℤ) * s) D r e
    (by linarith) (by positivity) (by exact_mod_cast hrq)
  rw [key]
  exact hone

/-! ## Piece 3: zero runs from rest to one -/

/-- outside the light cone the single seed's orbit under rule `126` is zero -/
private theorem f126_single_apply_eq_zero_of_lt (t : ℕ) (i : ℤ) (h : (t : ℤ) < |i|) :
    ((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i = 0 := by
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
      exact hq126

/-- rule `90` at step `2 ^ B + r` is zero at a cell outside both translated light cones -/
private theorem f90_single_two_pow_add_eq_zero (B r : ℕ) (x : ℤ) (h1 : (r : ℤ) < 2 ^ B - x)
    (h2 : (r : ℤ) < 2 ^ B + x) :
    ((finRule f90 hq90)^[2 ^ B + r] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x = 0 := by
  rw [f90_iterate_two_pow_add,
    f90_single_apply_eq_zero_of_lt r (x - 2 ^ B) (by rw [lt_abs]; right; linarith),
    f90_single_apply_eq_zero_of_lt r (x + 2 ^ B) (by rw [lt_abs]; left; linarith), add_zero]

/-- **Zero runs from rest to one on rule `126`** ([RuleSpace] §5 Proposition 5.1(ii) at rule
`126`): at a large power of two `2 ^ B`, an even step `2 * (2 ^ B + r')` of rule `126` reads rule
`90` at step `2 ^ B + r'` by `f126_single_two_mul`, which splits into two translated copies of
the orbit at step `r'` that the ray's cell lies outside of, and an odd step reads three such
cells and `f126 0 0 0 = 0`; the speed may be zero. -/
theorem lateZeroRuns_f126 (p q : ℕ) (hpq : p < q) (e : ℤ) :
    ∀ n T : ℕ, ∃ t₀ : ℕ, T ≤ t₀ ∧ ∀ r < n,
      observedRationalRay (finRule f126 hq126) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e
        (t₀ + r) = 0 := by
  intro n T
  set M : ℕ := e.natAbs + 2 * n + 4 with hM
  set B : ℕ := T + q * M with hB
  have hlt : B < 2 ^ B := Nat.lt_two_pow_self
  have hq0 : 0 < q := by omega
  refine ⟨2 * 2 ^ B, by nlinarith, ?_⟩
  intro r hr
  unfold observedRationalRay
  have hk1 : q * (p * (2 * 2 ^ B + r) / q) ≤ p * (2 * 2 ^ B + r) := Nat.mul_div_le _ _
  generalize hkdef : p * (2 * 2 ^ B + r) / q = k at hk1 ⊢
  have habs : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
  have he1 : -(e.natAbs : ℤ) ≤ e := by rw [habs]; exact neg_abs_le e
  have he2 : e ≤ (e.natAbs : ℤ) := by rw [habs]; exact le_abs_self e
  have hkz : (q : ℤ) * k ≤ p * (2 * 2 ^ B + r) := by exact_mod_cast hk1
  have hpq' : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
  have hu : (B : ℤ) < 2 ^ B := by exact_mod_cast hlt
  have hBz : (q : ℤ) * M ≤ B := by
    rw [hB]; push_cast; have : (0 : ℤ) ≤ T := by positivity
    linarith
  have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq0
  have hMz : (M : ℤ) = e.natAbs + 2 * n + 4 := by rw [hM]; push_cast; ring
  have hM1 : (M : ℤ) ≤ q * M := by
    have : (0 : ℤ) ≤ M := by positivity
    nlinarith
  have ht0 : (0 : ℤ) ≤ 2 * 2 ^ B + r := by positivity
  have hbig : (k : ℤ) + 2 * M < 2 * 2 ^ B + r := by
    by_contra hcon
    have hcon := not_lt.mp hcon
    have h1 : (q : ℤ) * (2 * 2 ^ B + r - k) ≤ q * (2 * M) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (2 * 2 ^ B + r : ℤ) ≤ ((q : ℤ) - p) * (2 * 2 ^ B + r) := by
      nlinarith
    nlinarith
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hrz : (r : ℤ) < n := by exact_mod_cast hr
  obtain ⟨r', hr' | hr'⟩ := Nat.even_or_odd' r
  · -- even step
    have hrz' : 2 * (r' : ℤ) = r := by omega
    rw [show 2 * 2 ^ B + r = 2 * (2 ^ B + r') by omega, two_mul_halfIndex]
    have bound : ∀ z : ℤ, e + k - 1 ≤ z → z ≤ e + k + 1 →
        (r' : ℤ) < 2 ^ B - halfIndex z ∧ (r' : ℤ) < 2 ^ B + halfIndex z := by
      intro z h1 h2
      unfold halfIndex
      split_ifs <;> omega
    exact f90_single_two_pow_add_eq_zero B r' _ (bound _ (by omega) (by omega)).1
      (bound _ (by omega) (by omega)).2
  · -- odd step
    have hrz' : 2 * (r' : ℤ) + 1 = r := by omega
    rw [show 2 * 2 ^ B + r = 2 * (2 ^ B + r') + 1 by omega, Function.iterate_succ_apply',
      finRule_apply, two_mul_halfIndex, two_mul_halfIndex, two_mul_halfIndex]
    have bound : ∀ z : ℤ, e + k - 1 ≤ z → z ≤ e + k + 1 →
        (r' : ℤ) < 2 ^ B - halfIndex z ∧ (r' : ℤ) < 2 ^ B + halfIndex z := by
      intro z h1 h2
      unfold halfIndex
      split_ifs <;> omega
    rw [f90_single_two_pow_add_eq_zero B r' _ (bound (e + k - 1) (by omega) (by omega)).1
        (bound (e + k - 1) (by omega) (by omega)).2,
      f90_single_two_pow_add_eq_zero B r' _ (bound (e + k) (by omega) (by omega)).1
        (bound (e + k) (by omega) (by omega)).2,
      f90_single_two_pow_add_eq_zero B r' _ (bound (e + k + 1) (by omega) (by omega)).1
        (bound (e + k + 1) (by omega) (by omega)).2]
    exact hq126

/-! ## The main statement -/

/-- **A ray of rule `126` from the single seed, at a speed `p / q` strictly between rest and
one, from any cell, is not eventually periodic** ([RuleSpace] §5 Proposition 5.1 at rule `126`,
with Propositions 5.6 and 5.8): a one past every step on the ray and zero runs of every length
past every step together rule out a period. -/
theorem not_eventuallyPeriodic_observedRationalRay_f126_single (p q : ℕ) (hp : 0 < p)
    (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f126 hq126) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) :=
  not_eventuallyPeriodic_of_late_one_of_late_zero_runs _
    (exists_late_one_observedRationalRay_f126_single p q hp hpq e)
    (lateZeroRuns_f126 p q hpq e)

/-- **Joint satisfiability** of the speed hypotheses of the statement on rule `126`: the ray at
speed `1 / 2` from cell zero is not eventually periodic. -/
theorem not_eventuallyPeriodic_observedRationalRay_f126_single_nonvacuous :
    0 < 1 ∧ 1 < 2 ∧
      ¬ DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule f126 hq126) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 0) :=
  ⟨by decide, by decide,
    not_eventuallyPeriodic_observedRationalRay_f126_single 1 2 (by decide) (by decide) 0⟩

/-! ## Piece 5: the center column -/

/-- rule `90` from the single seed reads `1` at the cell `1` at the steps `2 ^ i - 1`, `1 ≤ i` -/
private theorem f90_single_apply_one_two_pow_sub_one (i : ℕ) (hi : 1 ≤ i) :
    ((finRule f90 hq90)^[2 ^ i - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 1 := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hpos : 0 < 2 ^ i := by positivity
  have hdis : (2 ^ i) &&& (2 ^ i - 1) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
    simp only [Nat.zero_testBit]
    by_cases h : i = k <;> simp [h]
  have := oneOfDisjoint (2 ^ i) (2 ^ i - 1) hdis
  rw [show 2 ^ i + (2 ^ i - 1) = 2 ^ (i + 1) - 1 by rw [pow_succ]; omega] at this
  have e : ((2 ^ i : ℕ) : ℤ) - ((2 ^ i - 1 : ℕ) : ℤ) = 1 := by omega
  rw [e] at this
  exact this

/-- **The center column of rule `126` from the single seed reads `1` at the steps `2 ^ j - 1`**
([RuleSpace] §5 Proposition 5.8): the odd step `2 * t + 1` with `t = 2 ^ (j - 1) - 1` reads the
cells `-1`, `0` and `1` of rule `90` at step `t`, which are `0, 1, 0` at `t = 0` and `1, 0, 1`
at every odd `t` of that form (the single seed of rule `90` reads `1` at the cell `1` at the
steps `2 ^ i - 1`, and is symmetric and of one parity). -/
theorem f126_single_apply_zero_two_pow_sub_one (j : ℕ) :
    ((finRule f126 hq126)^[2 ^ j - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · obtain ⟨i, rfl⟩ : ∃ i', j = i' + 1 := ⟨j - 1, by omega⟩
    have hpos : 0 < 2 ^ i := by positivity
    rw [show 2 ^ (i + 1) - 1 = 2 * (2 ^ i - 1) + 1 by rw [pow_succ]; omega,
      Function.iterate_succ_apply', finRule_apply, f126_single_two_mul, f126_single_two_mul,
      f126_single_two_mul]
    norm_num
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero, tsub_self, Function.iterate_zero, id_eq, Int.reduceNeg, ne_eq,
        neg_eq_zero, one_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne,
        Finsupp.single_eq_same]
      decide
    · have h1 := f90_single_apply_one_two_pow_sub_one i hi
      have h2 := finRule_f90_single_apply_neg (2 ^ i - 1) 1
      have h0 : ((finRule f90 hq90)^[2 ^ i - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = 0 := by
        apply f90_single_apply_eq_zero_of_odd
        have : 2 ≤ 2 ^ i := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
        have h3 : ((2 ^ i - 1 : ℕ) : ℤ) = 2 ^ i - 1 := by
          rw [Nat.cast_sub hpos]; push_cast; ring
        rw [h3]
        obtain ⟨m, hm⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        subst hm
        rw [pow_succ]
        omega
      rw [h2, h1, h0]
      decide

/-- **The center column of rule `126` from the single seed is not eventually periodic**
([RuleSpace] §5 Proposition 5.8): it reads a one at the steps `2 ^ j - 1` and zero runs of every
length past every step. At rule `90` the same ray, the speed-zero ray from cell `0`, is
eventually periodic, so rule `126` contrasts. -/
theorem not_eventuallyPeriodic_observedRationalRay_f126_single_zero :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f126 hq126) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1 0) := by
  refine not_eventuallyPeriodic_of_late_one_of_late_zero_runs _ ?_
    (lateZeroRuns_f126 0 1 (by omega) 0)
  intro T
  refine ⟨2 ^ T - 1, ?_, ?_⟩
  · have := Nat.lt_two_pow_self (n := T)
    omega
  · unfold observedRationalRay
    simpa using f126_single_apply_zero_two_pow_sub_one T

/-! ## Guards -/

/-- rule `126` from the single seed: the front cell reads `1` and nothing lies beyond it -/
private theorem f126_single_front (t : ℕ) :
    ((finRule f126 hq126)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (t : ℤ) = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', finRule_apply]
    push_cast
    rw [add_sub_cancel_right, ih,
      f126_single_apply_eq_zero_of_lt t ((t : ℤ) + 1)
        (by rw [abs_of_nonneg (by positivity)]; omega),
      f126_single_apply_eq_zero_of_lt t ((t : ℤ) + 1 + 1)
        (by rw [abs_of_nonneg (by positivity)]; omega)]
    decide

/-- **Guard: at speed one the ray of rule `126` from the single seed at cell `0` reads `1` at
every step**, the front, so it is eventually periodic; the speed hypothesis `p < q` is needed. -/
theorem observedRationalRay_f126_single_guard_one :
    DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f126 hq126) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 1 0) := by
  have hall : ∀ t,
      observedRationalRay (finRule f126 hq126) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      1 1 0 t = 1 := by
    intro t
    unfold observedRationalRay
    simpa using f126_single_front t
  exact ⟨1, 0, one_pos, fun u _ => by rw [hall, hall]⟩

end ECA

/-- info:
'ECA.f126_single_two_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f126_single_two_mul

/-- info:
'ECA.exists_late_one_observedRationalRay_f126_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_late_one_observedRationalRay_f126_single

/-- info:
'ECA.lateZeroRuns_f126' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.lateZeroRuns_f126

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f126_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f126_single

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f126_single_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f126_single_nonvacuous

/-- info:
'ECA.f126_single_apply_zero_two_pow_sub_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f126_single_apply_zero_two_pow_sub_one

/-- info:
'ECA.not_eventuallyPeriodic_observedRationalRay_f126_single_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedRationalRay_f126_single_zero

/-- info:
'ECA.observedRationalRay_f126_single_guard_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f126_single_guard_one
