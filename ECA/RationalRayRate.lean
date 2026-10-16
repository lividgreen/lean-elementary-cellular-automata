module

public import ECA.RationalRaySeeds
public import ECA.MarkovErrorCount
import all ECA.RationalRaySeeds

/-!
# Rule 90 from the single seed: where the rays of speed one half and one third read a one
([RuleSpace] §5 Proposition 5.4)

`[RuleSpace] §5 Proposition 5.1` shows the ray of rule `90` from the single seed is not eventually
periodic at every speed strictly between `0` and `1`, and says nothing of how often it reads a one.
Registered as [RuleSpace] §5 Proposition 5.4, row RS-14. With `oneOfDisjoint` and
`zeroOfShared` the single seed reads `1` at cell `a - b` at step `a + b` exactly
when `a &&& b = 0`, which turns two of those rays into digit conditions.

* The ray of speed `1 / 2` from cell `1` reads `1` exactly at the steps `(4 ^ (i + 1) - 1) / 3`
  and twice that, so it holds at most two ones for each power of four below the horizon.
* The ray of speed `1 / 3` from cell `0` reads `1` exactly at the steps `3 b` with
  `b &&& (2 * b) = 0`, which is the classical statement
  `PascalColumns.choose_three_mul_mod_two_eq_one_iff` of the classical package: the binomial
  coefficient `C(3 n, n)` is odd exactly when `n` and `2 n` share no binary digit.

## Main results

* `and_three_mul_add_one_eq_zero_iff`, `and_three_mul_add_two_eq_zero_iff` — the two digit
  conditions behind the speed `1 / 2` ray.
* `observedRationalRay_f90_single_half_one_iff` — where the speed `1 / 2` ray from cell `1` reads
  a one.
* `observedRationalRay_f90_single_third_one_iff` — where the speed `1 / 3` ray from cell `0`
  reads a one.
* `markovErrorCount_le_card_ones` — at every order the Markov error count of a `ZMod 2` sequence is
  at most the number of its ones; `markovErrorCount_f90_single_half_le` — for the speed `1 / 2`
  ray the count at order `k` and horizon `T` is at most `2 * Nat.log 4 (T + k) + 2`.
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## The digit lemmas -/

private theorem and_eq_zero_iff_div (a b : ℕ) :
    a &&& b = 0 ↔ (a % 2 = 0 ∨ b % 2 = 0) ∧ (a / 2) &&& (b / 2) = 0 := by
  constructor
  · intro h
    have h0 : (a &&& b).testBit 0 = false := by rw [h]; simp
    rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero] at h0
    refine ⟨?_, ?_⟩
    · by_contra hc
      push Not at hc
      have e1 : a % 2 = 1 := by omega
      have e2 : b % 2 = 1 := by omega
      simp [e1, e2] at h0
    · apply Nat.eq_of_testBit_eq
      intro i
      have hi : (a &&& b).testBit (i + 1) = false := by rw [h]; simp
      rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ] at hi
      rw [Nat.testBit_and, Nat.zero_testBit]
      exact hi
  · rintro ⟨h0, h1⟩
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases i with
    | zero =>
      rw [Nat.testBit_zero, Nat.testBit_zero]
      rcases h0 with h | h <;> simp [h]
    | succ i =>
      have := congrArg (fun n => n.testBit i) h1
      simp only [Nat.testBit_and, Nat.zero_testBit] at this
      rw [Nat.testBit_succ, Nat.testBit_succ]
      exact this

private theorem and_three_mul_eq_zero_iff (w : ℕ) : (3 * w) &&& w = 0 ↔ w = 0 := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    constructor
    · intro h
      rw [and_eq_zero_iff_div] at h
      obtain ⟨h0, h1⟩ := h
      by_cases hw : w = 0
      · exact hw
      · rcases Nat.even_or_odd' w with ⟨u, rfl | rfl⟩
        · have e : 3 * (2 * u) / 2 = 3 * u := by omega
          rw [e, show 2 * u / 2 = u by omega] at h1
          have := (ih u (by omega)).1 h1
          omega
        · omega
    · rintro rfl; simp

private theorem pow_four_succ (i : ℕ) : 3 * ((4 ^ i - 1) / 3) + 1 = 4 ^ i := by
  have : 4 ^ i % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have : 0 < 4 ^ i := by positivity
  omega

private theorem g_succ (i : ℕ) : (4 ^ (i + 1) - 1) / 3 = 4 * ((4 ^ i - 1) / 3) + 1 := by
  have h := pow_four_succ i
  rw [pow_succ]
  omega

private theorem step_one (w : ℕ) :
    (3 * w + 1) &&& w = 0 ↔ w = 0 ∨ ∃ u, w = 2 * u + 1 ∧ (3 * u + 2) &&& u = 0 := by
  rw [and_eq_zero_iff_div]
  constructor
  · rintro ⟨h0, h1⟩
    rcases Nat.even_or_odd' w with ⟨u, rfl | rfl⟩
    · rw [show (3 * (2 * u) + 1) / 2 = 3 * u by omega, show 2 * u / 2 = u by omega] at h1
      have := (and_three_mul_eq_zero_iff u).1 h1
      omega
    · rw [show (3 * (2 * u + 1) + 1) / 2 = 3 * u + 2 by omega,
        show (2 * u + 1) / 2 = u by omega] at h1
      exact Or.inr ⟨u, rfl, h1⟩
  · rintro (rfl | ⟨u, rfl, h⟩)
    · simp
    · refine ⟨Or.inl (by omega), ?_⟩
      rw [show (3 * (2 * u + 1) + 1) / 2 = 3 * u + 2 by omega,
        show (2 * u + 1) / 2 = u by omega]
      exact h

private theorem step_two (w : ℕ) :
    (3 * w + 2) &&& w = 0 ↔ ∃ u, w = 2 * u ∧ (3 * u + 1) &&& u = 0 := by
  rw [and_eq_zero_iff_div]
  constructor
  · rintro ⟨h0, h1⟩
    rcases Nat.even_or_odd' w with ⟨u, rfl | rfl⟩
    · rw [show (3 * (2 * u) + 2) / 2 = 3 * u + 1 by omega, show 2 * u / 2 = u by omega] at h1
      exact ⟨u, rfl, h1⟩
    · omega
  · rintro ⟨u, rfl, h⟩
    refine ⟨Or.inl (by omega), ?_⟩
    rw [show (3 * (2 * u) + 2) / 2 = 3 * u + 1 by omega, show 2 * u / 2 = u by omega]
    exact h

/-- The two digit conditions, together, by strong induction on `w`. -/
private theorem and_three_mul_add_aux (w : ℕ) :
    ((3 * w + 1) &&& w = 0 ↔ ∃ i : ℕ, w = (4 ^ i - 1) / 3) ∧
    ((3 * w + 2) &&& w = 0 ↔ ∃ i : ℕ, w = 2 * ((4 ^ i - 1) / 3)) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have P1 : (3 * w + 1) &&& w = 0 ↔ ∃ i : ℕ, w = (4 ^ i - 1) / 3 := by
      rw [step_one]
      constructor
      · rintro (rfl | ⟨u, rfl, h⟩)
        · exact ⟨0, by simp⟩
        · obtain ⟨i, hi⟩ := (ih u (by omega)).2.1 h
          exact ⟨i + 1, by rw [g_succ]; omega⟩
      · rintro ⟨i, hi⟩
        cases i with
        | zero => left; simpa using hi
        | succ i =>
          rw [g_succ] at hi
          right
          refine ⟨2 * ((4 ^ i - 1) / 3), by omega, ?_⟩
          have hu : 2 * ((4 ^ i - 1) / 3) < w := by omega
          exact (ih _ hu).2.2 ⟨i, rfl⟩
    refine ⟨P1, ?_⟩
    rw [step_two]
    constructor
    · rintro ⟨u, rfl, h⟩
      by_cases hu : u = 0
      · exact ⟨0, by simp [hu]⟩
      · obtain ⟨i, hi⟩ := (ih u (by omega)).1.1 h
        exact ⟨i, by omega⟩
    · rintro ⟨i, hi⟩
      refine ⟨(4 ^ i - 1) / 3, hi, ?_⟩
      by_cases h0 : (4 ^ i - 1) / 3 = 0
      · rw [h0]; simp
      · exact (ih _ (by omega)).1.2 ⟨i, rfl⟩

theorem and_three_mul_add_one_eq_zero_iff (w : ℕ) :
    (3 * w + 1) &&& w = 0 ↔ ∃ i : ℕ, w = (4 ^ i - 1) / 3 :=
  (and_three_mul_add_aux w).1

theorem and_three_mul_add_two_eq_zero_iff (w : ℕ) :
    (3 * w + 2) &&& w = 0 ↔ ∃ i : ℕ, w = 2 * ((4 ^ i - 1) / 3) :=
  (and_three_mul_add_aux w).2

/-! ## The two rays -/

/-- The single seed reads `1` at cell `a - b`, step `a + b`, exactly when `a &&& b = 0`. -/
private theorem single_apply_eq_one_iff (a b : ℕ) :
    ((finRule f90 hq90)^[a + b] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) ((a : ℤ) - b) = 1 ↔
      a &&& b = 0 := by
  constructor
  · intro h
    by_contra hne
    have := zeroOfShared a b hne
    rw [this] at h
    exact zero_ne_one h
  · exact oneOfDisjoint a b

private theorem single_apply_ne_one_of_odd (t : ℕ) (x : ℤ) (h : ¬ 2 ∣ ((t : ℤ) + x)) :
    ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x ≠ 1 := by
  rw [f90_single_apply_eq_zero_of_odd t x h]
  exact zero_ne_one

/-- **Where the ray of speed `1 / 2` from cell `1` reads a one**: exactly at the steps
`(4 ^ (i + 1) - 1) / 3` and twice that. The ray of rule `90` from the single seed of
`[RuleSpace] §5 Proposition 5.1`. -/
theorem observedRationalRay_f90_single_half_one_iff (t : ℕ) :
    observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 1 t = 1 ↔
      ∃ i : ℕ, t = (4 ^ (i + 1) - 1) / 3 ∨ t = 2 * ((4 ^ (i + 1) - 1) / 3) := by
  unfold observedRationalRay
  have hr : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr
  · have h := single_apply_ne_one_of_odd t (1 + ((1 * t / 2 : ℕ) : ℤ)) (by push_cast; omega)
    constructor
    · intro h'; exact absurd h' h
    · rintro ⟨i, hi⟩
      rw [g_succ] at hi
      omega
  · obtain ⟨w, rfl⟩ : ∃ w, t = 4 * w + 1 := ⟨t / 4, by omega⟩
    have e := single_apply_eq_one_iff (3 * w + 1) w
    rw [show 3 * w + 1 + w = 4 * w + 1 by omega,
      show (((3 * w + 1 : ℕ) : ℤ) - (w : ℤ)) = 1 + ((1 * (4 * w + 1) / 2 : ℕ) : ℤ) by
        push_cast; omega] at e
    rw [e, and_three_mul_add_one_eq_zero_iff]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Or.inl (by rw [g_succ]; omega)⟩
    · rintro ⟨i, hi | hi⟩
      · rw [g_succ] at hi
        exact ⟨i, by omega⟩
      · rw [g_succ] at hi
        omega
  · obtain ⟨w, rfl⟩ : ∃ w, t = 4 * w + 2 := ⟨t / 4, by omega⟩
    have e := single_apply_eq_one_iff (3 * w + 2) w
    rw [show 3 * w + 2 + w = 4 * w + 2 by omega,
      show (((3 * w + 2 : ℕ) : ℤ) - (w : ℤ)) = 1 + ((1 * (4 * w + 2) / 2 : ℕ) : ℤ) by
        push_cast; omega] at e
    rw [e, and_three_mul_add_two_eq_zero_iff]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Or.inr (by rw [g_succ]; omega)⟩
    · rintro ⟨i, hi | hi⟩
      · rw [g_succ] at hi
        omega
      · rw [g_succ] at hi
        exact ⟨i, by omega⟩
  · have h := single_apply_ne_one_of_odd t (1 + ((1 * t / 2 : ℕ) : ℤ)) (by push_cast; omega)
    constructor
    · intro h'; exact absurd h' h
    · rintro ⟨i, hi⟩
      rw [g_succ] at hi
      omega

/-- **Where the ray of speed `1 / 3` from cell `0` reads a one**: exactly at the steps `3 b` with
`b` and `2 b` sharing no binary digit, the classical statement
`PascalColumns.choose_three_mul_mod_two_eq_one_iff` of the classical package. The ray of rule `90`
from the single seed of `[RuleSpace] §5 Proposition 5.1`. -/
theorem observedRationalRay_f90_single_third_one_iff (t : ℕ) :
    observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 3 0 t = 1 ↔
      ∃ b : ℕ, t = 3 * b ∧ b &&& (2 * b) = 0 := by
  unfold observedRationalRay
  have hr : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · obtain ⟨b, rfl⟩ : ∃ b, t = 3 * b := ⟨t / 3, by omega⟩
    have e := single_apply_eq_one_iff (2 * b) b
    rw [show 2 * b + b = 3 * b by omega,
      show (((2 * b : ℕ) : ℤ) - (b : ℤ)) = 0 + ((1 * (3 * b) / 3 : ℕ) : ℤ) by
        push_cast; omega] at e
    rw [e, Nat.and_comm]
    constructor
    · intro h; exact ⟨b, rfl, h⟩
    · rintro ⟨c, hc, h⟩
      have : c = b := by omega
      subst this; exact h
  · have h := single_apply_ne_one_of_odd t (0 + ((1 * t / 3 : ℕ) : ℤ)) (by push_cast; omega)
    constructor
    · intro h'; exact absurd h' h
    · rintro ⟨b, hb, _⟩; omega
  · obtain ⟨b, rfl⟩ : ∃ b, t = 3 * b + 2 := ⟨t / 3, by omega⟩
    have e := single_apply_eq_one_iff (2 * b + 1) (b + 1)
    rw [show 2 * b + 1 + (b + 1) = 3 * b + 2 by omega,
      show (((2 * b + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ)) = 0 + ((1 * (3 * b + 2) / 3 : ℕ) : ℤ) by
        push_cast; omega] at e
    have hne : (2 * b + 1) &&& (b + 1) ≠ 0 := by
      have := and_ne_zero_two_mul_sub (b + 1) (by omega)
      rwa [show 2 * (b + 1) - 1 = 2 * b + 1 by omega] at this
    constructor
    · intro h
      rw [e] at h
      exact absurd h hne
    · rintro ⟨c, hc, _⟩
      omega

/-! ## The count -/

/-- **The Markov error count is at most the number of ones**: the constant law `0` errs exactly
at the ones. -/
theorem markovErrorCount_le_card_ones (k : ℕ) (x : ℕ → ZMod 2) (T : ℕ) :
    markovErrorCount k x T ≤
      ((Finset.range T).filter fun s => x (s + k) = 1).card := by
  refine le_trans (ciInf_le (OrderBot.bddBelow _) (fun _ => (0 : ZMod 2))) ?_
  unfold predictorErrors
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_filter] at hs ⊢
  refine ⟨hs.1, ?_⟩
  have h := hs.2
  have : x (s + k) ≠ 0 := fun h0 => h h0.symm
  generalize x (s + k) = z at this ⊢
  revert z
  decide

/-- **A logarithmic bound on the Markov error count at speed `1 / 2`**: at every order `k` and
horizon `T`, at most `2 * Nat.log 4 (T + k) + 2`. -/
theorem markovErrorCount_f90_single_half_le (k T : ℕ) :
    markovErrorCount k
      (observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 1) T
      ≤ 2 * Nat.log 4 (T + k) + 2 := by
  refine le_trans (markovErrorCount_le_card_ones k _ T) ?_
  set L := Nat.log 4 (T + k) with hL
  have hsub : ((Finset.range T).filter fun s =>
      observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 1
        (s + k) = 1) ⊆
      ((Finset.range (L + 1)).image fun i => (4 ^ (i + 1) - 1) / 3 - k) ∪
        ((Finset.range (L + 1)).image fun i => 2 * ((4 ^ (i + 1) - 1) / 3) - k) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    obtain ⟨hsT, hs1⟩ := hs
    rw [observedRationalRay_f90_single_half_one_iff] at hs1
    obtain ⟨i, hi⟩ := hs1
    have h4 : 4 ^ i ≤ 4 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hg := pow_four_succ (i + 1)
    have hgi := g_succ i
    have hpi := pow_four_succ i
    have hlt : 4 ^ i ≤ T + k := by
      rcases hi with hi | hi <;> omega
    have hiL : i ≤ L := Nat.le_log_of_pow_le (by norm_num) hlt
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    rcases hi with hi | hi
    · exact Or.inl ⟨i, by omega, by omega⟩
    · exact Or.inr ⟨i, by omega, by omega⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := Finset.card_image_le (s := Finset.range (L + 1))
    (f := fun i => (4 ^ (i + 1) - 1) / 3 - k)
  have h2 := Finset.card_image_le (s := Finset.range (L + 1))
    (f := fun i => 2 * ((4 ^ (i + 1) - 1) / 3) - k)
  simp only [Finset.card_range] at h1 h2
  omega

end ECA

/-- info: 'ECA.and_three_mul_add_one_eq_zero_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.and_three_mul_add_one_eq_zero_iff

/-- info: 'ECA.and_three_mul_add_two_eq_zero_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.and_three_mul_add_two_eq_zero_iff

/-- info: 'ECA.observedRationalRay_f90_single_half_one_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f90_single_half_one_iff

/-- info: 'ECA.observedRationalRay_f90_single_third_one_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f90_single_third_one_iff

/-- info: 'ECA.markovErrorCount_le_card_ones' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_le_card_ones

/-- info: 'ECA.markovErrorCount_f90_single_half_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_f90_single_half_le
