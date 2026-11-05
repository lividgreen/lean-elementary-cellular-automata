module

public import ECA.RationalRayBound
import all ECA.RationalRayRate
import Mathlib.Combinatorics.Colex

/-!
# A Fibonacci lower bound on the ones of rule `90` rays at a class of speeds
([RuleSpace] §5 Proposition 5.5)

[RuleSpace] §5 Proposition 5.5 bounds the ones of a ray of rule `90` from the single seed above by
`q * Nat.fib (K + 1)` below step `2 ^ K` (`card_ones_observedRationalRay_f90_single_le_fib`). This
file matches that exponent from below at the speeds `(2 ^ m - 1) / (2 ^ m + 1)`, `1 ≤ m`.

## Main results

* `observedRationalRay_f90_single_maxSpeed` — at the speed `(2 ^ m - 1) / (2 ^ m + 1)` the ray
  from cell `0` reads a one at step `(2 ^ m + 1) * b` whenever `b` and `2 ^ m * b` share no binary
  digit.
* `fib_le_card_ones_observedRationalRay_f90_single_maxSpeed` — the ray reads a one at least
  `Nat.fib (L + 2)` times below step `(2 ^ m + 1) * 2 ^ L`. The count of the numbers below `2 ^ L`
  with no two set bits at distance `m` is at least that of the numbers with no two adjacent set
  bits, which is `Nat.fib (L + 2)`; both counts are private.
* `observedRationalRay_f90_single_maxSpeed_nonvacuous` and
  `observedRationalRay_f90_single_maxSpeed_guard` — a witness at `m = 2`, `b = 3`, and an
  instance at `b = 5` where the digits are shared and the ray reads `0`.
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## The digit fact -/

/-- **The digit fact at the speed `(2 ^ m - 1) / (2 ^ m + 1)`**: the ray of rule `90` from the
single seed, from cell `0`, reads a one at step `(2 ^ m + 1) * b` when `b` and `2 ^ m * b` share no
binary digit: the cell is `(2 ^ m - 1) * b`, which is `a - b` for the pair `(2 ^ m * b, b)` of sum
the step. -/
theorem observedRationalRay_f90_single_maxSpeed (m b : ℕ) (hm : 1 ≤ m)
    (hb : b &&& (2 ^ m * b) = 0) :
    observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      (2 ^ m - 1) (2 ^ m + 1) 0 ((2 ^ m + 1) * b) = 1 := by
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h := oneOfDisjoint (2 ^ m * b) b (by rw [Nat.and_comm]; exact hb)
  unfold observedRationalRay
  have hdiv : (2 ^ m - 1) * ((2 ^ m + 1) * b) / (2 ^ m + 1) = (2 ^ m - 1) * b := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv, show (2 ^ m + 1) * b = 2 ^ m * b + b by ring]
  rw [show (0 : ℤ) + (((2 ^ m - 1) * b : ℕ) : ℤ) = ((2 ^ m * b : ℕ) : ℤ) - (b : ℤ) by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 ^ m)]
    ring]
  exact h

/-! ## The word counts -/

/-- The numbers below `2 ^ L` with no two adjacent set bits. -/
private def noAdjacent (L : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ L)).filter fun b => b &&& (2 * b) = 0

/-- The numbers below `2 ^ L` with no two set bits at distance `m`. -/
private def noDistance (m L : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ L)).filter fun b => b &&& (2 ^ m * b) = 0

private theorem fib_le_card_noAdjacent (L : ℕ) : Nat.fib (L + 2) ≤ (noAdjacent L).card := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    match L, ih with
    | 0, _ => decide
    | 1, _ => decide
    | L + 2, ih =>
      have h1 := ih (L + 1) (by omega)
      have h0 := ih L (by omega)
      -- the even members: `2 w` for `w` with no two adjacent set bits below `2 ^ (L + 1)`
      have hE : ((noAdjacent (L + 1)).image fun w => 2 * w) ⊆ noAdjacent (L + 2) := by
        intro x hx
        simp only [noAdjacent, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx ⊢
        obtain ⟨w, ⟨hw, hw0⟩, rfl⟩ := hx
        refine ⟨by rw [pow_succ 2 (L + 1)]; omega, ?_⟩
        have := (and_eq_zero_iff_div (2 * w) (2 * (2 * w))).mpr
          ⟨Or.inl (by omega), by
            rw [show 2 * w / 2 = w by omega, show 2 * (2 * w) / 2 = 2 * w by omega]
            exact hw0⟩
        exact this
      -- the odd members: `4 w + 1` for `w` with no two adjacent set bits below `2 ^ L`
      have hO : ((noAdjacent L).image fun w => 4 * w + 1) ⊆ noAdjacent (L + 2) := by
        intro x hx
        simp only [noAdjacent, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx ⊢
        obtain ⟨w, ⟨hw, hw0⟩, rfl⟩ := hx
        refine ⟨by rw [pow_succ 2 (L + 1), pow_succ 2 L]; omega, ?_⟩
        refine (and_eq_zero_iff_div (4 * w + 1) (2 * (4 * w + 1))).mpr
          ⟨Or.inr (by omega), ?_⟩
        rw [show (4 * w + 1) / 2 = 2 * w by omega,
          show 2 * (4 * w + 1) / 2 = 4 * w + 1 by omega]
        refine (and_eq_zero_iff_div (2 * w) (4 * w + 1)).mpr ⟨Or.inl (by omega), ?_⟩
        rw [show 2 * w / 2 = w by omega, show (4 * w + 1) / 2 = 2 * w by omega]
        exact hw0
      have hd : Disjoint ((noAdjacent (L + 1)).image fun w => 2 * w)
          ((noAdjacent L).image fun w => 4 * w + 1) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_image] at hx hx'
        obtain ⟨w, _, rfl⟩ := hx
        obtain ⟨w', _, h⟩ := hx'
        omega
      have hcE : ((noAdjacent (L + 1)).image fun w => 2 * w).card = (noAdjacent (L + 1)).card :=
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)
      have hcO : ((noAdjacent L).image fun w => 4 * w + 1).card = (noAdjacent L).card :=
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)
      have hc := Finset.card_le_card (Finset.union_subset hE hO)
      rw [Finset.card_union_of_disjoint hd, hcE, hcO] at hc
      have hf : Nat.fib (L + 2 + 2) = Nat.fib (L + 1 + 2) + Nat.fib (L + 2) := by
        rw [show L + 2 + 2 = (L + 2) + 2 by rfl, Nat.fib_add_two]
        ring_nf
      omega

/-- The index in the list of positions below `L` ordered by residue modulo `m` and then by
quotient, so that the positions `p` and `p + m` are consecutive. -/
private def listIndex (m L p : ℕ) : ℕ :=
  if p % m < L % m then (p % m) * (L / m + 1) + p / m
  else (p % m) * (L / m) + L % m + p / m

private theorem listIndex_add (m L p : ℕ) (hm : 0 < m) :
    listIndex m L (p + m) = listIndex m L p + 1 := by
  unfold listIndex
  rw [Nat.add_mod_right, Nat.add_div_right _ hm]
  split_ifs <;> omega

private theorem exists_listIndex (m L i : ℕ) (hm : 0 < m) (hi : i < L) :
    ∃ p, p < L ∧ listIndex m L p = i := by
  have hL : m * (L / m) + L % m = L := Nat.div_add_mod L m
  have hρ : L % m < m := Nat.mod_lt _ hm
  set k := L / m with hk
  set ρ := L % m with hρdef
  clear_value k ρ
  by_cases hc : i < ρ * (k + 1)
  · have hk1 : 0 < k + 1 := by omega
    have hr : i / (k + 1) < ρ := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
    have hq : i % (k + 1) < k + 1 := Nat.mod_lt _ hk1
    have hdm : (k + 1) * (i / (k + 1)) + i % (k + 1) = i := Nat.div_add_mod i (k + 1)
    refine ⟨(i % (k + 1)) * m + i / (k + 1), ?_, ?_⟩
    · rcases Nat.lt_or_ge (i % (k + 1)) k with h | h
      · have : (i % (k + 1) + 1) * m ≤ k * m := Nat.mul_le_mul_right _ h
        nlinarith
      · have : i % (k + 1) = k := by omega
        rw [this]
        nlinarith
    · have hmod : ((i % (k + 1)) * m + i / (k + 1)) % m = i / (k + 1) := by
        rw [Nat.mul_comm, Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by omega)
      have hdiv : ((i % (k + 1)) * m + i / (k + 1)) / m = i % (k + 1) := by
        rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt (by omega)]
        rfl
      unfold listIndex
      rw [hmod, hdiv, ← hk, ← hρdef]
      simp only [hr, ↓reduceIte]
      nlinarith
  · push Not at hc
    have hj : i - ρ * (k + 1) < (m - ρ) * k := by
      have : ρ * (k + 1) + (m - ρ) * k = L := by
        have : ρ * (k + 1) + (m - ρ) * k = m * k + ρ := by
          zify [hρ.le]
          ring
        rw [this]
        linarith [Nat.mul_comm m k]
      omega
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at hj
        simp at hj
      · exact h
    set j := i - ρ * (k + 1) with hjdef
    have hr : j / k < m - ρ := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
    have hq : j % k < k := Nat.mod_lt _ hk0
    have hdm : k * (j / k) + j % k = j := Nat.div_add_mod j k
    have hrm : ρ + j / k < m := by omega
    refine ⟨(j % k) * m + (ρ + j / k), ?_, ?_⟩
    · have : (j % k + 1) * m ≤ k * m := Nat.mul_le_mul_right _ hq
      nlinarith
    · have hmod : ((j % k) * m + (ρ + j / k)) % m = ρ + j / k := by
        rw [Nat.mul_comm, Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt hrm
      have hdiv : ((j % k) * m + (ρ + j / k)) / m = j % k := by
        rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt hrm]
        rfl
      unfold listIndex
      rw [hmod, hdiv, ← hk, ← hρdef]
      simp only [Nat.not_lt_of_le (Nat.le_add_right ρ (j / k)), ↓reduceIte]
      have : (ρ + j / k) * k = ρ * k + k * (j / k) := by ring
      rw [this]
      have h3 : ρ * (k + 1) = ρ * k + ρ := by ring
      omega

/-- The number whose bit `p` below `L` is the bit `listIndex m L p` of `b`. -/
private def spread (m L b : ℕ) : ℕ :=
  ∑ p ∈ (Finset.range L).filter (fun p => b.testBit (listIndex m L p)), 2 ^ p

private theorem testBit_spread (m L b q : ℕ) :
    (spread m L b).testBit q = true ↔ q < L ∧ b.testBit (listIndex m L q) = true := by
  have h := Finset.toFinset_bitIndices_sum_two_pow
    ((Finset.range L).filter fun p => b.testBit (listIndex m L p))
  rw [← Nat.mem_bitIndices]
  have e : q ∈ (spread m L b).bitIndices ↔ q ∈ (spread m L b).bitIndices.toFinset := by simp
  rw [e]
  unfold spread
  rw [h]
  simp

private theorem spread_lt (m L b : ℕ) : spread m L b < 2 ^ L :=
  Nat.geomSum_lt (le_refl 2) (fun k hk => by simpa using (Finset.mem_filter.mp hk).1)

private theorem spread_noDistance (m L b : ℕ) (hm : 0 < m) (hb : b &&& (2 * b) = 0) :
    spread m L b &&& (2 ^ m * spread m L b) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.zero_testBit]
  by_contra hne
  simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
  obtain ⟨h1, hqm, h2⟩ := hne
  obtain ⟨p, rfl⟩ : ∃ p, q = p + m := ⟨q - m, by omega⟩
  rw [show p + m - m = p by omega] at h2
  have e1 := (testBit_spread m L b (p + m)).mp h1
  have e2 := (testBit_spread m L b p).mp h2
  rw [listIndex_add m L p hm] at e1
  have hz := congrArg (fun x => x.testBit (listIndex m L p + 1)) hb
  simp only [Nat.testBit_and, Nat.zero_testBit] at hz
  rw [show 2 * b = 2 ^ 1 * b by ring, Nat.testBit_two_pow_mul] at hz
  simp [e1.2, e2.2] at hz

private theorem spread_injOn (m L : ℕ) (hm : 0 < m) :
    Set.InjOn (spread m L) (noAdjacent L : Set ℕ) := by
  intro b hb b' hb' h
  have hb := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
  have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).1
  rw [Finset.mem_range] at hb hb'
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < L
  · obtain ⟨p, hp, rfl⟩ := exists_listIndex m L i hm hi
    have := testBit_spread m L b p
    have := testBit_spread m L b' p
    rw [h] at *
    cases h1 : b.testBit (listIndex m L p) <;> cases h2 : b'.testBit (listIndex m L p) <;> simp_all
  · push Not at hi
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb' (Nat.pow_le_pow_right (by norm_num) hi))]

private theorem card_noAdjacent_le (m L : ℕ) (hm : 0 < m) :
    (noAdjacent L).card ≤ (noDistance m L).card := by
  refine Finset.card_le_card_of_injOn (spread m L) (fun b hb => ?_) (spread_injOn m L hm)
  have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
  refine Finset.mem_coe.mpr ?_
  simp only [noDistance, Finset.mem_filter, Finset.mem_range]
  exact ⟨spread_lt m L b, spread_noDistance m L b hm hb'.2⟩

/-! ## The count -/

/-- **A Fibonacci lower bound at the speed `(2 ^ m - 1) / (2 ^ m + 1)`**: the ray of rule `90`
from the single seed, from cell `0`, reads a one at least `Nat.fib (L + 2)` times below step
`(2 ^ m + 1) * 2 ^ L`. The ceiling
`card_ones_observedRationalRay_f90_single_le_fib` bounds the ones below step `2 ^ K` by
`q * Nat.fib (K + 1)`; here the exponent `L` is attained from below at a step `(2 ^ m + 1) * 2 ^ L`
of the same order. -/
theorem fib_le_card_ones_observedRationalRay_f90_single_maxSpeed (m L : ℕ) (hm : 1 ≤ m) :
    Nat.fib (L + 2) ≤ ((Finset.range ((2 ^ m + 1) * 2 ^ L)).filter fun t =>
      observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
        (2 ^ m - 1) (2 ^ m + 1) 0 t = 1).card := by
  refine (fib_le_card_noAdjacent L).trans ((card_noAdjacent_le m L hm).trans ?_)
  refine Finset.card_le_card_of_injOn (fun b => (2 ^ m + 1) * b) (fun b hb => ?_) ?_
  · have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    rw [Finset.mem_range] at hb'
    have h2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    refine Finset.mem_coe.mpr ?_
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mul_lt_mul_of_pos_left hb'.1 (Nat.succ_pos _),
      observedRationalRay_f90_single_maxSpeed m b hm hb'.2⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos _) h

/-! ## The witness and the guard -/

/-- **Joint satisfiability**: at `m = 2` and `b = 3`, which share no binary digit with `4 * 3`,
the ray reads a one at step `5 * 3`. -/
theorem observedRationalRay_f90_single_maxSpeed_nonvacuous :
    1 ≤ 2 ∧ (3 : ℕ) &&& (2 ^ 2 * 3) = 0 ∧
      observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
        (2 ^ 2 - 1) (2 ^ 2 + 1) 0 ((2 ^ 2 + 1) * 3) = 1 :=
  ⟨by norm_num, by decide,
    observedRationalRay_f90_single_maxSpeed 2 3 (by norm_num) (by decide)⟩

/-- **The digit hypothesis is load-bearing**: at `m = 2` and `b = 5`, which shares a binary digit
with `4 * 5`, the ray reads `0` at step `5 * 5`. -/
theorem observedRationalRay_f90_single_maxSpeed_guard :
    (5 : ℕ) &&& (2 ^ 2 * 5) ≠ 0 ∧
      observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
        (2 ^ 2 - 1) (2 ^ 2 + 1) 0 ((2 ^ 2 + 1) * 5) = 0 := by
  refine ⟨by decide, ?_⟩
  have key : ∀ (a b t : ℕ) (c : ℤ), a &&& b ≠ 0 → t = a + b → c = (a : ℤ) - b →
      ((finRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) c = 0 := by
    intro a b t c hab ht hc
    subst ht hc
    exact zeroOfShared a b hab
  unfold observedRationalRay
  exact key 20 5 _ _ (by decide) (by norm_num) (by norm_num)

end ECA

/-- info: 'ECA.observedRationalRay_f90_single_maxSpeed' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f90_single_maxSpeed

/-- info: 'ECA.fib_le_card_ones_observedRationalRay_f90_single_maxSpeed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.fib_le_card_ones_observedRationalRay_f90_single_maxSpeed

/-- info: 'ECA.observedRationalRay_f90_single_maxSpeed_nonvacuous' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f90_single_maxSpeed_nonvacuous

/-- info: 'ECA.observedRationalRay_f90_single_maxSpeed_guard' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f90_single_maxSpeed_guard
