/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.RationalRayRate
public import Mathlib.Data.Nat.Fib.Basic
public import CellularAutomata.RationalRayPairs
import all CellularAutomata.RationalRayRate
-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# A Fibonacci bound on the ones of a rule `90` ray at every speed
([RuleSpace] §5 Proposition 5.5)

The upper bound of [RuleSpace] §5 Proposition 5.5, rows RS-15 and RS-16. The pairs `(a, b)` of
naturals below `2 ^ K` with no shared binary digit and `D a - P b = c` are counted by their lowest
binary digits: those digits are `(0, 0)`, `(1, 0)` or `(0, 1)`, and the quotients by two are a pair
below `2 ^ (K - 1)` on a line through half of `c - D i + P j`. At every pair of positive integers
the count is at most `Nat.fib (K + 1)`: when `D` and `P` are not both even it is a two-branch
count, an odd value having one child and an even value two, and that count is bounded by a
product of Fibonacci numbers, one for each of the parities met along the next steps of the
one-child branch. For a *closing* pair `(D, P)` (both odd with `(D + P) / 2` odd, or exactly one
even and that one `2` modulo `4`) a line has at most one admissible lowest digit pair, or two of
which one has one, and the bound has its own one-step proof. The bound is then carried to the rays
of rule `90` from the single seed.

## Main results

* `lineCount_le_fib_of_pos` — at every `0 < D` and `0 < P` every line `D a - P b = c` holds at
  most `Nat.fib (K + 1)` pairs of naturals below `2 ^ K` with no shared binary digit.
* `repCountBound` — the two-branch count `repCount G E` is at most `Nat.fib (K + 1)` at an odd
  `G` and a nonzero even `E`; `lineCount_eq_repCount_of_even_odd`,
  `lineCount_eq_repCount_of_odd_even` and `lineCount_eq_repCount_of_odd_odd` identify the line
  count with it.
* `card_ones_observedRationalRay_f90_single_le_fib` — a ray of speed `p / q` with `0 < p < q`,
  from any cell, reads at most `q * Nat.fib (K + 1)` ones below step `2 ^ K`.
* `lineCount_le_fib`, `card_ones_observedRationalRay_f90_single_le` — the same bounds at a
  closing pair, or the double of one, by the one-step proof.
* `lineCount_not_le_fib_of_neg` — positivity is load-bearing.

## Scope

An upper bound only, from the single seed: nothing here says which exponent a given speed
attains, and the product of Fibonacci numbers that bounds the two-branch count is not a public
declaration.
-/

@[expose] public section

namespace RationalRayBound

open ExtremeTapWidth EndpointClasses
open ObservedColumn (observedRationalRay hq90)

/-! ## Piece 1: the line count -/

/-- **A closing line pair**: both odd with `(D + P) / 2` odd, or exactly one even and that one
`2` modulo `4`. -/
def Closing (D P : ℤ) : Prop :=
  (Odd D ∧ Odd P ∧ Odd ((D + P) / 2)) ∨ (Even D ∧ Odd P ∧ D % 4 = 2) ∨
    (Odd D ∧ Even P ∧ P % 4 = 2)

/-- **The line count**: the pairs of naturals below `2 ^ K` with no shared binary digit on the
line `D a - P b = c`. -/
def lineCount (D P c : ℤ) (K : ℕ) : ℕ :=
  ((Finset.range (2 ^ K) ×ˢ Finset.range (2 ^ K)).filter
    fun ab : ℕ × ℕ => ab.1 &&& ab.2 = 0 ∧ D * ab.1 - P * ab.2 = c).card

theorem lineCount_zero (D P c : ℤ) : lineCount D P c 0 = if c = 0 then 1 else 0 := by
  unfold lineCount
  simp only [pow_zero, Finset.range_one, Finset.singleton_product_singleton,
    Finset.filter_singleton]
  by_cases h : c = 0
  · simp [h]
  · simp [h, Ne.symm h]

/-- The pairs with lowest digits `(i, j)` correspond to the pairs below half the bound on the
line through half of the shifted value. -/
private theorem fiber_card (D P c' : ℤ) (K i j : ℕ) (hi : i < 2) (hj : j < 2)
    (hij : i = 0 ∨ j = 0) :
    ((Finset.range (2 ^ (K + 1)) ×ˢ Finset.range (2 ^ (K + 1))).filter
      fun ab : ℕ × ℕ => (ab.1 % 2 = i ∧ ab.2 % 2 = j) ∧ ab.1 &&& ab.2 = 0 ∧
        D * ab.1 - P * ab.2 = 2 * c' + D * i - P * j).card = lineCount D P c' K := by
  unfold lineCount
  have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
  refine Finset.card_nbij' (fun ab => (ab.1 / 2, ab.2 / 2)) (fun ab => (2 * ab.1 + i, 2 * ab.2 + j))
    ?_ ?_ ?_ ?_
  · intro ab hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab ⊢
    obtain ⟨⟨h1, h2⟩, ⟨e1, e2⟩, hand, hl⟩ := hab
    rw [RationalRayRate.and_eq_zero_iff_div] at hand
    refine ⟨⟨by omega, by omega⟩, hand.2, ?_⟩
    have ha : (ab.1 : ℤ) = 2 * ((ab.1 / 2 : ℕ) : ℤ) + i := by omega
    have hb : (ab.2 : ℤ) = 2 * ((ab.2 / 2 : ℕ) : ℤ) + j := by omega
    rw [ha, hb] at hl
    linarith
  · intro ab hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab ⊢
    obtain ⟨⟨h1, h2⟩, hand, hl⟩ := hab
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_, ?_⟩
    · rw [RationalRayRate.and_eq_zero_iff_div]
      refine ⟨by omega, ?_⟩
      rw [show (2 * ab.1 + i) / 2 = ab.1 by omega, show (2 * ab.2 + j) / 2 = ab.2 by omega]
      exact hand
    · push_cast
      linear_combination 2 * hl
  · intro ab hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
    obtain ⟨_, ⟨e1, e2⟩, _⟩ := hab
    ext <;> simp <;> omega
  · intro ab _
    ext <;> simp <;> omega

/-- The fiber with lowest digits `(i, j)`: empty unless the shifted value is even, and then the
line count of half of it one level down. -/
private theorem fiber_eq (D P c : ℤ) (K i j : ℕ) (hi : i < 2) (hj : j < 2)
    (hij : i = 0 ∨ j = 0) :
    ((Finset.range (2 ^ (K + 1)) ×ˢ Finset.range (2 ^ (K + 1))).filter
      fun ab : ℕ × ℕ => (ab.1 % 2 = i ∧ ab.2 % 2 = j) ∧ ab.1 &&& ab.2 = 0 ∧
        D * ab.1 - P * ab.2 = c).card =
      if 2 ∣ c - D * i + P * j then lineCount D P ((c - D * i + P * j) / 2) K else 0 := by
  split_ifs with hd
  · obtain ⟨c', hc'⟩ := hd
    have hc : c = 2 * c' + D * i - P * j := by linarith
    have : (c - D * i + P * j) / 2 = c' := by omega
    rw [this, hc]
    exact fiber_card D P c' K i j hi hj hij
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ab _ hab
    obtain ⟨⟨e1, e2⟩, _, hl⟩ := hab
    apply hd
    have ha : (ab.1 : ℤ) = 2 * ((ab.1 / 2 : ℕ) : ℤ) + i := by omega
    have hb : (ab.2 : ℤ) = 2 * ((ab.2 / 2 : ℕ) : ℤ) + j := by omega
    rw [ha, hb] at hl
    exact ⟨D * ((ab.1 / 2 : ℕ) : ℤ) - P * ((ab.2 / 2 : ℕ) : ℤ), by linarith⟩

/-- **One level of the recursion**: the count at level `K + 1` is the sum over the three
admissible lowest digit pairs of the count at level `K` on the line through half the shifted
value, when that value is even. -/
theorem lineCount_succ (D P c : ℤ) (K : ℕ) :
    lineCount D P c (K + 1) =
      (if 2 ∣ c then lineCount D P (c / 2) K else 0) +
      (if 2 ∣ c - D then lineCount D P ((c - D) / 2) K else 0) +
      (if 2 ∣ c + P then lineCount D P ((c + P) / 2) K else 0) := by
  have hf : ∀ x : ℕ × ℕ, x ∈
      (Finset.range (2 ^ (K + 1)) ×ˢ Finset.range (2 ^ (K + 1))).filter
      (fun ab : ℕ × ℕ => ab.1 &&& ab.2 = 0 ∧ D * ab.1 - P * ab.2 = c) →
      (x.1 % 2, x.2 % 2) ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ℕ × ℕ)) := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    have := (RationalRayRate.and_eq_zero_iff_div x.1 x.2).1 hx.2.1
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  unfold lineCount
  rw [Finset.card_eq_sum_card_fiberwise hf]
  have e : ∀ i j : ℕ, ((Finset.range (2 ^ (K + 1)) ×ˢ Finset.range (2 ^ (K + 1))).filter
      fun ab : ℕ × ℕ => (ab.1 &&& ab.2 = 0 ∧ D * ab.1 - P * ab.2 = c) ∧
        (ab.1 % 2, ab.2 % 2) = (i, j)).card =
      ((Finset.range (2 ^ (K + 1)) ×ˢ Finset.range (2 ^ (K + 1))).filter
      fun ab : ℕ × ℕ => (ab.1 % 2 = i ∧ ab.2 % 2 = j) ∧ ab.1 &&& ab.2 = 0 ∧
        D * ab.1 - P * ab.2 = c).card := by
    intro i j
    congr 1
    apply Finset.filter_congr
    intro x _
    simp only [Prod.mk.injEq]
    tauto
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Finset.filter_filter]
  rw [e, e, e, fiber_eq D P c K 0 0 (by omega) (by omega) (by omega),
    fiber_eq D P c K 1 0 (by omega) (by omega) (by omega),
    fiber_eq D P c K 0 1 (by omega) (by omega) (by omega)]
  simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero, add_zero]
  rw [add_assoc]
  rfl

private theorem single_a (D P c : ℤ) (h0 : 2 ∣ c) (h1 : ¬ 2 ∣ c - D) (h2 : ¬ 2 ∣ c + P) :
    ∃ c', ∀ K, lineCount D P c (K + 1) = lineCount D P c' K :=
  ⟨c / 2, fun K => by simp only [lineCount_succ, h0, h1, h2, ↓reduceIte]; simp⟩

private theorem single_b (D P c : ℤ) (h0 : ¬ 2 ∣ c) (h1 : 2 ∣ c - D) (h2 : ¬ 2 ∣ c + P) :
    ∃ c', ∀ K, lineCount D P c (K + 1) = lineCount D P c' K :=
  ⟨(c - D) / 2, fun K => by simp only [lineCount_succ, h0, h1, h2, ↓reduceIte]; simp⟩

private theorem single_c (D P c : ℤ) (h0 : ¬ 2 ∣ c) (h1 : ¬ 2 ∣ c - D) (h2 : 2 ∣ c + P) :
    ∃ c', ∀ K, lineCount D P c (K + 1) = lineCount D P c' K :=
  ⟨(c + P) / 2, fun K => by simp only [lineCount_succ, h0, h1, h2, ↓reduceIte]; simp⟩

/-- **The two-term shape**: some line is a single step from one level down, and the other one
is a sum of two lines one level down, of which one is itself a single step. -/
private def StepShape (D P c : ℤ) : Prop :=
  (∃ c', ∀ K, lineCount D P c (K + 1) = lineCount D P c' K) ∨
    ∃ c₁ c₂ : ℤ, (∃ c', ∀ K, lineCount D P c₁ (K + 1) = lineCount D P c' K) ∧
      c₁ ≠ c₂ ∧
      ∀ K, lineCount D P c (K + 1) = lineCount D P c₁ K + lineCount D P c₂ K

private theorem stepShape_two (D P c c₁ c₂ : ℤ) (hne : c₁ ≠ c₂)
    (hs : (∃ c', ∀ K, lineCount D P c₁ (K + 1) = lineCount D P c' K) ∨
      (∃ c', ∀ K, lineCount D P c₂ (K + 1) = lineCount D P c' K))
    (hK : ∀ K, lineCount D P c (K + 1) = lineCount D P c₁ K + lineCount D P c₂ K) :
    StepShape D P c := by
  right
  rcases hs with hs | hs
  · exact ⟨c₁, c₂, hs, hne, hK⟩
  · exact ⟨c₂, c₁, hs, hne.symm, fun K => by rw [hK, add_comm]⟩

private theorem stepShape (D P : ℤ) (h : Closing D P) (c : ℤ) : StepShape D P c := by
  unfold Closing at h
  rcases h with ⟨hD, hP, hDP⟩ | ⟨hD, hP, h4⟩ | ⟨hD, hP, h4⟩ <;>
    simp only [Int.odd_iff, Int.even_iff] at hD hP
  · simp only [Int.odd_iff] at hDP
    by_cases hc : 2 ∣ c
    · exact Or.inl (single_a D P c hc (by omega) (by omega))
    · refine stepShape_two D P c ((c - D) / 2) ((c + P) / 2) (by omega) ?_ ?_
      · by_cases h2 : 2 ∣ (c - D) / 2
        · exact Or.inl (single_a D P _ h2 (by omega) (by omega))
        · exact Or.inr (single_a D P _ (by omega) (by omega) (by omega))
      · intro K
        have b : 2 ∣ c - D := by omega
        have d : 2 ∣ c + P := by omega
        simp only [lineCount_succ, hc, b, d, ↓reduceIte, zero_add]
  · by_cases hc : 2 ∣ c
    · refine stepShape_two D P c (c / 2) ((c - D) / 2) (by omega) ?_ ?_
      · by_cases h2 : 2 ∣ c / 2
        · exact Or.inr (single_c D P _ (by omega) (by omega) (by omega))
        · exact Or.inl (single_c D P _ h2 (by omega) (by omega))
      · intro K
        have b : 2 ∣ c - D := by omega
        have d : ¬ 2 ∣ c + P := by omega
        simp only [lineCount_succ, hc, b, d, ↓reduceIte, add_zero]
    · exact Or.inl (single_c D P c hc (by omega) (by omega))
  · by_cases hc : 2 ∣ c
    · refine stepShape_two D P c (c / 2) ((c + P) / 2) (by omega) ?_ ?_
      · by_cases h2 : 2 ∣ c / 2
        · exact Or.inr (single_b D P _ (by omega) (by omega) (by omega))
        · exact Or.inl (single_b D P _ h2 (by omega) (by omega))
      · intro K
        have b : ¬ 2 ∣ c - D := by omega
        have d : 2 ∣ c + P := by omega
        simp only [lineCount_succ, hc, b, d, ↓reduceIte, add_zero]
    · exact Or.inl (single_b D P c hc (by omega) (by omega))

/-- **The Fibonacci bound on a line**: at a closing pair `(D, P)` every line holds at most
`Nat.fib (K + 1)` pairs of naturals below `2 ^ K` with no shared binary digit
([RuleSpace] §5 Proposition 5.5, the pairs with a one-step proof). -/
theorem lineCount_le_fib (D P : ℤ) (h : Closing D P) (c : ℤ) (K : ℕ) :
    lineCount D P c K ≤ Nat.fib (K + 1) := by
  suffices H : ∀ K : ℕ, ∀ c : ℤ, lineCount D P c K ≤ Nat.fib (K + 1) ∧
      lineCount D P c (K + 1) ≤ Nat.fib (K + 2) from (H K c).1
  intro K
  induction K with
  | zero =>
    intro c
    refine ⟨by rw [lineCount_zero]; split_ifs <;> simp, ?_⟩
    rcases stepShape D P h c with ⟨c', hc'⟩ | ⟨c₁, c₂, -, hne, hK⟩
    · rw [hc']
      rw [lineCount_zero]
      split_ifs <;> simp
    · rw [hK, lineCount_zero, lineCount_zero]
      split_ifs <;> first | (exfalso; apply hne; omega) | simp
  | succ K ih =>
    intro c
    refine ⟨(ih c).2, ?_⟩
    rcases stepShape D P h c with ⟨c', hc'⟩ | ⟨c₁, c₂, ⟨c'', hc''⟩, hne, hK⟩
    · rw [hc']
      exact le_trans (ih c').2 (Nat.fib_mono (by omega))
    · rw [hK, hc'' K, show K + 1 + 2 = K + 1 + 1 + 1 by rfl, Nat.fib_add_two (n := K + 1)]
      have h1 := (ih c'').1
      have h2 : lineCount D P c₂ (K + 1) ≤ Nat.fib (K + 1 + 1) := (ih c₂).2
      omega

/-- Doubling `D`, `P` and `c` leaves the line count unchanged. -/
theorem lineCount_two_mul (D P c : ℤ) (K : ℕ) :
    lineCount (2 * D) (2 * P) (2 * c) K = lineCount D P c K := by
  unfold lineCount
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> linarith

/-- With `D` and `P` even, an odd value has no pair on its line. -/
theorem lineCount_two_mul_odd (D P c : ℤ) (K : ℕ) (hc : ¬ 2 ∣ c) :
    lineCount (2 * D) (2 * P) c K = 0 := by
  unfold lineCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  exact hc ⟨D * x.1 - P * x.2, by linarith [hx.2]⟩

/-- The bound at a closing pair, or at the double of a closing pair. -/
theorem lineCount_le_fib_of_double (D P : ℤ)
    (h : Closing D P ∨ (Closing (D / 2) (P / 2) ∧ Even D ∧ Even P)) (c : ℤ) (K : ℕ) :
    lineCount D P c K ≤ Nat.fib (K + 1) := by
  rcases h with h | ⟨h, hD, hP⟩
  · exact lineCount_le_fib D P h c K
  · obtain ⟨D', rfl⟩ : ∃ D', D = 2 * D' := by
      obtain ⟨r, hr⟩ := hD; exact ⟨r, by omega⟩
    obtain ⟨P', rfl⟩ : ∃ P', P = 2 * P' := by
      obtain ⟨r, hr⟩ := hP; exact ⟨r, by omega⟩
    have e1 : 2 * D' / 2 = D' := by omega
    have e2 : 2 * P' / 2 = P' := by omega
    rw [e1, e2] at h
    by_cases hc : 2 ∣ c
    · obtain ⟨c', rfl⟩ := hc
      rw [lineCount_two_mul]
      exact lineCount_le_fib D' P' h c' K
    · rw [lineCount_two_mul_odd D' P' c K hc]
      exact Nat.zero_le _

/-! ## Piece 2: the rays -/

/-- A one of the single seed at cell `x`, step `t`, comes from a pair of naturals with no shared
binary digit, sum `t` and difference `x`. -/
private theorem pair_of_one (t : ℕ) (x : ℤ)
    (h : ((tableRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) x = 1) :
    ∃ a b : ℕ, a + b = t ∧ (a : ℤ) - b = x ∧ a &&& b = 0 := by
  have hodd : 2 ∣ ((t : ℤ) + x) := by
    by_contra hn
    rw [RationalRaySeeds.f90_single_apply_eq_zero_of_odd t x hn] at h
    exact zero_ne_one h
  have hcone : |x| ≤ t := by
    by_contra hn
    rw [RationalRayNinety.f90_single_apply_eq_zero_of_lt t x (by omega)] at h
    exact zero_ne_one h
  rw [abs_le] at hcone
  refine ⟨(((t : ℤ) + x) / 2).toNat, (((t : ℤ) - x) / 2).toNat, ?_, ?_, ?_⟩
  · omega
  · omega
  · have e := RationalRayRate.single_apply_eq_one_iff (((t : ℤ) + x) / 2).toNat
      (((t : ℤ) - x) / 2).toNat
    refine e.1 ?_
    have h1 : (((t : ℤ) + x) / 2).toNat + (((t : ℤ) - x) / 2).toNat = t := by omega
    have h2 : ((((t : ℤ) + x) / 2).toNat : ℤ) - ((((t : ℤ) - x) / 2).toNat : ℤ) = x := by
      omega
    rw [h1, h2]
    exact h

/-- The ray count from a bound on every line of the pair `(q - p, q + p)`. -/
private theorem ray_card_le_of_line (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hline : ∀ (c : ℤ) (K : ℕ), lineCount ((q : ℤ) - p) ((q : ℤ) + p) c K ≤ Nat.fib (K + 1))
    (e : ℤ) (K : ℕ) :
    ((Finset.range (2 ^ K)).filter fun t =>
      observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1).card ≤ q * Nat.fib (K + 1) := by
  have hq : 0 < q := by omega
  set T : Finset (ℕ × ℕ) := (Finset.range q).biUnion fun r : ℕ =>
    (Finset.range (2 ^ K) ×ˢ Finset.range (2 ^ K)).filter fun ab : ℕ × ℕ =>
      ab.1 &&& ab.2 = 0 ∧ ((q : ℤ) - p) * ab.1 - ((q : ℤ) + p) * ab.2 = q * e - r with hT
  have hsub : ((Finset.range (2 ^ K)).filter fun t =>
      observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t = 1)
      ⊆ T.image fun ab => ab.1 + ab.2 := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htK, h1⟩ := ht
    obtain ⟨a, b, hab, hx, hand⟩ := pair_of_one t _ h1
    have hon : RationalRayNinety.OnRay p q e a b := by
      unfold RationalRayNinety.OnRay
      rw [hab]
      exact hx
    rw [RationalRayNinety.onRay_iff p q hq] at hon
    obtain ⟨hlo, hhi⟩ := hon
    simp only [Finset.mem_image, hT, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    refine ⟨(a, b), ⟨(((q : ℤ) + p) * b - ((q : ℤ) - p) * a + q * e).toNat, ?_,
      ⟨by omega, by omega⟩, hand, ?_⟩, hab⟩
    · omega
    · have : ((((q : ℤ) + p) * b - ((q : ℤ) - p) * a + q * e).toNat : ℤ) =
          ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + q * e := Int.toNat_of_nonneg hlo
      rw [this]
      ring
  calc _ ≤ (T.image fun ab => ab.1 + ab.2).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ ≤ ∑ r ∈ Finset.range q, ((Finset.range (2 ^ K) ×ˢ Finset.range (2 ^ K)).filter
        fun ab : ℕ × ℕ => ab.1 &&& ab.2 = 0 ∧
          ((q : ℤ) - p) * ab.1 - ((q : ℤ) + p) * ab.2 = q * e - r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ r ∈ Finset.range q, Nat.fib (K + 1) :=
      Finset.sum_le_sum fun r _ =>
        hline (q * e - r) K
    _ = q * Nat.fib (K + 1) := by simp

/-- **A Fibonacci bound on the ones of a ray of rule `90` from the single seed**
([RuleSpace] §5 Proposition 5.5, the pairs with a one-step proof): a ray of speed `p / q`
from any cell reads at most `q * Nat.fib (K + 1)` ones below step `2 ^ K` when `(q - p, q + p)`
is closing, or is the double of a closing pair. The bound at every speed is
`card_ones_observedRationalRay_f90_single_le_fib`. -/
theorem card_ones_observedRationalRay_f90_single_le (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hcl : Closing ((q : ℤ) - p) ((q : ℤ) + p) ∨
      Closing (((q : ℤ) - p) / 2) (((q : ℤ) + p) / 2) ∧ Even ((q : ℤ) - p))
    (e : ℤ) (K : ℕ) :
    ((Finset.range (2 ^ K)).filter fun t =>
      observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1).card ≤ q * Nat.fib (K + 1) := by
  have hq : 0 < q := by omega
  have hcl' : Closing ((q : ℤ) - p) ((q : ℤ) + p) ∨
      (Closing (((q : ℤ) - p) / 2) (((q : ℤ) + p) / 2) ∧ Even ((q : ℤ) - p) ∧
        Even ((q : ℤ) + p)) := by
    rcases hcl with h | ⟨h, hev⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, hev, ?_⟩
      obtain ⟨r, hr⟩ := hev
      exact ⟨q - r, by omega⟩
  have hq : 0 < q := by omega
  have hcl' : Closing ((q : ℤ) - p) ((q : ℤ) + p) ∨
      (Closing (((q : ℤ) - p) / 2) (((q : ℤ) + p) / 2) ∧ Even ((q : ℤ) - p) ∧
        Even ((q : ℤ) + p)) := by
    rcases hcl with h | ⟨h, hev⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, hev, ?_⟩
      obtain ⟨r, hr⟩ := hev
      exact ⟨q - r, by omega⟩
  exact ray_card_le_of_line p q hp hpq (fun c K => lineCount_le_fib_of_double _ _ hcl' c K) e K

/-- The hypotheses of the ray bound are met at speed `1 / 3`, where `(q - p, q + p) = (2, 4)`
is the double of the closing pair `(1, 2)`. -/
theorem card_ones_observedRationalRay_f90_single_le_nonvacuous :
    0 < 1 ∧ 1 < 3 ∧ Closing (((3 : ℤ) - 1) / 2) (((3 : ℤ) + 1) / 2) ∧
      Even ((3 : ℤ) - 1) := by
  refine ⟨by norm_num, by norm_num, ?_, by decide⟩
  right; right
  exact ⟨by decide, by decide, by decide⟩

/-! ## Piece 3: the bound at every positive pair, from the two-branch count -/

/-- **The two-branch count**: the number of ways to reach `n` in `K` steps from `0`, where a step
from an even value halves it or halves it after subtracting `E`, and a step from an odd value
halves it after subtracting `G`. -/
def repCount (G E : ℤ) : ℕ → ℤ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | K + 1, n =>
      if 2 ∣ n then repCount G E K (n / 2) + repCount G E K ((n - E) / 2)
      else repCount G E K ((n - G) / 2)

/-- **The two-branch bound**: the two-branch count is at most `Nat.fib (K + 1)` at an odd `G`
and a nonzero even `E`. -/
def RepCountBound : Prop :=
  ∀ (G E : ℤ), Odd G → Even E → E ≠ 0 → ∀ (K : ℕ) (n : ℤ),
    repCount G E K n ≤ Nat.fib (K + 1)

/-! ### The two-branch bound -/

/-- One step along the branch that does not use `E`. -/
private def stepT (G n : ℤ) : ℤ := if 2 ∣ n then n / 2 else (n - G) / 2

/-- The parity `r` steps ahead along that branch: `0` when even, `1` when odd. -/
private def win (G : ℤ) (r : ℕ) (n : ℤ) : ℕ := if 2 ∣ (stepT G)^[r] n then 0 else 1

/-- The potential: a product of Fibonacci numbers, one factor for each residue of the number of
steps modulo `m`, lowered by one where the parity ahead is odd. -/
private def pot (G : ℤ) (m K : ℕ) (n : ℤ) : ℕ :=
  ∏ r ∈ Finset.range m, Nat.fib ((K + m - 1 - r) / m + 1 - win G r n)

private theorem stepT_add (G n k : ℤ) : stepT G (n + 2 * k) = stepT G n + k := by
  unfold stepT
  by_cases h : 2 ∣ n
  · have h' : 2 ∣ n + 2 * k := by omega
    simp only [h, h', ↓reduceIte]
    omega
  · have h' : ¬ 2 ∣ n + 2 * k := by omega
    simp only [h, h', ↓reduceIte]
    omega

private theorem iterT_add (G : ℤ) (r : ℕ) (n k : ℤ) :
    (stepT G)^[r] (n + 2 ^ r * k) = (stepT G)^[r] n + k := by
  induction r generalizing n k with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show n + 2 ^ (r + 1) * k = n + 2 * (2 ^ r * k) by ring, stepT_add, ih]

private theorem win_succ (G : ℤ) (r : ℕ) (n : ℤ) : win G (r + 1) n = win G r (stepT G n) := by
  unfold win
  rw [Function.iterate_succ_apply]

private theorem win_le (G : ℤ) (r : ℕ) (n : ℤ) : win G r n ≤ 1 := by
  unfold win
  split_ifs <;> omega

private theorem stepT_zero (G : ℤ) : stepT G 0 = 0 := by
  simp [stepT]

private theorem iterT_zero (G : ℤ) (r : ℕ) : (stepT G)^[r] 0 = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, stepT_zero, ih]

private theorem win_zero_arg (G : ℤ) (r : ℕ) : win G r 0 = 0 := by
  simp [win, iterT_zero]

/-- The two ends of a branching step agree, `r` steps ahead, up to a power of two times `e`. -/
private theorem iterT_split (G e : ℤ) (m' r : ℕ) (hr : r ≤ m') (x : ℤ) :
    (stepT G)^[r] x = (stepT G)^[r] (x - 2 ^ m' * e) + 2 ^ (m' - r) * e := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h := iterT_add G r (x - 2 ^ (r + d) * e) (2 ^ d * e)
  have h2 : x - 2 ^ (r + d) * e + 2 ^ r * (2 ^ d * e) = x := by
    rw [pow_add]; ring
  rw [h2] at h
  rw [h]
  simp

private theorem child_eq (m' : ℕ) (e n : ℤ) (hn : 2 ∣ n) :
    (n - 2 ^ (m' + 1) * e) / 2 = n / 2 - 2 ^ m' * e := by
  have : 2 ^ (m' + 1) * e = 2 * (2 ^ m' * e) := by ring
  rw [this]
  generalize 2 ^ m' * e = Q
  omega

private theorem win_eq_of_lt (G e : ℤ) (m' r : ℕ) (hr : r < m') (n : ℤ) (hn : 2 ∣ n) :
    win G r (n / 2) = win G r ((n - 2 ^ (m' + 1) * e) / 2) := by
  rw [child_eq m' e n hn]
  unfold win
  rw [iterT_split G e m' r hr.le (n / 2)]
  have : 2 ∣ (2 : ℤ) ^ (m' - r) * e := by
    obtain ⟨d, hd⟩ : ∃ d, m' - r = d + 1 := ⟨m' - r - 1, by omega⟩
    rw [hd, pow_succ]
    exact ⟨2 ^ d * e, by ring⟩
  generalize (stepT G)^[r] (n / 2 - 2 ^ m' * e) = a at this ⊢
  generalize (2 : ℤ) ^ (m' - r) * e = b at this ⊢
  by_cases h : 2 ∣ a
  · have : 2 ∣ a + b := by omega
    simp [h, this]
  · have : ¬ 2 ∣ a + b := by omega
    simp [h, this]

private theorem win_last (G e : ℤ) (he : Odd e) (m' : ℕ) (n : ℤ) (hn : 2 ∣ n) :
    (win G m' (n / 2) = 0 ∧ win G m' ((n - 2 ^ (m' + 1) * e) / 2) = 1) ∨
      (win G m' (n / 2) = 1 ∧ win G m' ((n - 2 ^ (m' + 1) * e) / 2) = 0) := by
  rw [child_eq m' e n hn]
  unfold win
  rw [iterT_split G e m' m' le_rfl (n / 2)]
  simp only [Nat.sub_self, pow_zero, one_mul]
  have he' : e % 2 = 1 := Int.odd_iff.1 he
  generalize (stepT G)^[m'] (n / 2 - 2 ^ m' * e) = a
  by_cases h : 2 ∣ a
  · have : ¬ 2 ∣ a + e := by omega
    simp [h, this]
  · have : 2 ∣ a + e := by omega
    simp [h, this]

private theorem pot_peel_first (G : ℤ) (m' K : ℕ) (n : ℤ) :
    pot G (m' + 1) (K + 1) n =
      (∏ r ∈ Finset.range m',
        Nat.fib ((K + m' - r) / (m' + 1) + 1 - win G r (stepT G n))) *
      Nat.fib (K / (m' + 1) + 1 + 1 - win G 0 n) := by
  unfold pot
  rw [Finset.prod_range_succ']
  congr 1
  · apply Finset.prod_congr rfl
    intro r hr
    rw [win_succ]
    have : K + 1 + (m' + 1) - 1 - (r + 1) = K + m' - r := by omega
    rw [this]
  · have : K + 1 + (m' + 1) - 1 - 0 = K + (m' + 1) := by omega
    rw [this, Nat.add_div_right _ (by omega)]

private theorem pot_peel_last (G : ℤ) (m' K : ℕ) (n : ℤ) :
    pot G (m' + 1) K n =
      (∏ r ∈ Finset.range m',
        Nat.fib ((K + m' - r) / (m' + 1) + 1 - win G r n)) *
      Nat.fib (K / (m' + 1) + 1 - win G m' n) := by
  unfold pot
  rw [Finset.prod_range_succ]
  have h1 : ∀ r ∈ Finset.range m', Nat.fib ((K + (m' + 1) - 1 - r) / (m' + 1) + 1 - win G r n) =
      Nat.fib ((K + m' - r) / (m' + 1) + 1 - win G r n) := by
    intro r _
    have : K + (m' + 1) - 1 - r = K + m' - r := by omega
    rw [this]
  rw [Finset.prod_congr rfl h1, show K + (m' + 1) - 1 - m' = K by omega]

private theorem repCount_le_pot (G e : ℤ) (he : Odd e) (m' : ℕ) :
    ∀ (K : ℕ) (n : ℤ), repCount G (2 ^ (m' + 1) * e) K n ≤ pot G (m' + 1) K n := by
  intro K
  induction K with
  | zero =>
    intro n
    unfold pot
    have h1 : ∀ r ∈ Finset.range (m' + 1),
        Nat.fib ((0 + (m' + 1) - 1 - r) / (m' + 1) + 1 - win G r n) =
          Nat.fib (1 - win G r n) := by
      intro r hr
      rw [Finset.mem_range] at hr
      have : (0 + (m' + 1) - 1 - r) / (m' + 1) = 0 := Nat.div_eq_of_lt (by omega)
      rw [this]
    rw [Finset.prod_congr rfl h1]
    by_cases hn : n = 0
    · subst hn
      simp [repCount, win_zero_arg]
    · simp [repCount, hn]
  | succ K ih =>
    intro n
    rw [pot_peel_first, repCount]
    by_cases hn : 2 ∣ n
    · simp only [hn, ↓reduceIte]
      have hw0 : win G 0 n = 0 := by simp [win, hn]
      have hs : stepT G n = n / 2 := by simp [stepT, hn]
      have i1 := ih (n / 2)
      have i2 := ih ((n - 2 ^ (m' + 1) * e) / 2)
      rw [pot_peel_last] at i1 i2
      have eq2 : (∏ r ∈ Finset.range m',
          Nat.fib ((K + m' - r) / (m' + 1) + 1 - win G r ((n - 2 ^ (m' + 1) * e) / 2))) =
          ∏ r ∈ Finset.range m',
          Nat.fib ((K + m' - r) / (m' + 1) + 1 - win G r (n / 2)) := by
        apply Finset.prod_congr rfl
        intro r hr
        rw [Finset.mem_range] at hr
        rw [win_eq_of_lt G e m' r hr n hn]
      rw [eq2] at i2
      rw [hs]
      set Q := ∏ r ∈ Finset.range m',
          Nat.fib ((K + m' - r) / (m' + 1) + 1 - win G r (n / 2)) with hQ
      have key : Nat.fib (K / (m' + 1) + 1 - win G m' (n / 2)) +
          Nat.fib (K / (m' + 1) + 1 - win G m' ((n - 2 ^ (m' + 1) * e) / 2)) =
          Nat.fib (K / (m' + 1) + 1 + 1 - win G 0 n) := by
        rw [hw0]
        rcases win_last G e he m' n hn with ⟨a, b⟩ | ⟨a, b⟩
        · rw [a, b]
          simp only [Nat.add_sub_cancel, Nat.sub_zero]
          rw [Nat.fib_add_two]
          omega
        · rw [a, b]
          simp only [Nat.add_sub_cancel, Nat.sub_zero]
          rw [Nat.fib_add_two]
      calc _ ≤ _ + _ := Nat.add_le_add i1 i2
        _ = Q * (Nat.fib (K / (m' + 1) + 1 - win G m' (n / 2)) +
            Nat.fib (K / (m' + 1) + 1 - win G m' ((n - 2 ^ (m' + 1) * e) / 2))) := by
          ring
        _ = _ := by rw [key]
    · simp only [hn, ↓reduceIte]
      have hw0 : win G 0 n = 1 := by simp [win, hn]
      have hs : stepT G n = (n - G) / 2 := by simp [stepT, hn]
      have i1 := ih ((n - G) / 2)
      rw [pot_peel_last, ← hs] at i1
      rw [← hs, hw0]
      refine le_trans i1 (Nat.mul_le_mul_left _ ?_)
      apply Nat.fib_mono
      omega

/-- The potential is at most `Nat.fib (K + 1)`. -/
private theorem fib_prod_le (s : Finset ℕ) (c : ℕ → ℕ) :
    ∏ r ∈ s, Nat.fib (c r + 1) ≤ Nat.fib (∑ r ∈ s, c r + 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    calc _ ≤ Nat.fib (c a + 1) * Nat.fib (∑ r ∈ s, c r + 1) := Nat.mul_le_mul_left _ ih
      _ ≤ Nat.fib (c a + ∑ r ∈ s, c r + 1) := by
        rw [Nat.fib_add]
        exact Nat.le_add_left _ _

private theorem sum_div_eq (m' K : ℕ) :
    ∑ r ∈ Finset.range (m' + 1), (K + (m' + 1) - 1 - r) / (m' + 1) = K := by
  induction K with
  | zero =>
    apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.mem_range] at hr
    exact Nat.div_eq_of_lt (by omega)
  | succ K ih =>
    rw [Finset.sum_range_succ] at ih
    rw [Finset.sum_range_succ']
    have h1 : ∀ r ∈ Finset.range m', (K + 1 + (m' + 1) - 1 - (r + 1)) / (m' + 1) =
        (K + (m' + 1) - 1 - r) / (m' + 1) := by
      intro r _
      have : K + 1 + (m' + 1) - 1 - (r + 1) = K + (m' + 1) - 1 - r := by omega
      rw [this]
    rw [Finset.sum_congr rfl h1]
    have h2 : K + 1 + (m' + 1) - 1 - 0 = K + (m' + 1) := by omega
    have h3 : K + (m' + 1) - 1 - m' = K := by omega
    rw [h3] at ih
    rw [h2, Nat.add_div_right _ (by omega)]
    omega

private theorem pot_le_fib (G : ℤ) (m' K : ℕ) (n : ℤ) :
    pot G (m' + 1) K n ≤ Nat.fib (K + 1) := by
  calc pot G (m' + 1) K n
      ≤ ∏ r ∈ Finset.range (m' + 1), Nat.fib ((K + (m' + 1) - 1 - r) / (m' + 1) + 1) := by
        apply Finset.prod_le_prod
        intro r _
        exact Nat.fib_mono (Nat.sub_le _ _)
    _ ≤ Nat.fib (∑ r ∈ Finset.range (m' + 1), (K + (m' + 1) - 1 - r) / (m' + 1) + 1) :=
        fib_prod_le _ _
    _ = Nat.fib (K + 1) := by rw [sum_div_eq]

/-- **The two-branch bound holds**: the two-branch count is at most `Nat.fib (K + 1)` at an odd
`G` and a nonzero even `E` ([RuleSpace] §5 Proposition 5.5). -/
theorem repCountBound : RepCountBound := by
  intro G E _ hE hE0 K n
  obtain ⟨k, m, hm, hEk⟩ := Nat.exists_eq_two_pow_mul_odd (n := E.natAbs)
    (by omega)
  obtain ⟨e, he, hEe⟩ : ∃ e : ℤ, Odd e ∧ E = 2 ^ k * e := by
    rcases Int.natAbs_eq E with h | h
    · refine ⟨m, by exact_mod_cast hm, ?_⟩
      rw [h, hEk]; push_cast; ring
    · refine ⟨-m, (by exact_mod_cast hm : Odd (m : ℤ)).neg, ?_⟩
      rw [h, hEk]; push_cast; ring
  have hk : k ≠ 0 := by
    rintro rfl
    have : Odd E := by simpa [hEe] using he
    exact (Int.not_even_iff_odd.2 this) hE
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [hEe]
  exact (repCount_le_pot G e he m' K n).trans (pot_le_fib G m' K n)

/-- With `D` even and `P` odd, the line count is the two-branch count at `(-P, D)`. -/
theorem lineCount_eq_repCount_of_even_odd (D P : ℤ) (hD : Even D) (hP : Odd P) (c : ℤ) (K : ℕ) :
    lineCount D P c K = repCount (-P) D K c := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨p, hp⟩ := hP
  induction K generalizing c with
  | zero => simp [lineCount_zero, repCount]
  | succ K ih =>
    rw [lineCount_succ, repCount]
    by_cases hc : 2 ∣ c
    · have h1 : 2 ∣ c - D := by omega
      have h2 : ¬ 2 ∣ c + P := by omega
      simp only [hc, h1, h2, ↓reduceIte, add_zero]
      rw [ih, ih]
    · have h1 : ¬ 2 ∣ c - D := by omega
      have h2 : 2 ∣ c + P := by omega
      simp only [hc, h1, h2, ↓reduceIte, zero_add]
      rw [ih, sub_neg_eq_add]

/-- With `D` odd and `P` even, the line count is the two-branch count at `(D, -P)`. -/
theorem lineCount_eq_repCount_of_odd_even (D P : ℤ) (hD : Odd D) (hP : Even P) (c : ℤ) (K : ℕ) :
    lineCount D P c K = repCount D (-P) K c := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨p, hp⟩ := hP
  induction K generalizing c with
  | zero => simp [lineCount_zero, repCount]
  | succ K ih =>
    rw [lineCount_succ, repCount]
    by_cases hc : 2 ∣ c
    · have h1 : ¬ 2 ∣ c - D := by omega
      have h2 : 2 ∣ c + P := by omega
      simp only [hc, h1, h2, ↓reduceIte, add_zero]
      rw [ih, ih, sub_neg_eq_add]
    · have h1 : 2 ∣ c - D := by omega
      have h2 : ¬ 2 ∣ c + P := by omega
      simp only [hc, h1, h2, ↓reduceIte, zero_add, add_zero]
      rw [ih]

/-- With `D` and `P` both odd, the line count is the two-branch count at `(P, D + P)`, at the
value shifted by `P * (2 ^ K - 1)`. -/
theorem lineCount_eq_repCount_of_odd_odd (D P : ℤ) (hD : Odd D) (hP : Odd P) (c : ℤ) (K : ℕ) :
    lineCount D P c K = repCount P (D + P) K (c + P * (2 ^ K - 1)) := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨p, hp⟩ := hP
  induction K generalizing c with
  | zero => simp [lineCount_zero, repCount]
  | succ K ih =>
    rw [lineCount_succ, repCount]
    have e1 : (c + P * (2 ^ (K + 1) - 1)) = c + P * (2 ^ K - 1) + P * 2 ^ K := by ring
    have e2 : P * (2 ^ K - 1) = P * 2 ^ K - P := by ring
    generalize P * 2 ^ K = Q at e1 e2 ⊢
    by_cases hc : 2 ∣ c
    · have h1 : ¬ 2 ∣ c - D := by omega
      have h2 : ¬ 2 ∣ c + P := by omega
      have hn : ¬ 2 ∣ c + P * (2 ^ (K + 1) - 1) := by omega
      simp only [hc, h1, h2, hn, ↓reduceIte, add_zero]
      rw [ih]
      congr 1
      omega
    · have h1 : 2 ∣ c - D := by omega
      have h2 : 2 ∣ c + P := by omega
      have hn : 2 ∣ c + P * (2 ^ (K + 1) - 1) := by omega
      simp only [hc, h1, h2, hn, ↓reduceIte, zero_add]
      rw [ih, ih, add_comm]
      congr 2 <;> omega

/-- **The Fibonacci bound on a line at every pair of positive integers**
([RuleSpace] §5 Proposition 5.5): `lineCount D P c K ≤ Nat.fib (K + 1)` for all `c` and `K`,
whenever `0 < D` and `0 < P`. -/
theorem lineCount_le_fib_of_pos (D P : ℤ) (hD : 0 < D) (hP : 0 < P)
    (c : ℤ) (K : ℕ) : lineCount D P c K ≤ Nat.fib (K + 1) := by
  obtain ⟨n, hn⟩ : ∃ n, D.natAbs = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing D P c with | _ n ih
  rcases Int.even_or_odd D with hDe | hDo <;> rcases Int.even_or_odd P with hPe | hPo
  · obtain ⟨D', rfl⟩ : ∃ D', D = 2 * D' := by
      obtain ⟨r, hr⟩ := hDe; exact ⟨r, by omega⟩
    obtain ⟨P', rfl⟩ : ∃ P', P = 2 * P' := by
      obtain ⟨r, hr⟩ := hPe; exact ⟨r, by omega⟩
    by_cases hc : 2 ∣ c
    · obtain ⟨c', rfl⟩ := hc
      rw [lineCount_two_mul]
      exact ih D'.natAbs (by omega) D' P' (by omega) (by omega) c' rfl
    · rw [lineCount_two_mul_odd D' P' c K hc]
      exact Nat.zero_le _
  · rw [lineCount_eq_repCount_of_even_odd D P hDe hPo]
    exact repCountBound (-P) D hPo.neg hDe (by omega) K c
  · rw [lineCount_eq_repCount_of_odd_even D P hDo hPe]
    exact repCountBound D (-P) hDo hPe.neg (by omega) K c
  · rw [lineCount_eq_repCount_of_odd_odd D P hDo hPo]
    exact repCountBound P (D + P) hPo (hDo.add_odd hPo) (by omega) K _

/-- **The Fibonacci bound on the ones of a ray of rule `90` from the single seed at every speed
below `1`** ([RuleSpace] §5 Proposition 5.5): a ray of speed `p / q` from any cell reads at most
`q * Nat.fib (K + 1)` ones below step `2 ^ K`. -/
theorem card_ones_observedRationalRay_f90_single_le_fib (p q : ℕ)
    (hp : 0 < p) (hpq : p < q) (e : ℤ) (K : ℕ) :
    ((Finset.range (2 ^ K)).filter fun t =>
      observedRationalRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1).card ≤ q * Nat.fib (K + 1) :=
  ray_card_le_of_line p q hp hpq
    (fun c K => lineCount_le_fib_of_pos _ _ (by omega) (by omega) c K) e K

/-- The hypotheses of the two-branch bound hold together at `G = 1`, `E = 2`, where the bound is
attained at `K = 3` and `n = 4`. -/
theorem repCountBound_nonvacuous :
    Odd (1 : ℤ) ∧ Even (2 : ℤ) ∧ (2 : ℤ) ≠ 0 ∧ repCount 1 2 3 4 = Nat.fib (3 + 1) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The hypotheses of the line bound hold together at `(2, 1)`, where the bound is attained at
`K = 3`: the pairs are `(0, 0)`, `(1, 2)` and `(2, 4)`. -/
theorem lineCount_le_fib_of_pos_nonvacuous :
    0 < (2 : ℤ) ∧ 0 < (1 : ℤ) ∧ lineCount 2 1 0 3 = Nat.fib (3 + 1) :=
  ⟨by norm_num, by norm_num, by decide⟩

/-- Positivity is load-bearing: on the line `a + b = 1` the pairs `(0, 1)` and `(1, 0)` both lie
below `2`, so the count is `2` while `Nat.fib 2 = 1`. -/
theorem lineCount_not_le_fib_of_neg : Nat.fib (1 + 1) < lineCount 1 (-1) 1 1 := by
  decide

end RationalRayBound

/-- info: 'RationalRayBound.lineCount_le_fib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.lineCount_le_fib

/-- info: 'RationalRayBound.lineCount_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.lineCount_two_mul

/-- info: 'RationalRayBound.card_ones_observedRationalRay_f90_single_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.card_ones_observedRationalRay_f90_single_le

/-- info: 'RationalRayBound.card_ones_observedRationalRay_f90_single_le_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.card_ones_observedRationalRay_f90_single_le_nonvacuous

/-- info: 'RationalRayBound.repCountBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.repCountBound

/-- info: 'RationalRayBound.lineCount_le_fib_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.lineCount_le_fib_of_pos

/-- info: 'RationalRayBound.card_ones_observedRationalRay_f90_single_le_fib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.card_ones_observedRationalRay_f90_single_le_fib

/-- info: 'RationalRayBound.lineCount_not_le_fib_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.lineCount_not_le_fib_of_neg

/-- info: 'RationalRayBound.lineCount_le_fib_of_pos_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.lineCount_le_fib_of_pos_nonvacuous

/-- info: 'RationalRayBound.repCountBound_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RationalRayBound.repCountBound_nonvacuous
