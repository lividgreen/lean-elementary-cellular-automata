module

public import ECA.RationalRayMax
import all ECA.RationalRayBound
import all ECA.RationalRayRate
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# The ones of rule `90` rays at the speeds `1 - 2 ^ (-m)` are polynomially many
([RuleSpace] §5)

[RuleSpace] §5 Proposition 5.16 shows that at the speeds `(2 ^ m - 1) / (2 ^ m + 1)` the ray of
rule `90` from the single seed reads `Nat.fib (L + 2)` ones below step `(2 ^ m + 1) * 2 ^ L`,
matching the Fibonacci ceiling of Proposition 5.5. This file shows that the exponent of the ones
at the speeds `(2 ^ m - 1) / 2 ^ m`, `1 ≤ m`, is zero: the ray reads at most
`2 ^ m * (K + 1) ^ (m + 1)` ones below step `2 ^ K`.

A one at step `t` and cell `x` comes from a pair `(a, b)` of naturals with no shared binary
digit, `a + b = t` and `a - b = x`. At this speed the pair lies on a line
`a + b + r = 2 ^ (m + 1) * b` with `r < 2 ^ m`. Then `b = 0`, or `b` has a least set bit `z`, the
bit `z + (m + 1)` is clear, and every set bit above that one has the bit `m + 1` below it set:
the set bits other than `z` form chains descending by `m + 1`, each an initial segment of its
residue class. The position `z` and the `m` chain lengths determine `b`, and so the pair.

## Main results

* `card_ones_observedRationalRay_f90_single_zeroSpeed_le` — below step `2 ^ K` the ray of speed
  `(2 ^ m - 1) / 2 ^ m` from cell `0` reads at most `2 ^ m * (K + 1) ^ (m + 1)` ones.
* `card_ones_observedRationalRay_f90_single_zeroSpeed_le_guard` — the speed is load-bearing: at
  the speed `1 / 3`, the case `m = 1` of Proposition 5.16, the ones below step `2 ^ 18` outnumber
  the polynomial bound of the case `m = 1`.
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## Bit lemmas -/

/-- If `a` and `b` share no binary digit, every binary digit of `b` is one of `a + b`. -/
private theorem testBit_add_of_and_eq_zero (j : ℕ) :
    ∀ a b : ℕ, a &&& b = 0 → b.testBit j = true → (a + b).testBit j = true := by
  induction j with
  | zero =>
    intro a b h hb
    rw [and_eq_zero_iff_div] at h
    rw [Nat.testBit_zero] at hb ⊢
    simp only [decide_eq_true_eq] at hb ⊢
    omega
  | succ j ih =>
    intro a b h hb
    rw [and_eq_zero_iff_div] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.testBit_succ] at hb ⊢
    have e : (a + b) / 2 = a / 2 + b / 2 := by omega
    rw [e]
    exact ih _ _ h2 hb

/-- The binary digits of `b - 1`, for `b` with least set bit `z`. -/
private theorem testBit_pred (z : ℕ) : ∀ b : ℕ, (∀ i < z, ¬ b.testBit i) → b.testBit z → ∀ i,
    (b - 1).testBit i =
      if i < z then true else if i = z then false else b.testBit i := by
  induction z with
  | zero =>
    intro b _ hz i
    rw [Nat.testBit_zero] at hz
    simp only [decide_eq_true_eq] at hz
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      simp only [Nat.not_lt_zero, ↓reduceIte, decide_eq_false_iff_not]
      omega
    | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      have e : (b - 1) / 2 = b / 2 := by omega
      rw [e]
      simp
  | succ z ih =>
    intro b hlow hz i
    have h0 : ¬ b.testBit 0 := hlow 0 (by omega)
    rw [Nat.testBit_zero] at h0
    simp only [decide_eq_true_eq] at h0
    have hlow' : ∀ i < z, ¬ (b / 2).testBit i := fun i hi => by
      rw [← Nat.testBit_succ]
      exact hlow (i + 1) (by omega)
    have hz' : (b / 2).testBit z := by
      rw [← Nat.testBit_succ]
      exact hz
    have hpos : 0 < b / 2 := by
      rcases Nat.eq_zero_or_pos (b / 2) with h | h
      · rw [h] at hz'
        simp at hz'
      · exact h
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      simp only [Nat.zero_lt_succ, ↓reduceIte, decide_eq_true_eq]
      omega
    | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      have e : (b - 1) / 2 = b / 2 - 1 := by omega
      rw [e, ih (b / 2) hlow' hz' i]
      by_cases h1 : i < z
      · simp [h1]
      · by_cases h2 : i = z
        · simp [h2]
        · have h3 : ¬ i + 1 < z + 1 := by omega
          simp [h1, h2, h3]

/-! ## The shape of the set bits -/

/-- **The shape**: `z` is the least set bit of `b`, the bit `z + (m + 1)` is clear, and every set
bit above that one has the bit `m + 1` below it set. -/
private def ZeroShape (m z b : ℕ) : Prop :=
  (∀ i < z, ¬ b.testBit i) ∧ b.testBit z = true ∧ ¬ b.testBit (z + (m + 1)) ∧
    ∀ j, z + (m + 1) < j → b.testBit j = true → b.testBit (j - (m + 1)) = true

/-- A pair with no shared digit on a line `a + b + r = 2 ^ (m + 1) * b`, `r < 2 ^ (m + 1)`, has
`b = 0` or `b` of the shape. -/
private theorem zeroShape_of_line (m r a b : ℕ) (hr : r < 2 ^ (m + 1)) (hb : 0 < b)
    (hab : a &&& b = 0) (hl : a + b + r = 2 ^ (m + 1) * b) : ∃ z, ZeroShape m z b := by
  have hex : ∃ j, b.testBit j = true := by
    refine ⟨b.log2, ?_⟩
    exact Nat.testBit_log2 (by omega)
  classical
  set z := Nat.find hex with hzdef
  have hz : b.testBit z = true := Nat.find_spec hex
  have hlow : ∀ i < z, ¬ b.testBit i = true := fun i hi => Nat.find_min hex hi
  have hsub : ∀ j, b.testBit j = true → (a + b).testBit j = true := fun j hj =>
    testBit_add_of_and_eq_zero j a b hab hj
  have hP : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · exfalso
    subst hr0
    have h1 := hsub z hz
    have e : a + b = 2 ^ (m + 1) * b := by omega
    rw [e, Nat.testBit_two_pow_mul] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact hlow (z - (m + 1)) (by omega) h1.2
  · obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
    have ht : a + (d + 1) = 2 ^ (m + 1) * d + (2 ^ (m + 1) - r) := by
      rw [Nat.mul_add, Nat.mul_one] at hl
      omega
    have hdiv : (a + (d + 1)) / 2 ^ (m + 1) = d := by
      rw [ht, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega)]
      rfl
    have star : ∀ i, (d + 1).testBit (i + (m + 1)) = true → d.testBit i = true := by
      intro i hi
      have := hsub _ hi
      rw [← Nat.testBit_div_two_pow, hdiv] at this
      exact this
    have hpred := testBit_pred z (d + 1) hlow hz
    simp only [Nat.add_sub_cancel] at hpred
    refine ⟨z, hlow, hz, ?_, ?_⟩
    · intro hc
      have := star z hc
      rw [hpred z] at this
      simp at this
    · intro j hj hbit
      obtain ⟨i, rfl⟩ : ∃ i, j = i + (m + 1) := ⟨j - (m + 1), by omega⟩
      have := star i hbit
      have h1 : ¬ i < z := by omega
      have h2 : ¬ i = z := by omega
      rw [hpred i] at this
      simp only [h1, h2, ↓reduceIte] at this
      rw [Nat.add_sub_cancel]
      exact this

/-! ## The chain lengths -/

private theorem exists_not_testBit (m b z u : ℕ) :
    ∃ k, ¬ b.testBit (z + u + k * (m + 1)) = true := by
  refine ⟨b, ?_⟩
  have h : b < 2 ^ (z + u + b * (m + 1)) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  rw [Nat.testBit_eq_false_of_lt h]
  simp

/-- The length of the chain of set bits `z + u`, `z + u + (m + 1)`, `z + u + 2 (m + 1)`, … of
`b`: the first index at which the chain stops. -/
private noncomputable def chainLen (m b z u : ℕ) : ℕ :=
  @Nat.find (fun k => ¬ b.testBit (z + u + k * (m + 1)) = true)
    (Classical.decPred _) (exists_not_testBit m b z u)

private theorem chainLen_spec (m b z u : ℕ) :
    ¬ b.testBit (z + u + chainLen m b z u * (m + 1)) = true :=
  @Nat.find_spec (fun k => ¬ b.testBit (z + u + k * (m + 1)) = true)
    (Classical.decPred _) (exists_not_testBit m b z u)

private theorem chainLen_min (m b z u k : ℕ) (hk : k < chainLen m b z u) :
    b.testBit (z + u + k * (m + 1)) = true := by
  have := @Nat.find_min (fun k => ¬ b.testBit (z + u + k * (m + 1)) = true)
    (Classical.decPred _) (exists_not_testBit m b z u) k hk
  simpa using this

private theorem chainLen_le (m b z u K : ℕ) (h : b < 2 ^ K) : chainLen m b z u ≤ K := by
  have h1 : ¬ b.testBit (z + u + K * (m + 1)) = true := by
    have : b < 2 ^ (z + u + K * (m + 1)) :=
      lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    rw [Nat.testBit_eq_false_of_lt this]
    simp
  exact @Nat.find_min' (fun k => ¬ b.testBit (z + u + k * (m + 1)) = true)
    (Classical.decPred _) (exists_not_testBit m b z u) K h1

private theorem chainLen_iff (m z b u : ℕ) (hu : 1 ≤ u) (h : ZeroShape m z b) (k : ℕ) :
    b.testBit (z + u + k * (m + 1)) = true ↔ k < chainLen m b z u := by
  obtain ⟨_, _, _, h3⟩ := h
  have hspec := chainLen_spec m b z u
  have hmin := chainLen_min m b z u
  have hdown : ∀ d k, b.testBit (z + u + (k + d) * (m + 1)) = true →
      b.testBit (z + u + k * (m + 1)) = true := by
    intro d
    induction d with
    | zero => intro k hk; simpa using hk
    | succ d ih =>
      intro k hk
      apply ih
      have h1 := h3 (z + u + (k + (d + 1)) * (m + 1)) (by nlinarith) hk
      rw [show z + u + (k + (d + 1)) * (m + 1) - (m + 1) = z + u + (k + d) * (m + 1) by
        rw [show k + (d + 1) = (k + d) + 1 by ring, Nat.succ_mul]; omega] at h1
      exact h1
  constructor
  · intro hk
    by_contra hlt
    push Not at hlt
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlt
    rw [hd] at hk
    exact hspec (hdown d _ hk)
  · exact hmin k

private theorem not_testBit_zero_class (m z b : ℕ) (h : ZeroShape m z b) :
    ∀ k, 1 ≤ k → ¬ b.testBit (z + k * (m + 1)) = true := by
  obtain ⟨_, _, h2, h3⟩ := h
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using h2
  | succ k hk ih =>
    intro hc
    apply ih
    have := h3 (z + (k + 1) * (m + 1)) (by nlinarith) hc
    rw [show z + (k + 1) * (m + 1) - (m + 1) = z + k * (m + 1) by
      rw [Nat.succ_mul]; omega] at this
    exact this

private theorem eq_of_zeroShape (m z b b' : ℕ) (h : ZeroShape m z b) (h' : ZeroShape m z b')
    (hlen : ∀ u, 1 ≤ u → u ≤ m → chainLen m b z u = chainLen m b' z u) : b = b' := by
  apply Nat.eq_of_testBit_eq
  intro j
  rcases lt_trichotomy j z with hj | hj | hj
  · rw [Bool.eq_false_iff.mpr (h.1 j hj), Bool.eq_false_iff.mpr (h'.1 j hj)]
  · rw [hj, h.2.1, h'.2.1]
  · obtain ⟨u, k, hjk, hlt⟩ : ∃ u k, j = z + u + k * (m + 1) ∧ u < m + 1 := by
      refine ⟨(j - z) % (m + 1), (j - z) / (m + 1), ?_, Nat.mod_lt _ (Nat.succ_pos _)⟩
      have hmod := Nat.mod_add_div (j - z) (m + 1)
      rw [Nat.mul_comm ((j - z) / (m + 1))]
      omega
    by_cases hu0 : u = 0
    · have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · exfalso
          rw [hu0, h0] at hjk
          omega
        · exact h0
      have hj' : j = z + k * (m + 1) := by rw [hjk, hu0]; ring
      rw [hj', Bool.eq_false_iff.mpr (not_testBit_zero_class m z b h k hk1),
        Bool.eq_false_iff.mpr (not_testBit_zero_class m z b' h' k hk1)]
    · have hu1 : 1 ≤ u := by omega
      rw [hjk, Bool.eq_iff_iff, chainLen_iff m z b u hu1 h k, chainLen_iff m z b' u hu1 h' k,
        hlen u hu1 (by omega)]

/-! ## The count -/

private theorem lt_of_zeroShape (m z b K : ℕ) (h : ZeroShape m z b) (hb : b < 2 ^ K) : z < K := by
  by_contra hc
  push Not at hc
  have : b < 2 ^ z := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hc)
  have h1 := h.2.1
  rw [Nat.testBit_eq_false_of_lt this] at h1
  simp at h1

/-- The pairs with no shared binary digit below `2 ^ K` on the line
`a + b + r = 2 ^ (m + 1) * b`, `r < 2 ^ (m + 1)`, number at most `(K + 1) ^ (m + 1)`. -/
private theorem card_line_le (m K r : ℕ) (hr : r < 2 ^ (m + 1)) :
    ((Finset.range (2 ^ K) ×ˢ Finset.range (2 ^ K)).filter fun ab : ℕ × ℕ =>
      ab.1 &&& ab.2 = 0 ∧ ab.1 + ab.2 + r = 2 ^ (m + 1) * ab.2).card ≤ (K + 1) ^ (m + 1) := by
  set Q := (Finset.range (2 ^ K) ×ˢ Finset.range (2 ^ K)).filter fun ab : ℕ × ℕ =>
      ab.1 &&& ab.2 = 0 ∧ ab.1 + ab.2 + r = 2 ^ (m + 1) * ab.2 with hQ
  have hsub : Q ⊆ insert (0, 0) (Q.filter fun ab => 0 < ab.2) := by
    intro p hp
    by_cases h0 : p.2 = 0
    · have hl := (Finset.mem_filter.mp hp).2.2
      rw [h0] at hl
      refine Finset.mem_insert.mpr (Or.inl ?_)
      ext
      · simp only
        omega
      · simpa using h0
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, Nat.pos_of_ne_zero h0⟩)
  have hT : (Q.filter fun ab => 0 < ab.2).card ≤
      ((Finset.range K) ×ˢ Fintype.piFinset (fun _ : Fin m => Finset.range (K + 1))).card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun (p : ℕ × ℕ) (c : ℕ × (Fin m → ℕ)) =>
        ZeroShape m c.1 p.2 ∧ ∀ i : Fin m, chainLen m p.2 c.1 (i + 1) = c.2 i) ?_ ?_
    · intro p hp
      obtain ⟨hpQ, hpos⟩ := Finset.mem_filter.mp hp
      have hmem := Finset.mem_filter.mp hpQ
      have hb : p.2 < 2 ^ K := Finset.mem_range.mp (Finset.mem_product.mp hmem.1).2
      obtain ⟨z, hz⟩ := zeroShape_of_line m r p.1 p.2 hr hpos hmem.2.1 hmem.2.2
      refine ⟨(z, fun i => chainLen m p.2 z (i + 1)), ?_, hz, fun i => rfl⟩
      simp only [Finset.mem_product, Finset.mem_range, Fintype.mem_piFinset]
      exact ⟨lt_of_zeroShape m z p.2 K hz hb, fun i =>
        Nat.lt_succ_of_le (chainLen_le m p.2 z _ K hb)⟩
    · intro c _ p hp p' hp'
      have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
      have hmem' := Finset.mem_filter.mp (Finset.mem_filter.mp hp'.1).1
      have hb : p.2 = p'.2 := by
        refine eq_of_zeroShape m c.1 p.2 p'.2 hp.2.1 hp'.2.1 fun u hu hum => ?_
        obtain ⟨i, rfl⟩ : ∃ i : Fin m, u = i + 1 := ⟨⟨u - 1, by omega⟩, by simp; omega⟩
        rw [hp.2.2 i, hp'.2.2 i]
      refine Prod.ext ?_ hb
      have h1 := hmem.2.2
      have h2 := hmem'.2.2
      rw [hb] at h1
      omega
  have hc := Finset.card_le_card hsub
  have hc2 := Finset.card_insert_le (0, 0) (Q.filter fun ab => 0 < ab.2)
  rw [Finset.card_product, Fintype.card_piFinset] at hT
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hT
  have hX : 1 ≤ (K + 1) ^ m := Nat.one_le_pow _ _ (Nat.succ_pos K)
  rw [pow_succ]
  nlinarith

/-! ## The bound and its guard -/

/-- **The ones at the speeds `(2 ^ m - 1) / 2 ^ m` are polynomially many** ([RuleSpace] §5): the
ray of rule `90` from the single seed, from cell `0`, reads at most `2 ^ m * (K + 1) ^ (m + 1)`
ones below step `2 ^ K`. The pair behind a one lies on one of `2 ^ m` lines
`a + b + r = 2 ^ (m + 1) * b`, and on each the position of the least set bit of `b` and the `m`
lengths of the chains of set bits descending by `m + 1` determine the pair. The ceiling
`card_ones_observedRationalRay_f90_single_le_fib` bounds the same count by a Fibonacci number,
attained at the speeds `(2 ^ m - 1) / (2 ^ m + 1)` by
`fib_le_card_ones_observedRationalRay_f90_single_maxSpeed`. -/
theorem card_ones_observedRationalRay_f90_single_zeroSpeed_le (m K : ℕ) (hm : 1 ≤ m) :
    ((Finset.range (2 ^ K)).filter fun t =>
      observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
        (2 ^ m - 1) (2 ^ m) 0 t = 1).card ≤ 2 ^ m * (K + 1) ^ (m + 1) := by
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ray_card_le_of_line (2 ^ m - 1) (2 ^ m) (by omega) (by omega)
    (fun K => (K + 1) ^ (m + 1)) 0 ?_ K
  intro r hr K'
  unfold lineCount
  refine le_trans (Finset.card_le_card ?_) (card_line_le m K' r (by rw [pow_succ]; omega))
  intro ab hab
  simp only [Finset.mem_filter] at hab ⊢
  refine ⟨hab.1, hab.2.1, ?_⟩
  have h := hab.2.2
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 ^ m)] at h
  have h' : ((ab.1 + ab.2 + r : ℕ) : ℤ) = ((2 ^ (m + 1) * ab.2 : ℕ) : ℤ) := by
    push_cast
    linear_combination h
  exact_mod_cast h'

/-- **The speed is load-bearing**: at the speed `1 / 3`, the case `m = 1` of
[RuleSpace] §5 Proposition 5.16's class, the ones below step `2 ^ 18` number more than the bound
`2 ^ 1 * (18 + 1) ^ (1 + 1)` of the speeds `(2 ^ m - 1) / 2 ^ m` at `m = 1`. -/
theorem card_ones_observedRationalRay_f90_single_zeroSpeed_le_guard :
    2 * (18 + 1) ^ (1 + 1) <
      ((Finset.range (2 ^ 18)).filter fun t =>
        observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
          (2 ^ 1 - 1) (2 ^ 1 + 1) 0 t = 1).card := by
  have h := fib_le_card_ones_observedRationalRay_f90_single_maxSpeed 1 16 le_rfl
  have hfib : Nat.fib 18 = 2584 := by decide +kernel
  have hsub : Finset.range ((2 ^ 1 + 1) * 2 ^ 16) ⊆ Finset.range (2 ^ 18) :=
    Finset.range_mono (by norm_num)
  have h2 := Finset.card_le_card (Finset.filter_subset_filter
    (fun t => observedRationalRay (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      (2 ^ 1 - 1) (2 ^ 1 + 1) 0 t = 1) hsub)
  calc 2 * (18 + 1) ^ (1 + 1) = 722 := by norm_num
    _ < Nat.fib (16 + 2) := by rw [show 16 + 2 = 18 by rfl, hfib]; norm_num
    _ ≤ _ := h.trans h2

end ECA

/-- info: 'ECA.card_ones_observedRationalRay_f90_single_zeroSpeed_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_ones_observedRationalRay_f90_single_zeroSpeed_le

/-- info: 'ECA.card_ones_observedRationalRay_f90_single_zeroSpeed_le_guard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_ones_observedRationalRay_f90_single_zeroSpeed_le_guard
