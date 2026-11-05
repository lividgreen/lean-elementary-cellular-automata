module

public import ECA.Rule106Leftmost
public import ECA.Rule106Sight
public import ECA.Rule106Level
import all ECA.Rule106
import all ECA.EdgeWindow
import all ECA.ReproductionBracket

/-!
# Rule `106` at the states its pair's orbit shadows
([RuleSpace] §5)

Rule `106` acts on the window of a state, read from its leftmost set cell, by `window106`: cell
`j` of the image is `w j + w (j - 2) * w (j - 1)`. A state is shadowed by the pair when, at every
step and at every cell from a bound on, its window agrees with the window of the pair's orbit moved
some cells right. Such a state is reproduced exactly when its diameter is `2`, that is, when it is
the pair `11` up to translation.

The argument rests on three facts. The iterates of a window that is not periodic return to the
window, below a given width, only at the multiples of a power of two that grows without bound with
the width: cell `m` of the image gains a function of the cells below it, so the return times below
width `m + 1` are the return times below width `m` or the multiples of twice the least one. Every
set cell of the `k`-fold renormalization lies at a residue `0`, `1` or `3 * 2 ^ (k - 1) + 1` modulo
`3 * 2 ^ k`, so two of its set cells are adjacent or far apart. And the orbit of the pair at a step
`4 ^ k * u` is the `k`-fold renormalization of its orbit at the step `u`. A reproduced shadowed
state that is not periodic up to translation has, at a step divisible by `4 ^ k`, a second copy
past the bound, which would set two non-adjacent cells of the `k`-fold renormalization of the
pair's window closer together than the residues allow.

## Main results

* `renorm_iterate_eq_zero` / `renorm_iterate_eq_zero_add` — the residues of the set cells of the
  `k`-fold renormalization, and the consequence that a cell `δ` right of a set cell is clear for
  `2 ≤ δ` and `δ + 2 ≤ 3 * 2 ^ (k - 1)`; `renorm_iterate_eq_zero_add_sharp` — the bound is sharp.
* `window106_iterate_four_pow_mul_pair` — the pair's orbit at the step `4 ^ k * u` is the `k`-fold
  renormalization of its orbit at the step `u`.
* `Copies.fullWindow_second_copy` — the second of two or more copies sets two cells of the full
  window, the leftmost and the rightmost set cell of the pattern, at least the pattern's diameter
  plus the gap from the first.
* `FiniteConfiguration.PairShadowed` — the window of the state agrees, at every step and at every
  cell from a bound on, with the window of the pair's orbit moved some cells right.
* `FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff` — **the class decided**: a state
  shadowed by the pair is reproduced exactly when its diameter is `2`;
  `FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff_nonvacuous` meets both sides of the
  equivalence, and `FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff_load_bearing` shows
  the shadow cannot be dropped.
* `pairShadowed_wolfram106_cells` / `not_reproduces_wolfram106_cells` — four states, of widths
  `8`, `11`, `14` and `14`, are shadowed by the pair, certified by a finite computation on the
  difference of the windows, and so are not reproduced.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The return times of a window -/

/-- A step of the window map reads three cells: windows agreeing below `m` have images agreeing
below `m`. -/
private theorem window106_congr_lt {V W : ℕ → ZMod 2} {m : ℕ} (h : ∀ j < m, V j = W j) :
    ∀ j < m, window106 V j = window106 W j := by
  intro j hj
  have e2 : (if 2 ≤ j then V (j - 2) else 0) = if 2 ≤ j then W (j - 2) else 0 := by
    split_ifs with h2
    · exact h _ (by omega)
    · rfl
  have e1 : (if 1 ≤ j then V (j - 1) else 0) = if 1 ≤ j then W (j - 1) else 0 := by
    split_ifs with h1
    · exact h _ (by omega)
    · rfl
  simp only [window106, e1, e2, h j hj]

/-- Iterates of two windows that agree below `m` agree below `m`. -/
private theorem window106_iterate_congr_lt {V W : ℕ → ZMod 2} {m : ℕ}
    (h : ∀ j < m, V j = W j) (n : ℕ) : ∀ j < m, window106^[n] V j = window106^[n] W j := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact window106_congr_lt ih

/-- Cell `m ≥ 2` of the `n`-th iterate gains the sum, over the earlier steps, of the product of
the cells `m - 2` and `m - 1`. -/
private theorem window106_iterate_apply_sum (w : ℕ → ZMod 2) {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    window106^[n] w m = w m +
      ∑ i ∈ Finset.range n, window106^[i] w (m - 2) * window106^[i] w (m - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Finset.sum_range_succ, ← add_assoc, ← ih]
    simp [window106, show 2 ≤ m from hm, show 1 ≤ m from by omega]

/-- **The return times below a width**: for every window and every width `m` there is an exponent
`e` such that the iterates of the window agree with it below `m` exactly at the steps divisible by
`2 ^ e`. -/
private theorem window106_returns_iff (w : ℕ → ZMod 2) (m : ℕ) :
    ∃ e : ℕ, ∀ t : ℕ, (∀ j < m, window106^[t] w j = w j) ↔ 2 ^ e ∣ t := by
  induction m with
  | zero => exact ⟨0, fun t => by simp⟩
  | succ m ih =>
    obtain ⟨e, he⟩ := ih
    by_cases hm : m < 2
    · refine ⟨0, fun t => ?_⟩
      simp only [pow_zero, one_dvd, iff_true]
      intro j hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact window106_iterate_zero t w
      · exact window106_iterate_one t w
    · push Not at hm
      set f : ℕ → ZMod 2 := fun i => window106^[i] w (m - 2) * window106^[i] w (m - 1) with hf
      have hP : ∀ j < m, window106^[2 ^ e] w j = w j := (he _).mpr dvd_rfl
      have hper : ∀ q i, f (i + q * 2 ^ e) = f i := by
        have h1 : ∀ i, f (i + 2 ^ e) = f i := by
          intro i
          have hc := window106_iterate_congr_lt hP i
          simp only [hf]
          rw [Function.iterate_add_apply, hc (m - 2) (by omega),
            hc (m - 1) (by omega)]
        intro q
        induction q with
        | zero => intro i; simp
        | succ q ih =>
          intro i
          rw [show i + (q + 1) * 2 ^ e = (i + q * 2 ^ e) + 2 ^ e by ring, h1, ih]
      set c : ZMod 2 := ∑ i ∈ Finset.range (2 ^ e), f i with hc
      have hsum : ∀ q : ℕ, ∑ i ∈ Finset.range (q * 2 ^ e), f i = (q : ZMod 2) * c := by
        intro q
        induction q with
        | zero => simp
        | succ q ih =>
          rw [show (q + 1) * 2 ^ e = q * 2 ^ e + 2 ^ e by ring, Finset.sum_range_add, ih]
          have : ∑ x ∈ Finset.range (2 ^ e), f (q * 2 ^ e + x) = c := by
            apply Finset.sum_congr rfl
            intro x _
            rw [add_comm, hper]
          rw [this]
          push_cast
          ring
      have hcell : ∀ t, window106^[t] w m = w m ↔ ∑ i ∈ Finset.range t, f i = 0 := by
        intro t
        rw [window106_iterate_apply_sum w (by omega) t]
        simp [hf]
      have hret : ∀ t, (∀ j < m + 1, window106^[t] w j = w j) ↔
          (2 ^ e ∣ t ∧ ∑ i ∈ Finset.range t, f i = 0) := by
        intro t
        constructor
        · intro h
          exact ⟨(he t).mp (fun j hj => h j (by omega)), (hcell t).mp (h m (by omega))⟩
        · rintro ⟨h1, h2⟩ j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact (he t).mpr h1 j hj
          · exact (hcell t).mpr h2
      by_cases hc0 : c = 0
      · refine ⟨e, fun t => ?_⟩
        rw [hret]
        constructor
        · exact fun h => h.1
        · intro h
          obtain ⟨q, rfl⟩ := h
          refine ⟨⟨q, by ring⟩, ?_⟩
          rw [mul_comm, hsum, hc0, mul_zero]
      · have hc1 : c = 1 := by
          revert hc0
          generalize c = x
          revert x
          decide
        refine ⟨e + 1, fun t => ?_⟩
        rw [hret]
        constructor
        · rintro ⟨⟨q, rfl⟩, h2⟩
          rw [mul_comm, hsum, hc1, mul_one] at h2
          have : 2 ∣ q := (ZMod.natCast_eq_zero_iff q 2).mp h2
          obtain ⟨q', rfl⟩ := this
          exact ⟨q', by ring⟩
        · rintro ⟨q, rfl⟩
          refine ⟨⟨2 * q, by ring⟩, ?_⟩
          rw [show 2 ^ (e + 1) * q = (2 * q) * 2 ^ e by ring, hsum, hc1, mul_one]
          push_cast
          rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

/-- **The return times grow without bound**: for a window that is not periodic, the steps at
which an iterate agrees with it below a width `m` are all divisible by `2 ^ N`, for a width `m`
large enough. -/
private theorem window106_returns_dvd (w : ℕ → ZMod 2) (hw : ∀ T, 0 < T → window106^[T] w ≠ w)
    (N : ℕ) : ∃ m, ∀ t, (∀ j < m, window106^[t] w j = w j) → 2 ^ N ∣ t := by
  by_contra hcon
  push Not at hcon
  apply hw (2 ^ N) (by positivity)
  funext j
  obtain ⟨e, he⟩ := window106_returns_iff w (j + 1)
  obtain ⟨t, ht, hnd⟩ := hcon (j + 1)
  have h1 : 2 ^ e ∣ t := (he t).mp ht
  have h2 : e < N := by
    by_contra h
    push Not at h
    exact hnd ((pow_dvd_pow 2 h).trans h1)
  exact (he _).mpr (pow_dvd_pow 2 h2.le) j (by omega)

/-! ## The residues of the set cells of a renormalization -/

private theorem res_even (A x i : ℕ) (hi : i = 2 * x)
    (h : x % (6 * A) = 0 ∨ x % (6 * A) = 1 ∨ x % (6 * A) = 3 * A + 1) (h3 : x % 3 ≠ 1) :
    i % (12 * A) = 0 := by
  have h3' : x % (6 * A) % 3 = x % 3 := Nat.mod_mod_of_dvd x ⟨2 * A, by ring⟩
  have hd : i % (2 * (6 * A)) = 2 * (x % (6 * A)) := by
    rw [hi]
    exact Nat.mul_mod_mul_left 2 x (6 * A)
  rw [show 12 * A = 2 * (6 * A) by ring]
  rcases h with h | h | h
  · rw [hd, h]
  · rw [h] at h3'
    omega
  · rw [h] at h3'
    omega

private theorem res_odd (A x i : ℕ) (hA : 0 < A) (hi : i + 1 = 2 * x)
    (h : x % (6 * A) = 0 ∨ x % (6 * A) = 1 ∨ x % (6 * A) = 3 * A + 1) (h3 : x % 3 = 1) :
    i % (12 * A) = 1 ∨ i % (12 * A) = 6 * A + 1 := by
  have h3' : x % (6 * A) % 3 = x % 3 := Nat.mod_mod_of_dvd x ⟨2 * A, by ring⟩
  have hM : 0 < 6 * A := by omega
  have h1 := Nat.div_add_mod x (6 * A)
  have h2 := Nat.mod_lt x hM
  have e : 12 * A * (x / (6 * A)) = 2 * (6 * A * (x / (6 * A))) := by ring
  have key : ∀ r, x % (6 * A) = r → 1 ≤ r → r < 6 * A → i % (12 * A) = 2 * r - 1 := by
    intro r hr hr1 hr2
    have : i = 12 * A * (x / (6 * A)) + (2 * r - 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rcases h with h | h | h
  · rw [h] at h3'
    omega
  · left
    have := key 1 h (by omega) (by omega)
    omega
  · right
    have := key (3 * A + 1) h (by omega) (by omega)
    omega

private theorem renorm_ne_zero {w : ℕ → ZMod 2} {i : ℕ} (h : renorm w i ≠ 0) :
    (i % 2 = 0 ∧ (i / 2) % 3 ≠ 1 ∧ w (i / 2) ≠ 0) ∨
      (i % 2 = 1 ∧ ((i + 1) / 2) % 3 = 1 ∧ w ((i + 1) / 2) ≠ 0) := by
  unfold renorm at h
  by_cases h2 : i % 2 = 0
  · by_cases h3 : (i / 2) % 3 ≠ 1
    · rw [ite_eq_left h2, ite_eq_left h3] at h
      exact Or.inl ⟨h2, h3, h⟩
    · rw [ite_eq_left h2, ite_eq_right h3] at h
      exact absurd rfl h
  · by_cases h3 : ((i + 1) / 2) % 3 = 1
    · rw [ite_eq_right h2, ite_eq_left h3] at h
      exact Or.inr ⟨by omega, h3, h⟩
    · rw [ite_eq_right h2, ite_eq_right h3] at h
      exact absurd rfl h

private theorem renorm_iterate_ne_zero_res (j : ℕ) : ∀ (v : ℕ → ZMod 2) (i : ℕ),
    renorm^[j + 1] v i ≠ 0 →
      i % (6 * 2 ^ j) = 0 ∨ i % (6 * 2 ^ j) = 1 ∨ i % (6 * 2 ^ j) = 3 * 2 ^ j + 1 := by
  induction j with
  | zero =>
    intro v i h
    rw [zero_add, Function.iterate_one] at h
    simp only [pow_zero, mul_one]
    rcases renorm_ne_zero h with ⟨h2, h3, -⟩ | ⟨h2, h3, -⟩ <;> omega
  | succ j ih =>
    intro v i h
    rw [Function.iterate_succ_apply'] at h
    have hA : 0 < 2 ^ j := by positivity
    have e12 : 6 * 2 ^ (j + 1) = 12 * 2 ^ j := by ring
    have e3 : 3 * 2 ^ (j + 1) + 1 = 6 * 2 ^ j + 1 := by ring
    rw [e12, e3]
    rcases renorm_ne_zero h with ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
    · exact Or.inl (res_even (2 ^ j) (i / 2) i (by omega) (ih _ _ h4) h3)
    · exact Or.inr (res_odd (2 ^ j) ((i + 1) / 2) i hA (by omega) (ih _ _ h4) h3)

/-- **The residues of the set cells of a renormalization**: every set cell of the `k`-fold
renormalization of a window, `k ≥ 1`, lies at a residue `0`, `1` or `3 * 2 ^ (k - 1) + 1` modulo
`3 * 2 ^ k`. -/
theorem renorm_iterate_eq_zero (k : ℕ) (hk : 1 ≤ k) (v : ℕ → ZMod 2) (i : ℕ)
    (h0 : i % (3 * 2 ^ k) ≠ 0) (h1 : i % (3 * 2 ^ k) ≠ 1)
    (h2 : i % (3 * 2 ^ k) ≠ 3 * 2 ^ (k - 1) + 1) : renorm^[k] v i = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  by_contra hne
  have := renorm_iterate_ne_zero_res j v i hne
  have e : 3 * 2 ^ (j + 1) = 6 * 2 ^ j := by ring
  rw [e] at h0 h1 h2
  simp only [Nat.add_sub_cancel] at h2
  omega

private theorem mod_add_of_lt (M i δ : ℕ) (h : i % M + δ < M) : (i + δ) % M = i % M + δ := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show δ < M by omega), Nat.mod_eq_of_lt h]

/-- **Two set cells of a renormalization are adjacent or far apart**: in the `k`-fold
renormalization of a window, `k ≥ 1`, a cell `δ` right of a set cell is clear for `2 ≤ δ` and
`δ + 2 ≤ 3 * 2 ^ (k - 1)`. -/
theorem renorm_iterate_eq_zero_add (k : ℕ) (hk : 1 ≤ k) (v : ℕ → ZMod 2) (i δ : ℕ)
    (hδ : 2 ≤ δ) (hδk : δ + 2 ≤ 3 * 2 ^ (k - 1)) (hi : renorm^[k] v i ≠ 0) :
    renorm^[k] v (i + δ) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hres := renorm_iterate_ne_zero_res j v i hi
  simp only [Nat.add_sub_cancel] at hδk
  have e : 3 * 2 ^ (j + 1) = 6 * 2 ^ j := by ring
  have hlt : i % (6 * 2 ^ j) + δ < 6 * 2 ^ j := by omega
  have hm := mod_add_of_lt (6 * 2 ^ j) i δ hlt
  apply renorm_iterate_eq_zero (j + 1) hk v (i + δ)
  all_goals rw [e, hm]
  · omega
  · omega
  · simp only [Nat.add_sub_cancel]
    omega

/-- **The bound is sharp**: at `k = 2` the bound `δ + 2 ≤ 3 * 2 ^ (k - 1)` fails at `δ = 5`, one
past its last value, and the window with cells `2` and `3` set has a `2`-fold renormalization with
cells `7` and `12` set, `5` apart. -/
theorem renorm_iterate_eq_zero_add_sharp :
    2 ≤ 5 ∧ ¬ (5 + 2 ≤ 3 * 2 ^ (2 - 1)) ∧
      renorm^[2] (fun j => if j = 2 ∨ j = 3 then (1 : ZMod 2) else 0) 7 = 1 ∧
      renorm^[2] (fun j => if j = 2 ∨ j = 3 then (1 : ZMod 2) else 0) (7 + 5) = 1 := by
  decide +kernel

/-! ## The orbit of the pair at the steps `4 ^ k * u` -/

/-- **The orbit of the pair at the step `4 ^ k * u`** is the `k`-fold renormalization of its orbit
at the step `u`. -/
theorem window106_iterate_four_pow_mul_pair (k u : ℕ) :
    window106^[4 ^ k * u] (pairLattice {0}) = renorm^[k] (window106^[u] (pairLattice {0})) := by
  have h := (renorm_pow_window106_iterate rule106Stays_pair k u).2
  rw [Function.iterate_fixed renorm_pair k] at h
  exact h


/-! ## Windows of states, and the second of several copies -/

private theorem fullWindow_eq_zero_of_diam_le {p : FiniteConfiguration} (hp : p ≠ 0) {j : ℕ}
    (hj : p.diam ≤ j) : p.fullWindow j = 0 := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmm := Finset.min'_le_max' p.support hne
  by_contra hc
  have hmem : p.leftEnd + (j : ℤ) ∈ p.support := Finsupp.mem_support_iff.mpr hc
  have hle : p.leftEnd + (j : ℤ) ≤ p.support.max' hne := Finset.le_max' p.support _ hmem
  rw [diam_eq' hne] at hj
  rw [leftEnd_eq hne] at hle
  omega

private theorem window106_eq_of_diam_one {p : FiniteConfiguration} (hp : p ≠ 0)
    (hd : p.diam = 1) : window106 p.fullWindow = p.fullWindow := by
  funext j
  have hz : ∀ i, 1 ≤ i → p.fullWindow i = 0 := fun i hi =>
    fullWindow_eq_zero_of_diam_le hp (by omega)
  simp only [window106]
  by_cases h2 : 2 ≤ j
  · rw [hz (j - 1) (by omega)]
    simp
  · simp [h2]

private theorem eq_translate_of_fullWindow_eq {a b : FiniteConfiguration} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : a.fullWindow = b.fullWindow) :
    a = translate (a.leftEnd - b.leftEnd) b := by
  ext x
  rw [translate_apply']
  by_cases hx : x < a.leftEnd
  · rw [eq_zero_of_lt_leftEnd ha hx, eq_zero_of_lt_leftEnd hb (by omega)]
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x - a.leftEnd by omega)
    have h1 : a x = a.fullWindow n := by
      simp only [fullWindow]
      congr 1
      omega
    have h2 : b (x - (a.leftEnd - b.leftEnd)) = b.fullWindow n := by
      simp only [fullWindow]
      congr 1
      omega
    rw [h1, h2, h]

private theorem rightPairOnly_of_diam_eq_two {p : FiniteConfiguration} (hp : p ≠ 0)
    (hd : p.diam = 2) : p.RightPairOnly := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hd' := diam_eq' hne
  have hmm := Finset.min'_le_max' p.support hne
  have hmax : p (p.support.max' hne) ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)
  have hmin : p (p.support.min' hne) ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
  refine ⟨p.support.max' hne, hmax, ?_, ?_, ?_⟩
  · rwa [show p.support.max' hne - 1 = p.support.min' hne by omega]
  · intro i hi
    by_contra hc
    have := Finset.le_max' p.support i (Finsupp.mem_support_iff.mpr hc)
    omega
  · intro i hi hi1
    have h1 := Finset.le_max' p.support (i + 1) (Finsupp.mem_support_iff.mpr hi1)
    have h2 := Finset.min'_le p.support i (Finsupp.mem_support_iff.mpr hi)
    omega

/-- **The second of two or more copies sets two cells of the full window**: if a state is `k ≥ 2`
copies of a nonzero pattern at gap `G`, then for some `D` at least the pattern's diameter plus `G`
the full window of the state has the cells `D` and `D + (diam p - 1)` set, the leftmost and
rightmost set cells of the second copy. -/
theorem Copies.fullWindow_second_copy {p s : FiniteConfiguration} {k G : ℕ} (hp : p ≠ 0)
    (hk : 2 ≤ k) (h : Copies p s k G) :
    ∃ D : ℕ, p.diam + G ≤ D ∧ s.fullWindow D ≠ 0 ∧ s.fullWindow (D + (p.diam - 1)) ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmin : p.leftEnd = p.support.min' hpne := leftEnd_eq hpne
  have hdiam := diam_eq' hpne
  have hmm := Finset.min'_le_max' p.support hpne
  have hd1 : 1 ≤ p.diam := one_le_diam hp
  have hpa : p p.leftEnd ≠ 0 := by
    rw [hmin]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
  have hpb : p (p.leftEnd + ((p.diam - 1 : ℕ) : ℤ)) ≠ 0 := by
    have : p.leftEnd + ((p.diam - 1 : ℕ) : ℤ) = p.support.max' hpne := by omega
    rw [this]
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)
  have hlow : ∀ y, y < p.leftEnd → p y = 0 := fun y hy => eq_zero_of_lt_leftEnd hp hy
  have hhigh : ∀ y, p.leftEnd + ((p.diam - 1 : ℕ) : ℤ) < y → p y = 0 := by
    intro y hy
    by_contra hc'
    have := Finset.le_max' p.support y (Finsupp.mem_support_iff.mpr hc')
    omega
  have hchain : ∀ i j, i < j → j < k → c i + p.diam + G ≤ c j := by
    intro i j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro hij hjk
      have h1 := hc j (by omega)
      by_cases hij' : i = j
      · subst hij'
        exact h1
      · have h2 := ih (by omega) (by omega)
        omega
  have hev : ∀ x, ((Finset.range k).sum fun j => translate (c j) p) x =
      (Finset.range k).sum fun j => p (x - c j) := by
    intro x
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun j _ => translate_apply' _ _ _
  have hk0 : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hk1 : 1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  -- the first copy's leftmost cell is set, and nothing lies left of it
  have hs0 : ((Finset.range k).sum fun j => translate (c j) p) (c 0 + p.leftEnd) ≠ 0 := by
    rw [hev, Finset.sum_eq_single_of_mem 0 hk0]
    · simpa using hpa
    · intro j hj hj0
      apply hlow
      have := hchain 0 j (by omega) (Finset.mem_range.mp hj)
      omega
  have hsl : ∀ x, x < c 0 + p.leftEnd →
      ((Finset.range k).sum fun j => translate (c j) p) x = 0 := by
    intro x hx
    rw [hev]
    apply Finset.sum_eq_zero
    intro j hj
    apply hlow
    by_cases hj0 : j = 0
    · subst hj0
      omega
    · have := hchain 0 j (by omega) (Finset.mem_range.mp hj)
      omega
  have hend : ((Finset.range k).sum fun j => translate (c j) p).leftEnd = c 0 + p.leftEnd := by
    have hsne : ((Finset.range k).sum fun j => translate (c j) p).support.Nonempty :=
      ⟨_, Finsupp.mem_support_iff.mpr hs0⟩
    rw [leftEnd_eq hsne]
    apply le_antisymm (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hs0))
    apply Finset.le_min'
    intro y hy
    by_contra hlt
    push Not at hlt
    exact (Finsupp.mem_support_iff.mp hy) (hsl y hlt)
  -- the second copy's leftmost and rightmost cells are set
  have hs1 : ∀ e : ℕ, e < p.diam → p (p.leftEnd + (e : ℤ)) ≠ 0 →
      ((Finset.range k).sum fun j => translate (c j) p) (c 1 + p.leftEnd + (e : ℤ)) ≠ 0 := by
    intro e he hpe
    rw [hev, Finset.sum_eq_single_of_mem 1 hk1]
    · rwa [show c 1 + p.leftEnd + (e : ℤ) - c 1 = p.leftEnd + (e : ℤ) by ring]
    · intro j hj hj1
      by_cases hj0 : j = 0
      · subst hj0
        apply hhigh
        have := hchain 0 1 (by omega) (by omega)
        omega
      · apply hlow
        have := hchain 1 j (by omega) (Finset.mem_range.mp hj)
        omega
  refine ⟨(c 1 - c 0).toNat, ?_, ?_, ?_⟩
  · have := hchain 0 1 (by omega) (by omega)
    omega
  · simp only [fullWindow, hend]
    have e : c 0 + p.leftEnd + (((c 1 - c 0).toNat : ℕ) : ℤ) = c 1 + p.leftEnd + ((0 : ℕ) : ℤ) := by
      have := hchain 0 1 (by omega) (by omega)
      omega
    rw [e]
    exact hs1 0 (by omega) (by simpa using hpa)
  · simp only [fullWindow, hend]
    have e : c 0 + p.leftEnd + (((c 1 - c 0).toNat + (p.diam - 1) : ℕ) : ℤ) =
        c 1 + p.leftEnd + ((p.diam - 1 : ℕ) : ℤ) := by
      have := hchain 0 1 (by omega) (by omega)
      push_cast
      omega
    rw [e]
    exact hs1 (p.diam - 1) (by omega) hpb


/-! ## The states the pair's orbit shadows -/

/-- **A state shadowed by the pair**: for some shift `s` and bound `B`, at every step `n` and at
every cell `j ≥ B`, the full window of the `n`-th iterate of rule `106`'s window map at the
state's full window agrees with the window of the `n`-th iterate at the pair `11`, moved `s`
cells right. -/
def FiniteConfiguration.PairShadowed (p : FiniteConfiguration) : Prop :=
  ∃ s B : ℕ, ∀ n j : ℕ, B ≤ j →
    window106^[n] p.fullWindow j = windowShift s (window106^[n] (pairLattice {0})) j

/-- **Rule `106` reproduces a state shadowed by the pair exactly when it is the pair**: a state
whose window, at every step and at every cell past a bound, is the window of the pair's orbit
moved right is reproduced exactly when its diameter is `2`, that is, when it is the pair `11` up
to translation ([RuleSpace] §5). -/
theorem FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff
    (hq : wolframRule 106 0 0 0 = 0) {p : FiniteConfiguration} (hp : p.PairShadowed) :
    Reproduces (finRule (wolframRule 106) hq) p ↔ diam p = 2 := by
  constructor
  · intro hrep
    by_contra hd2
    obtain ⟨hp0, hrep'⟩ := hrep
    obtain ⟨s, B, hsh⟩ := hp
    by_cases hT : ∃ T, 0 < T ∧ window106^[T] p.fullWindow = p.fullWindow
    · obtain ⟨T, hT0, hT⟩ := hT
      obtain ⟨hne, hfw⟩ := iterate_fullWindow hq hp0 T
      have htr := eq_translate_of_fullWindow_eq hne hp0 (hfw.trans hT)
      exact Reproduces.not_of_iterate_eq_translate (wolframRule 106) hq hT0 htr ⟨hp0, hrep'⟩
    · push Not at hT
      have hd1 := one_le_diam hp0
      have hd3 : 3 ≤ p.diam := by
        by_contra hlt
        have h1 : p.diam = 1 := by omega
        exact hT 1 Nat.one_pos (by
          rw [Function.iterate_one]
          exact window106_eq_of_diam_one hp0 h1)
      set k := p.diam + 2 with hk
      obtain ⟨m, hm⟩ := window106_returns_dvd p.fullWindow hT (2 * k)
      obtain ⟨t, K, hK, hcop⟩ := hrep' 2 (m + B + s)
      obtain ⟨hne, hfw⟩ := iterate_fullWindow hq hp0 t
      have hlw := leftWindowCopies p _ K (m + B + s) hp0 (by omega) hcop
      have hret : ∀ j < m, window106^[t] p.fullWindow j = p.fullWindow j := by
        intro j hj
        rw [← hfw]
        have := congrFun hlw j
        simp only [leftWindow, show j < p.diam + (m + B + s) by omega, ite_true] at this
        exact this
      obtain ⟨u, hu⟩ := hm t hret
      have ht : t = 4 ^ k * u := by
        rw [hu, pow_mul]
        norm_num
      obtain ⟨D, hD, hD0, hD1⟩ := Copies.fullWindow_second_copy hp0 (by omega) hcop
      rw [hfw] at hD0 hD1
      have h0 := hsh t D (by omega)
      have h1 := hsh t (D + (p.diam - 1)) (by omega)
      rw [h0] at hD0
      rw [h1] at hD1
      have hO := window106_iterate_four_pow_mul_pair k u
      rw [← ht] at hO
      simp only [windowShift, show s ≤ D by omega, ite_true, hO] at hD0
      simp only [windowShift, show s ≤ D + (p.diam - 1) by omega, ite_true, hO] at hD1
      have hpow : p.diam + 1 < 2 ^ (p.diam + 1) := Nat.lt_two_pow_self
      have := renorm_iterate_eq_zero_add k (by omega) (window106^[u] (pairLattice {0}))
        (D - s) (p.diam - 1) (by omega)
        (by rw [hk, show p.diam + 2 - 1 = p.diam + 1 by omega]; omega) hD0
      rw [show D - s + (p.diam - 1) = D + (p.diam - 1) - s by omega] at this
      exact hD1 this
  · intro hd
    have hp0 : p ≠ 0 := by
      intro h
      rw [h] at hd
      simp [FiniteConfiguration.diam] at hd
    exact ((rightPairOnly_of_diam_eq_two hp0 hd).reproduces_wolfram106_iff hq).mpr hd


/-! ## A shadow certified by a finite computation -/

private theorem testBit_stepNat (x j : ℕ) :
    (stepNat x).testBit j = (x.testBit j ^^ ((decide (2 ≤ j) && x.testBit (j - 2)) &&
      (decide (1 ≤ j) && x.testBit (j - 1)))) := by
  simp [stepNat, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]

private theorem stepNat_shiftLeft (y s : ℕ) : stepNat (y <<< s) = stepNat y <<< s := by
  have h2 : (y <<< s) <<< 2 = (y <<< 2) <<< s := by
    rw [← Nat.shiftLeft_add, ← Nat.shiftLeft_add, add_comm]
  have h1 : (y <<< s) <<< 1 = (y <<< 1) <<< s := by
    rw [← Nat.shiftLeft_add, ← Nat.shiftLeft_add, add_comm]
  unfold stepNat
  rw [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_and_distrib, h2, h1]

private theorem stepNat_mod (x M : ℕ) : stepNat x % 2 ^ M = stepNat (x % 2 ^ M) % 2 ^ M := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, testBit_stepNat, testBit_stepNat]
  by_cases hj : j < M
  · simp only [hj, decide_true, Bool.true_and, Nat.testBit_mod_two_pow]
    have h2 : (j - 2 < M) := by omega
    have h1 : (j - 1 < M) := by omega
    simp [h1, h2]
  · simp [hj]

private theorem shiftLeft_mod_two_pow (y s L : ℕ) :
    (y <<< s) % 2 ^ (s + L) = (y % 2 ^ L) <<< s := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases h1 : s ≤ j
  · by_cases h2 : j - s < L
    · simp [h1, h2, show j < s + L by omega]
    · simp [h1, h2, show ¬ j < s + L by omega]
  · simp [h1]

/-- The difference of the steps of two numbers whose difference is below `2 ^ B` is below
`2 ^ (B + 2)`. -/
private theorem stepNat_xor_lt (Z D B : ℕ) (hD : D < 2 ^ B) :
    stepNat (Z ^^^ D) ^^^ stepNat Z < 2 ^ (B + 2) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [Nat.testBit_xor, testBit_stepNat, testBit_stepNat]
  have hD' : ∀ i, B ≤ i → D.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) hi))
  have a0 := hD' j (by omega)
  have a1 := hD' (j - 1) (by omega)
  have a2 := hD' (j - 2) (by omega)
  simp only [Nat.testBit_xor, a0, a1, a2, Bool.xor_false]
  cases Z.testBit j <;> cases Z.testBit (j - 1) <;> cases Z.testBit (j - 2) <;> simp

/-- **The joint state of the finite check**, as a pair of numbers read as windows: the first is the
difference of the two windows, kept below cell `B + 2`, the second the pair's window, kept below
cell `B + 2 - s`. One step takes the first to the difference of the two images and the second to
the image of the pair's window, each cut at its own cell. -/
private def jointStep (s B : ℕ) (σ : ℕ × ℕ) : ℕ × ℕ :=
  ((stepNat ((σ.2 <<< s) ^^^ σ.1) ^^^ stepNat (σ.2 <<< s)) % 2 ^ (B + 2),
    stepNat σ.2 % 2 ^ (B + 2 - s))

/-- **The finite check**: the difference at the start is below `2 ^ B`, the differences of the `P`
joint states from the start are below `2 ^ B`, and the joint state returns to the start after `P`
steps. -/
private def shadowCertOK (N s B P : ℕ) : Bool :=
  decide (N ^^^ (3 <<< s) < 2 ^ B) &&
    (List.range P).all (fun n =>
      decide (((jointStep s B)^[n] (N ^^^ (3 <<< s), 3 % 2 ^ (B + 2 - s))).1 < 2 ^ B)) &&
    decide ((jointStep s B)^[P] (N ^^^ (3 <<< s), 3 % 2 ^ (B + 2 - s)) =
      (N ^^^ (3 <<< s), 3 % 2 ^ (B + 2 - s)))

private theorem jointStep_spec (X Y s B : ℕ) (hsB : s ≤ B) (hD : (X ^^^ (Y <<< s)) < 2 ^ B) :
    stepNat X ^^^ (stepNat Y <<< s) =
      (jointStep s B (X ^^^ (Y <<< s), Y % 2 ^ (B + 2 - s))).1 := by
  have hX : X = (Y <<< s) ^^^ (X ^^^ (Y <<< s)) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases X.testBit i <;> cases (Y <<< s).testBit i <;> rfl
  set D := X ^^^ (Y <<< s) with hDdef
  have hlt := stepNat_xor_lt (Y <<< s) D B hD
  have hz : (Y <<< s) % 2 ^ (B + 2) = (Y % 2 ^ (B + 2 - s)) <<< s := by
    rw [← shiftLeft_mod_two_pow, show s + (B + 2 - s) = B + 2 by omega]
  have hDmod : D % 2 ^ (B + 2) = D :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hR : stepNat X ^^^ stepNat (Y <<< s) = stepNat ((Y <<< s) ^^^ D) ^^^ stepNat (Y <<< s) := by
    rw [← hX]
  have h1 : ((Y <<< s) ^^^ D) % 2 ^ (B + 2) = ((Y % 2 ^ (B + 2 - s)) <<< s) ^^^ D := by
    rw [Nat.xor_mod_two_pow, hz, hDmod]
  have h2 : stepNat ((Y <<< s) ^^^ D) % 2 ^ (B + 2) =
      stepNat (((Y % 2 ^ (B + 2 - s)) <<< s) ^^^ D) % 2 ^ (B + 2) := by
    rw [stepNat_mod, h1]
  have h3 : stepNat (Y <<< s) % 2 ^ (B + 2) =
      stepNat ((Y % 2 ^ (B + 2 - s)) <<< s) % 2 ^ (B + 2) := by
    rw [stepNat_mod, hz]
  unfold jointStep
  simp only
  rw [← stepNat_shiftLeft, hR, ← Nat.mod_eq_of_lt hlt, Nat.xor_mod_two_pow, h2, h3,
    ← Nat.xor_mod_two_pow]

private theorem shadow_of_cert (N s B P : ℕ) (hsB : s ≤ B) (hP : 0 < P)
    (h : shadowCertOK N s B P = true) : ∀ n, (stepNat^[n] N ^^^ (stepNat^[n] 3 <<< s)) < 2 ^ B := by
  unfold shadowCertOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h0, htab⟩, hret⟩ := h
  set σ0 : ℕ × ℕ := (N ^^^ (3 <<< s), 3 % 2 ^ (B + 2 - s)) with hσ0
  have hper : Function.IsPeriodicPt (jointStep s B) P σ0 := hret
  have hbound : ∀ n, ((jointStep s B)^[n] σ0).1 < 2 ^ B := by
    intro n
    rw [← hper.iterate_mod_apply n]
    exact htab _ (Nat.mod_lt _ hP)
  have key : ∀ n, (stepNat^[n] N ^^^ (stepNat^[n] 3 <<< s)) = ((jointStep s B)^[n] σ0).1 ∧
      stepNat^[n] 3 % 2 ^ (B + 2 - s) = ((jointStep s B)^[n] σ0).2 := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hD : (stepNat^[n] N ^^^ (stepNat^[n] 3 <<< s)) < 2 ^ B := by
        rw [ih1]
        exact hbound n
      have hσ : (jointStep s B)^[n] σ0 =
          (stepNat^[n] N ^^^ (stepNat^[n] 3 <<< s), stepNat^[n] 3 % 2 ^ (B + 2 - s)) :=
        Prod.ext ih1.symm ih2.symm
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        hσ]
      refine ⟨jointStep_spec _ _ s B hsB hD, ?_⟩
      unfold jointStep
      simp only
      exact (stepNat_mod _ _)
  intro n
  rw [(key n).1]
  exact hbound n


/-- The state of the cells of a finite set. -/
private noncomputable abbrev cfgOf (S : Finset ℤ) : FiniteConfiguration :=
  Finsupp.indicator S fun _ _ => (1 : ZMod 2)

private theorem support_indicator_one (S : Finset ℤ) :
    (cfgOf S).support = S := by
  ext x
  rw [Finsupp.mem_support_iff, Finsupp.indicator_apply]
  by_cases hx : x ∈ S <;> simp [hx]

private theorem fullWindow_indicator {S : Finset ℤ} (h0 : 0 ∈ S) (hS : ∀ x ∈ S, 0 ≤ x) (j : ℕ) :
    (cfgOf S).fullWindow j =
      if (j : ℤ) ∈ S then 1 else 0 := by
  have hne : (cfgOf S).support.Nonempty := by
    rw [support_indicator_one]
    exact ⟨0, h0⟩
  have hle : (cfgOf S).leftEnd = 0 := by
    rw [leftEnd_eq hne]
    apply le_antisymm
    · exact Finset.min'_le _ _ (by rw [support_indicator_one]; exact h0)
    · apply Finset.le_min'
      intro y hy
      rw [support_indicator_one] at hy
      exact hS y hy
  simp only [fullWindow, hle, zero_add, Finsupp.indicator_apply]
  by_cases hj : (j : ℤ) ∈ S <;> simp [hj]

private theorem fullWindow_indicator_eq {S : Finset ℤ} {N W : ℕ} (h0 : 0 ∈ S)
    (hS : ∀ x ∈ S, 0 ≤ x ∧ x < (W : ℤ)) (hN : N < 2 ^ W)
    (h : ∀ j < W, (j : ℤ) ∈ S ↔ N.testBit j = true) :
    (cfgOf S).fullWindow = winOfNat N := by
  funext j
  rw [fullWindow_indicator h0 (fun x hx => (hS x hx).1)]
  unfold winOfNat
  by_cases hj : j < W
  · by_cases hb : N.testBit j = true
    · rw [ite_eq_left hb, ite_eq_left ((h j hj).mpr hb)]
    · rw [ite_eq_right hb, ite_eq_right (fun hm => hb ((h j hj).mp hm))]
  · have h1 : ¬ (j : ℤ) ∈ S := fun hm => by
      have := (hS _ hm).2
      omega
    have h2 : N.testBit j = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [ite_eq_right h1, h2]
    rfl

private theorem pairLattice_zero_eq_winOfNat : pairLattice {0} = winOfNat 3 := by
  funext j
  by_cases hj : j < 2
  · interval_cases j <;> decide
  · rw [winOfNat_apply_of_lt (L := 2) (by norm_num) (by omega)]
    simp only [pairLattice, Finset.mem_singleton]
    exact ite_eq_right (fun h => by omega)

private theorem pairShadowed_of_nat {p : FiniteConfiguration} {N s B : ℕ}
    (hfw : p.fullWindow = winOfNat N) (hsB : s ≤ B)
    (hcert : ∀ n, (stepNat^[n] N ^^^ (stepNat^[n] 3 <<< s)) < 2 ^ B) : p.PairShadowed := by
  refine ⟨s, B, fun n j hj => ?_⟩
  rw [hfw, iterate_winOfNat, pairLattice_zero_eq_winOfNat, iterate_winOfNat]
  unfold windowShift winOfNat
  have hb : (stepNat^[n] N ^^^ (stepNat^[n] 3 <<< s)).testBit j = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (hcert n) (Nat.pow_le_pow_right (by norm_num) hj))
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft] at hb
  have hsj : s ≤ j := by omega
  rw [ite_eq_left hsj]
  simp only [hsj, decide_true, Bool.true_and] at hb
  have : (stepNat^[n] N).testBit j = (stepNat^[n] 3).testBit (j - s) := by
    cases h1 : (stepNat^[n] N).testBit j <;> cases h2 : (stepNat^[n] 3).testBit (j - s) <;>
      simp_all
  rw [this]

private theorem pairShadowed_of_data {S : Finset ℤ} {N W s B P : ℕ} (h0 : 0 ∈ S)
    (hS : ∀ x ∈ S, 0 ≤ x ∧ x < (W : ℤ)) (hN : N < 2 ^ W)
    (h : ∀ j < W, (j : ℤ) ∈ S ↔ N.testBit j = true) (hsB : s ≤ B) (hP : 0 < P)
    (hcert : shadowCertOK N s B P = true) :
    (cfgOf S).PairShadowed :=
  pairShadowed_of_nat (fullWindow_indicator_eq h0 hS hN h) hsB
    (shadow_of_cert N s B P hsB hP hcert)


/-- **Four states are shadowed by the pair**: the states with cells `0, 1, 3, 4, 6, 7`,
`0, 1, 3, 4, 9, 10`, `0, 1, 6, 7, 12, 13` and `0, 1, 3, 4, 6, 7, 9, 10, 12, 13` set, at the shifts
`0`, `3`, `0`, `0` and the bounds `10`, `23`, `19`, `16`. The difference of the windows is checked
at the steps of one period of the pair's window below the cell the difference reaches, and
shown to return, which gives the shadow at every step. -/
theorem pairShadowed_wolfram106_cells :
    ∀ S ∈ ([{0, 1, 3, 4, 6, 7}, {0, 1, 3, 4, 9, 10}, {0, 1, 6, 7, 12, 13},
        {0, 1, 3, 4, 6, 7, 9, 10, 12, 13}] : List (Finset ℤ)),
      FiniteConfiguration.PairShadowed (Finsupp.indicator S fun _ _ => (1 : ZMod 2)) := by
  intro S hS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · exact pairShadowed_of_data (N := 219) (W := 8) (s := 0) (B := 10) (P := 32)
      (by decide) (by decide) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
      (by decide +kernel)
  · exact pairShadowed_of_data (N := 1563) (W := 11) (s := 3) (B := 23) (P := 128)
      (by decide) (by decide) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
      (by decide +kernel)
  · exact pairShadowed_of_data (N := 12483) (W := 14) (s := 0) (B := 19) (P := 128)
      (by decide) (by decide) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
      (by decide +kernel)
  · exact pairShadowed_of_data (N := 14043) (W := 14) (s := 0) (B := 16) (P := 128)
      (by decide) (by decide) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
      (by decide +kernel)

private theorem diam_ge_of_mem {S : Finset ℤ} {a b : ℤ} (ha : a ∈ S) (hb : b ∈ S) :
    (b - a).toNat + 1 ≤ (cfgOf S).diam := by
  refine le_diam_of_cells ?_ ?_
  · rw [Finsupp.indicator_apply]
    simp [ha]
  · rw [Finsupp.indicator_apply]
    simp [hb]

/-- **The four states are not reproduced**: each is shadowed by the pair and wider than the pair,
so rule `106` does not reproduce it. -/
theorem not_reproduces_wolfram106_cells (hq : wolframRule 106 0 0 0 = 0) :
    ∀ S ∈ ([{0, 1, 3, 4, 6, 7}, {0, 1, 3, 4, 9, 10}, {0, 1, 6, 7, 12, 13},
        {0, 1, 3, 4, 6, 7, 9, 10, 12, 13}] : List (Finset ℤ)),
      ¬ Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator S fun _ _ => (1 : ZMod 2)) := by
  intro S hS hrep
  have hsh := pairShadowed_wolfram106_cells S hS
  have hd := (hsh.reproduces_wolfram106_iff hq).mp hrep
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · have := diam_ge_of_mem (S := {0, 1, 3, 4, 6, 7}) (a := 0) (b := 7) (by decide) (by decide)
    change (cfgOf _).diam = 2 at hd
    omega
  · have := diam_ge_of_mem (S := {0, 1, 3, 4, 9, 10}) (a := 0) (b := 10) (by decide) (by decide)
    change (cfgOf _).diam = 2 at hd
    omega
  · have := diam_ge_of_mem (S := {0, 1, 6, 7, 12, 13}) (a := 0) (b := 13) (by decide) (by decide)
    change (cfgOf _).diam = 2 at hd
    omega
  · have := diam_ge_of_mem (S := {0, 1, 3, 4, 6, 7, 9, 10, 12, 13}) (a := 0) (b := 13)
      (by decide) (by decide)
    change (cfgOf _).diam = 2 at hd
    omega


private theorem diam_cfgOf {S : Finset ℤ} {a b : ℤ} (ha : a ∈ S) (hb : b ∈ S)
    (hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b) : (cfgOf S).diam = (b - a).toNat + 1 := by
  have hne : (cfgOf S).support.Nonempty := by
    rw [support_indicator_one]
    exact ⟨a, ha⟩
  have hmax : (cfgOf S).support.max' hne = b := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      rw [support_indicator_one] at hy
      exact (hS y hy).2
    · exact Finset.le_max' _ _ (by rw [support_indicator_one]; exact hb)
  have hmin : (cfgOf S).support.min' hne = a := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (by rw [support_indicator_one]; exact ha)
    · apply Finset.le_min'
      intro y hy
      rw [support_indicator_one] at hy
      exact (hS y hy).1
  rw [diam_eq' hne, hmax, hmin]

private theorem pair_eq_cfgOf :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 : FiniteConfiguration) =
      cfgOf {0, 1} := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.indicator_apply,
    Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> first | omega | decide

/-- **Both sides of the equivalence are met**: the pair `11` is shadowed, reproduced and of
diameter `2`, and the state with cells `0, 1, 3, 4, 6, 7` set is shadowed, not reproduced and not
of diameter `2`. -/
theorem FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff_nonvacuous
    (hq : wolframRule 106 0 0 0 = 0) :
    (FiniteConfiguration.PairShadowed
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∧
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∧
      diam (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) = 2) ∧
    (FiniteConfiguration.PairShadowed
        (Finsupp.indicator ({0, 1, 3, 4, 6, 7} : Finset ℤ) fun _ _ => (1 : ZMod 2)) ∧
      ¬ Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator ({0, 1, 3, 4, 6, 7} : Finset ℤ) fun _ _ => (1 : ZMod 2)) ∧
      diam (Finsupp.indicator ({0, 1, 3, 4, 6, 7} : Finset ℤ) fun _ _ => (1 : ZMod 2)) ≠ 2) := by
  have hpair : FiniteConfiguration.PairShadowed
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) := by
    rw [pair_eq_cfgOf]
    exact pairShadowed_of_data (N := 3) (W := 2) (s := 0) (B := 0) (P := 1)
      (by decide) (by decide) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
      (by decide +kernel)
  have hrep : Reproduces (finRule (wolframRule 106) hq)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) := by
    simpa using reproduces_wolfram106_orbit hq 0
  refine ⟨⟨hpair, hrep, (hpair.reproduces_wolfram106_iff hq).mp hrep⟩,
    pairShadowed_wolfram106_cells _ (by simp),
    not_reproduces_wolfram106_cells hq _ (by simp), ?_⟩
  have h := diam_cfgOf (S := {0, 1, 3, 4, 6, 7}) (a := 0) (b := 7) (by decide) (by decide)
    (by decide)
  change (cfgOf _).diam ≠ 2
  omega

/-- **The shadow cannot be dropped**: the state with cells `0`, `1` and `2` set, the pair's image
up to translation, is reproduced, has diameter `3`, and is not shadowed by the pair. -/
theorem FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff_load_bearing
    (hq : wolframRule 106 0 0 0 = 0) :
    Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator ({0, 1, 2} : Finset ℤ) fun _ _ => (1 : ZMod 2)) ∧
      diam (Finsupp.indicator ({0, 1, 2} : Finset ℤ) fun _ _ => (1 : ZMod 2)) = 3 ∧
      ¬ FiniteConfiguration.PairShadowed
        (Finsupp.indicator ({0, 1, 2} : Finset ℤ) fun _ _ => (1 : ZMod 2)) := by
  have hrep : Reproduces (finRule (wolframRule 106) hq) (cfgOf {0, 1, 2}) := by
    have h := reproduces_wolfram106_orbit hq 1
    rw [Function.iterate_one] at h
    have h2 := Reproduces.translate (wolframRule 106) hq h 1
    have e : FiniteConfiguration.translate 1
        (finRule (wolframRule 106) hq (Finsupp.single 0 1 + Finsupp.single 1 1)) =
        cfgOf {0, 1, 2} := by
      ext x
      rw [translate_apply', finRule_apply, wolframRule106_apply]
      simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.indicator_apply,
        Finset.mem_insert, Finset.mem_singleton]
      split_ifs <;> first | omega | decide
    rw [e] at h2
    exact h2
  have hd : (cfgOf {0, 1, 2}).diam = 3 :=
    diam_cfgOf (S := {0, 1, 2}) (a := 0) (b := 2) (by decide) (by decide) (by decide)
  refine ⟨hrep, hd, fun hsh => ?_⟩
  have := (FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff hq hsh).mp hrep
  change (cfgOf {0, 1, 2}).diam = 2 at this
  omega


end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_iterate_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_iterate_eq_zero

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_iterate_eq_zero_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_iterate_eq_zero_add

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_iterate_eq_zero_add_sharp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_iterate_eq_zero_add_sharp

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_four_pow_mul_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_four_pow_mul_pair

set_option linter.style.longLine false in
/-- info: 'ECA.Copies.fullWindow_second_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Copies.fullWindow_second_copy

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.PairShadowed.reproduces_wolfram106_iff_load_bearing

set_option linter.style.longLine false in
/-- info: 'ECA.pairShadowed_wolfram106_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.pairShadowed_wolfram106_cells

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram106_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram106_cells
