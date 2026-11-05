module

public import ECA.EdgeFamilies
public import ECA.Rule110Families

/-!
# Rules `110` and `124` reproduce no pattern
([RuleSpace] §5)

The bound `PeriodicColumnsBounded (wolframRule 110) 64` of `ECA.EdgeFamilies`, by a certificate
that the kernel checks, and rules `110` and `124` reproduce no pattern with no hypothesis left.

At rule `110`, `f a 0 x = x`, `f 0 1 x = 1` and `f 1 1 x = 1 - x`. A column of a family of window
cells, driven by the two columns before it, either reads the pair `(0, 1)` at some step, after
which two solutions agree from the next step on, so two purely periodic solutions agree
everywhere, or never reads it, and then each step is the identity or a flip, so two solutions
agree everywhere or are complements everywhere. So the purely periodic families form a tree over
the column index, and the tree is finite: six families, each tabulated in `ECA.Rule110Families` as
a list of sixty-four-bit words, bit `n` of word `j` the cell `j` at step `n`, up to a column from
which it repeats itself. A tail triple `(S, τ, j₀)` says that column `j + S` is column `j` read
`τ` steps later, from column `j₀` on; a sibling triple `(j, k, τ)` says that family `k` read `τ`
steps later agrees with the family below column `j` and is its complement at column `j`.

The certificate has four decidable parts per family, decided by `decide +kernel`: column `0` is
all ones and every column obeys the recurrence on words; the tail is consistent inside the table;
every column from `j₀` on reads `(0, 1)` at some step; and every column that does not is listed
with a sibling. Rotation commutes with the rule and preserves the reading of `(0, 1)`, so the
recurrence and the reading hold at every column of the extended family, by induction on the column
from the table's last `S + 2` columns. An induction on the column then matches any purely periodic
family with a tabulated one, up to a shift, so every column has period dividing `64`.

## Main results

* `periodicColumnsBounded_wolfram110` — every purely periodic family of window cells at rule
  `110` has every column of period dividing `64`, and
  `periodicColumnsBounded_wolfram110_nonvacuous` — its hypotheses are jointly satisfiable at
  every width.
* `not_reproduces_wolfram110`, `not_reproduces_wolfram124` — rules `110` and `124` reproduce no
  pattern.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The word checks -/

/-- The all-ones word of sixty-four bits. -/
private def mask : ℕ := 2 ^ 64 - 1

/-- Rotation of a sixty-four-bit word: bit `n` of `rot w τ` is bit `(n + τ) % 64` of `w`. -/
private def rot (w τ : ℕ) : ℕ :=
  (((w &&& mask) >>> τ) ||| ((w &&& mask) <<< (64 - τ))) &&& mask

/-- Rule `110` bitwise on sixty-four-bit words: `f a b c = (b ∨ c) ∧ ¬ (a ∧ b ∧ c)`. -/
private def gW (A B C : ℕ) : ℕ := ((B ||| C) &&& (mask ^^^ (A &&& B &&& C))) &&& mask

/-- The first column in which a pair of driving words reads `(0, 1)` at some step. -/
private def mergeW (A B : ℕ) : Bool := ((mask ^^^ (A &&& mask)) &&& B &&& mask) != 0

private def tab (k : ℕ) : List ℕ := rule110Tables.getD k []
private def tailS (k : ℕ) : ℕ := (rule110Tails.getD k (0, 0, 0)).1
private def tailT (k : ℕ) : ℕ := (rule110Tails.getD k (0, 0, 0)).2.1
private def tailJ (k : ℕ) : ℕ := (rule110Tails.getD k (0, 0, 0)).2.2
private def sibs (k : ℕ) : List (ℕ × ℕ × ℕ) := rule110Siblings.getD k []
private def len (k : ℕ) : ℕ := (tab k).length
private def tabCol (k j : ℕ) : ℕ := (tab k).getD j 0
private def z2 (k j : ℕ) : ℕ := if 2 ≤ j then tabCol k (j - 2) else 0
private def z1 (k j : ℕ) : ℕ := if 1 ≤ j then tabCol k (j - 1) else 0

private def chkS (k : ℕ) : Bool :=
  decide (0 < tailS k) && decide (tailT k < 64) &&
    decide (tailJ k + tailS k + 2 ≤ len k)

private def chkA (k : ℕ) : Bool :=
  (tabCol k 0 == mask) &&
    (List.range (len k)).all fun j => rot (tabCol k j) 1 == gW (z2 k j) (z1 k j) (tabCol k j)

private def chkB (k : ℕ) : Bool :=
  (List.range (len k)).all fun j =>
    decide (j < tailJ k) || decide (len k ≤ j + tailS k) ||
      ((tabCol k (j + tailS k) &&& mask) == rot (tabCol k j) (tailT k))

private def chkC (k : ℕ) : Bool :=
  (List.range (len k)).all fun j => decide (j < tailJ k) || mergeW (z2 k j) (z1 k j)

private def sibOK (k j k' τ' : ℕ) : Bool :=
  decide (k' < 6) && decide (j < len k') && decide (τ' < 64) &&
    (List.range j).all (fun i => rot (tabCol k' i) τ' == (tabCol k i &&& mask)) &&
    (rot (tabCol k' j) τ' == (mask ^^^ (tabCol k j &&& mask)))

private def chkD (k : ℕ) : Bool :=
  (List.range (len k)).all fun j => decide (j = 0) || mergeW (z2 k j) (z1 k j) ||
    (sibs k).any fun s => (s.1 == j) && sibOK k j s.2.1 s.2.2

private def chk (k : ℕ) : Bool := chkS k && chkA k && chkB k && chkC k && chkD k

private theorem chk_zero : chk 0 = true := by decide +kernel
private theorem chk_one : chk 1 = true := by decide +kernel
private theorem chk_two : chk 2 = true := by decide +kernel
private theorem chk_three : chk 3 = true := by decide +kernel
private theorem chk_four : chk 4 = true := by decide +kernel
private theorem chk_five : chk 5 = true := by decide +kernel

/-! ## Bits of the words -/

private theorem testBit_mask (i : ℕ) : mask.testBit i = decide (i < 64) := by
  unfold mask
  simpa using Nat.testBit_two_pow_sub_one 64 i

/-- Rule `110` on bits: `f a b c = (b ∨ c) ∧ ¬ (a ∧ b ∧ c)`. -/
private def fb (a b c : Bool) : Bool := (b || c) && !(a && b && c)

private theorem rot_testBit {w τ m : ℕ} (hτ : τ < 64) (hm : m < 64) :
    (rot w τ).testBit m = w.testBit ((m + τ) % 64) := by
  unfold rot
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    testBit_mask]
  by_cases h : m + τ < 64
  · have e : (m + τ) % 64 = τ + m := by omega
    have h1 : ¬ (64 - τ ≤ m) := by omega
    have h2 : τ + m < 64 := by omega
    simp [e, h1, h2, hm]
  · have e : (m + τ) % 64 = m - (64 - τ) := by omega
    have h1 : 64 - τ ≤ m := by omega
    have h2 : ¬ (τ + m < 64) := by omega
    have h3 : m - (64 - τ) < 64 := by omega
    simp [e, h1, h2, h3, hm]

private theorem gW_testBit {A B C m : ℕ} (hm : m < 64) :
    (gW A B C).testBit m = fb (A.testBit m) (B.testBit m) (C.testBit m) := by
  simp only [gW, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, testBit_mask, hm,
    decide_true, Bool.and_true]
  cases A.testBit m <;> cases B.testBit m <;> cases C.testBit m <;> simp [fb]

private theorem mergeW_spec {A B : ℕ} (h : mergeW A B = true) :
    ∃ m < 64, A.testBit m = false ∧ B.testBit m = true := by
  unfold mergeW at h
  have h' : (mask ^^^ (A &&& mask)) &&& B &&& mask ≠ 0 := by simpa using h
  obtain ⟨m, hm⟩ : ∃ m, ((mask ^^^ (A &&& mask)) &&& B &&& mask).testBit m = true := by
    by_contra hne
    push Not at hne
    exact h' (Nat.eq_of_testBit_eq fun i => by simpa using hne i)
  simp only [Nat.testBit_and, Nat.testBit_xor, testBit_mask] at hm
  have hm64 : m < 64 := by
    by_contra hc
    simp [hc] at hm
  have hm' : A.testBit m = false ∧ B.testBit m = true := by simpa [hm64] using hm
  exact ⟨m, hm64, hm'.1, hm'.2⟩

/-- The bit at step `n` of a word read with period `64`. -/
private def btn (w n : ℕ) : Bool := w.testBit (n % 64)

private theorem btn_add_mul (w n c : ℕ) : btn w (n + 64 * c) = btn w n := by
  simp [btn, Nat.add_mul_mod_self_left]

private theorem btn_rot {w τ : ℕ} (n : ℕ) (hτ : τ < 64) : btn (rot w τ) n = btn w (n + τ) := by
  unfold btn
  rw [rot_testBit hτ (Nat.mod_lt _ (by norm_num))]
  congr 1
  omega

private theorem btn_and_mask (w n : ℕ) : btn (w &&& mask) n = btn w n := by
  simp [btn, Nat.testBit_and, testBit_mask, Nat.mod_lt _ (by norm_num : 0 < 64)]

private theorem btn_gW (A B C n : ℕ) :
    btn (gW A B C) n = fb (btn A n) (btn B n) (btn C n) :=
  gW_testBit (Nat.mod_lt _ (by norm_num))

private theorem btn_zero (n : ℕ) : btn 0 n = false := by simp [btn]

/-! ## The extended columns -/

/-- Column `j` of the family `k`: the table's column below its length, and the column `tailS k`
places before it, rotated by `tailT k`, beyond. -/
private def ext (k j : ℕ) : ℕ :=
  if _h : j < len k ∨ j = 0 ∨ tailS k = 0 then tabCol k j
  else rot (ext k (j - tailS k)) (tailT k)
termination_by j
decreasing_by omega

private theorem ext_of_lt {k j : ℕ} (h : j < len k) : ext k j = tabCol k j := by
  rw [ext]; simp [h]

private theorem ext_of_ge {k j : ℕ} (h1 : len k ≤ j) (h2 : j ≠ 0) (h3 : tailS k ≠ 0) :
    ext k j = rot (ext k (j - tailS k)) (tailT k) := by
  have hn : ¬ (j < len k ∨ j = 0 ∨ tailS k = 0) := by omega
  rw [ext]; simp only [hn, ↓reduceDIte]

private def bx (k j n : ℕ) : Bool := btn (ext k j) n
private def bz2 (k j n : ℕ) : Bool := if 2 ≤ j then bx k (j - 2) n else false
private def bz1 (k j n : ℕ) : Bool := if 1 ≤ j then bx k (j - 1) n else false

private theorem chk_facts {k : ℕ} (hk : chk k = true) :
    0 < tailS k ∧ tailT k < 64 ∧ tailJ k + tailS k + 2 ≤ len k := by
  unfold chk at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨hS, _⟩, _⟩, _⟩, _⟩ := hk
  simpa [chkS, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hS

private theorem chk_A {k : ℕ} (hk : chk k = true) : chkA k = true := by
  unfold chk at hk
  simp only [Bool.and_eq_true] at hk
  exact hk.1.1.1.2

private theorem chk_B {k : ℕ} (hk : chk k = true) : chkB k = true := by
  unfold chk at hk
  simp only [Bool.and_eq_true] at hk
  exact hk.1.1.2

private theorem chk_C {k : ℕ} (hk : chk k = true) : chkC k = true := by
  unfold chk at hk
  simp only [Bool.and_eq_true] at hk
  exact hk.1.2

private theorem chk_D {k : ℕ} (hk : chk k = true) : chkD k = true := by
  unfold chk at hk
  simp only [Bool.and_eq_true] at hk
  exact hk.2

private theorem bx_periodic (k j n c : ℕ) : bx k j (n + 64 * c) = bx k j n := btn_add_mul _ _ _

private theorem bz2_periodic (k j n c : ℕ) : bz2 k j (n + 64 * c) = bz2 k j n := by
  unfold bz2; split_ifs <;> simp [bx_periodic]

private theorem bz1_periodic (k j n c : ℕ) : bz1 k j (n + 64 * c) = bz1 k j n := by
  unfold bz1; split_ifs <;> simp [bx_periodic]

private theorem bx_tail {k : ℕ} (hk : chk k = true) {i : ℕ} (hi : tailJ k ≤ i) (n : ℕ) :
    bx k (i + tailS k) n = bx k i (n + tailT k) := by
  obtain ⟨hS, hT, hL⟩ := chk_facts hk
  unfold bx
  by_cases h : i + tailS k < len k
  · rw [ext_of_lt h, ext_of_lt (by omega)]
    have hB := chk_B hk
    unfold chkB at hB
    rw [List.all_eq_true] at hB
    have := hB i (List.mem_range.2 (by omega))
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    rcases this with (h1 | h1) | h1
    · omega
    · omega
    · rw [← btn_and_mask, h1, btn_rot _ hT]
  · rw [ext_of_ge (by omega) (by omega) (by omega), Nat.add_sub_cancel, btn_rot _ hT]

private theorem bz2_tail {k : ℕ} (hk : chk k = true) {i : ℕ} (hi : tailJ k + 2 ≤ i) (n : ℕ) :
    bz2 k (i + tailS k) n = bz2 k i (n + tailT k) := by
  obtain ⟨hS, hT, hL⟩ := chk_facts hk
  unfold bz2
  have h1 : 2 ≤ i + tailS k := by omega
  have h2 : 2 ≤ i := by omega
  simp only [h1, h2, ↓reduceIte]
  have : i + tailS k - 2 = (i - 2) + tailS k := by omega
  rw [this, bx_tail hk (by omega)]

private theorem bz1_tail {k : ℕ} (hk : chk k = true) {i : ℕ} (hi : tailJ k + 1 ≤ i) (n : ℕ) :
    bz1 k (i + tailS k) n = bz1 k i (n + tailT k) := by
  obtain ⟨hS, hT, hL⟩ := chk_facts hk
  unfold bz1
  have h1 : 1 ≤ i + tailS k := by omega
  have h2 : 1 ≤ i := by omega
  simp only [h1, h2, ↓reduceIte]
  have : i + tailS k - 1 = (i - 1) + tailS k := by omega
  rw [this, bx_tail hk (by omega)]

private theorem btn_z2 {k j : ℕ} (hj : j < len k) (n : ℕ) : btn (z2 k j) n = bz2 k j n := by
  unfold z2 bz2
  split_ifs
  · unfold bx; rw [ext_of_lt (by omega)]
  · exact btn_zero n

private theorem btn_z1 {k j : ℕ} (hj : j < len k) (n : ℕ) : btn (z1 k j) n = bz1 k j n := by
  unfold z1 bz1
  split_ifs
  · unfold bx; rw [ext_of_lt (by omega)]
  · exact btn_zero n

/-- The recurrence on the bits of every column of the extended family. -/
private theorem bx_rec {k : ℕ} (hk : chk k = true) (j : ℕ) :
    ∀ n, bx k j (n + 1) = fb (bz2 k j n) (bz1 k j n) (bx k j n) := by
  obtain ⟨hS, hT, hL⟩ := chk_facts hk
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro n
    by_cases hj : j < len k
    · have hA := chk_A hk
      unfold chkA at hA
      rw [Bool.and_eq_true, List.all_eq_true] at hA
      have := hA.2 j (List.mem_range.2 hj)
      rw [beq_iff_eq] at this
      have h2 := congrArg (fun w => btn w n) this
      simp only [btn_rot _ (by norm_num : 1 < 64), btn_gW, btn_z2 hj, btn_z1 hj] at h2
      unfold bx
      rw [ext_of_lt hj]
      exact h2
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + tailS k := ⟨j - tailS k, by omega⟩
      have hi : tailJ k + 2 ≤ i := by omega
      have := ih i (by omega) (n + tailT k)
      rw [bx_tail hk (by omega), bz2_tail hk hi, bz1_tail hk (by omega), bx_tail hk (by omega)]
      rw [show n + 1 + tailT k = n + tailT k + 1 by omega]
      exact this

/-- From the column `tailJ k` on, some step of every column reads `(0, 1)` in its drivers. -/
private def MB (k j : ℕ) : Prop := ∃ n, bz2 k j n = false ∧ bz1 k j n = true

private theorem mb_of_mergeW {k j : ℕ} (hj : j < len k) (h : mergeW (z2 k j) (z1 k j) = true) :
    MB k j := by
  obtain ⟨m, _, h1, h2⟩ := mergeW_spec h
  refine ⟨m, ?_, ?_⟩
  · rw [← btn_z2 hj]; simpa [btn, Nat.mod_eq_of_lt ‹m < 64›] using h1
  · rw [← btn_z1 hj]; simpa [btn, Nat.mod_eq_of_lt ‹m < 64›] using h2

private theorem mb_all {k : ℕ} (hk : chk k = true) (j : ℕ) (hj : tailJ k ≤ j) : MB k j := by
  obtain ⟨hS, hT, hL⟩ := chk_facts hk
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hjl : j < len k
    · have hC := chk_C hk
      unfold chkC at hC
      rw [List.all_eq_true] at hC
      have := hC j (List.mem_range.2 hjl)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · omega
      · exact mb_of_mergeW hjl h
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + tailS k := ⟨j - tailS k, by omega⟩
      obtain ⟨n0, h0, h1⟩ := ih i (by omega) (by omega)
      refine ⟨n0 + 63 * tailT k, ?_, ?_⟩
      · rw [bz2_tail hk (by omega), show n0 + 63 * tailT k + tailT k = n0 + 64 * tailT k by ring,
          bz2_periodic, h0]
      · rw [bz1_tail hk (by omega), show n0 + 63 * tailT k + tailT k = n0 + 64 * tailT k by ring,
          bz1_periodic, h1]

/-! ## The sibling of a column that does not merge -/

/-- A sibling of the column `j` of the family `k`: a family `k'` read `τ'` steps later that agrees
with it below the column and is its complement at the column. -/
private def Sib (k j : ℕ) : Prop :=
  ∃ k' < 6, ∃ τ', ∀ n, (∀ i < j, bx k' i (n + τ') = bx k i n) ∧ bx k' j (n + τ') = !bx k j n

private theorem sib_of_sibOK {k j k' τ' : ℕ} (hj : j < len k) (h : sibOK k j k' τ' = true) :
    Sib k j := by
  unfold sibOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hk', hjl⟩, hτ⟩, hall⟩, hlast⟩ := h
  refine ⟨k', hk', τ', fun n => ⟨fun i hi => ?_, ?_⟩⟩
  · unfold bx
    rw [ext_of_lt (by omega), ext_of_lt (by omega), ← btn_rot n hτ, hall i hi, btn_and_mask]
  · unfold bx
    rw [ext_of_lt hjl, ext_of_lt hj, ← btn_rot n hτ, hlast]
    unfold btn
    simp [Nat.testBit_xor, Nat.testBit_and, testBit_mask, Nat.mod_lt _ (by norm_num : 0 < 64)]

private theorem mb_or_sib {k : ℕ} (hk : chk k = true) {j : ℕ} (hj : 1 ≤ j) :
    MB k j ∨ Sib k j := by
  obtain ⟨hS, hT, hL⟩ := chk_facts hk
  by_cases hjl : j < len k
  · have hD := chk_D hk
    unfold chkD at hD
    rw [List.all_eq_true] at hD
    have := hD j (List.mem_range.2 hjl)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with (h | h) | h
    · omega
    · exact Or.inl (mb_of_mergeW hjl h)
    · obtain ⟨s, _, hs⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true] at hs
      exact Or.inr (sib_of_sibOK hjl hs.2)
  · exact Or.inl (mb_all hk j (by omega))

/-! ## Rule `110` on `ZMod 2` -/

/-- A Boolean as an element of `ZMod 2`. -/
private def zb (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem rule110_zb (a b c : Bool) :
    wolframRule 110 (zb a) (zb b) (zb c) = zb (fb a b c) := by
  cases a <;> cases b <;> cases c <;> decide +kernel

private theorem zb_not (b : Bool) : zb (!b) = zb b + 1 := by
  cases b <;> decide +kernel

private theorem rule110_zero_zero (x : ZMod 2) : wolframRule 110 0 0 x = x := by
  revert x; decide +kernel

private theorem rule110_zero_one (x : ZMod 2) : wolframRule 110 0 1 x = 1 := by
  revert x; decide +kernel

private theorem rule110_inv (a b x y : ZMod 2) (h : ¬ (a = 0 ∧ b = 1)) :
    wolframRule 110 a b x + wolframRule 110 a b y = x + y := by
  revert a b x y; decide +kernel

/-! ## Two periodic solutions of one driven recurrence -/

/-- Two solutions of one driven recurrence, one periodic of period `t` and the other of period
`64`, agree everywhere when the drivers read `(0, 1)` at some step. -/
private theorem solutions_agree {x y a b : ℕ → ZMod 2} {t σ : ℕ} (ht : 0 < t)
    (hx : ∀ n, x (n + 1) = wolframRule 110 (a n) (b n) (x n))
    (hy : ∀ n, y (n + 1) = wolframRule 110 (a n) (b n) (y n))
    (hxp : ∀ n, x (n + t) = x n) (hyp : ∀ n, y (n + 64) = y n)
    (ha : a σ = 0) (hb : b σ = 1) : ∀ n, x n = y n := by
  have hag : ∀ m, σ + 1 ≤ m → x m = y m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rw [hx σ, hy σ, ha, hb, rule110_zero_one, rule110_zero_one]
    | succ m _ ih => rw [hx m, hy m, ih]
  have hxq : ∀ c n, x (n + c * t) = x n := by
    intro c
    induction c with
    | zero => intro n; simp
    | succ c ih => intro n; rw [Nat.succ_mul, ← Nat.add_assoc, hxp, ih]
  have hyq : ∀ c n, y (n + c * 64) = y n := by
    intro c
    induction c with
    | zero => intro n; simp
    | succ c ih => intro n; rw [Nat.succ_mul, ← Nat.add_assoc, hyp, ih]
  intro n
  have h1 : σ + 1 ≤ n + (64 * (σ + 1)) * t := by nlinarith
  have h2 := hag _ h1
  rw [hxq] at h2
  rw [show n + (64 * (σ + 1)) * t = n + (t * (σ + 1)) * 64 by ring, hyq] at h2
  exact h2

/-- Two solutions of one driven recurrence whose drivers never read `(0, 1)` differ by a
constant. -/
private theorem solutions_differ {x y a b : ℕ → ZMod 2}
    (hx : ∀ n, x (n + 1) = wolframRule 110 (a n) (b n) (x n))
    (hy : ∀ n, y (n + 1) = wolframRule 110 (a n) (b n) (y n))
    (hab : ∀ n, ¬ (a n = 0 ∧ b n = 1)) : ∀ n, x n + y n = x 0 + y 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [hx n, hy n, rule110_inv _ _ _ _ (hab n), ih]

/-! ## The families of a purely periodic window -/

private theorem exists_family (hk6 : ∀ k < 6, chk k = true) {e : ℕ → ℕ → ZMod 2} {W t : ℕ}
    (hrec : ∀ n j, j < W → e (n + 1) j = wolframRule 110
      (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j))
    (h0 : e 0 0 = 1) (ht : 0 < t) (hper : ∀ n j, j < W → e (n + t) j = e n j) :
    ∀ j, j < W → ∃ k < 6, ∃ τ, ∀ n, ∀ i ≤ j, e n i = zb (bx k i (n + τ)) := by
  intro j
  induction j with
  | zero =>
    intro hW
    have hcol : ∀ n, e n 0 = 1 := by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih =>
        rw [hrec n 0 hW]
        simpa [rule110_zero_zero] using ih
    refine ⟨0, by norm_num, 0, fun n i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    rw [hcol n]
    have hA := chk_A (hk6 0 (by norm_num))
    unfold chkA at hA
    rw [Bool.and_eq_true, beq_iff_eq] at hA
    unfold bx btn
    rw [ext_of_lt (by have := chk_facts (hk6 0 (by norm_num)); omega), hA.1, testBit_mask]
    simp [zb, Nat.mod_lt _ (by norm_num : 0 < 64)]
  | succ j ih =>
    intro hW
    obtain ⟨k, hk, τ, hfam⟩ := ih (by omega)
    have hck := hk6 k hk
    -- the drivers of the column `j + 1`, as the family's
    have hA : ∀ n, (if 2 ≤ j + 1 then e n (j + 1 - 2) else 0) = zb (bz2 k (j + 1) (n + τ)) := by
      intro n
      by_cases h2 : 2 ≤ j + 1
      · simp only [h2, ↓reduceIte, bz2]
        exact hfam n _ (by omega)
      · simp [h2, bz2, zb]
    have hB : ∀ n, (if 1 ≤ j + 1 then e n (j + 1 - 1) else 0) = zb (bz1 k (j + 1) (n + τ)) := by
      intro n
      simp only [bz1, show 1 ≤ j + 1 by omega, ↓reduceIte]
      exact hfam n _ (by omega)
    have hx : ∀ n, e (n + 1) (j + 1) = wolframRule 110 (zb (bz2 k (j + 1) (n + τ)))
        (zb (bz1 k (j + 1) (n + τ))) (e n (j + 1)) := by
      intro n
      rw [hrec n (j + 1) hW, hA n, hB n]
    have hy : ∀ n, zb (bx k (j + 1) (n + 1 + τ)) = wolframRule 110 (zb (bz2 k (j + 1) (n + τ)))
        (zb (bz1 k (j + 1) (n + τ))) (zb (bx k (j + 1) (n + τ))) := by
      intro n
      rw [rule110_zb, show n + 1 + τ = (n + τ) + 1 by omega, bx_rec hck]
    by_cases hM : ∃ σ, zb (bz2 k (j + 1) (σ + τ)) = 0 ∧ zb (bz1 k (j + 1) (σ + τ)) = 1
    · obtain ⟨σ, hσ1, hσ2⟩ := hM
      have hag := solutions_agree (x := fun n => e n (j + 1))
        (y := fun n => zb (bx k (j + 1) (n + τ)))
        (a := fun n => zb (bz2 k (j + 1) (n + τ))) (b := fun n => zb (bz1 k (j + 1) (n + τ)))
        ht hx (fun n => by simpa using hy n) (fun n => hper n (j + 1) hW)
        (fun n => by
          show zb (bx k (j + 1) (n + 64 + τ)) = _
          rw [show n + 64 + τ = (n + τ) + 64 * 1 by ring, bx_periodic])
        hσ1 hσ2
      refine ⟨k, hk, τ, fun n i hi => ?_⟩
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact hfam n i (by omega)
      · obtain rfl : i = j + 1 := by omega
        exact hag n
    · push Not at hM
      have hnm : ∀ n, ¬ (zb (bz2 k (j + 1) (n + τ)) = 0 ∧ zb (bz1 k (j + 1) (n + τ)) = 1) :=
        fun n h => hM n h.1 h.2
      have hdiff := solutions_differ (x := fun n => e n (j + 1))
        (y := fun n => zb (bx k (j + 1) (n + τ)))
        (a := fun n => zb (bz2 k (j + 1) (n + τ))) (b := fun n => zb (bz1 k (j + 1) (n + τ)))
        hx (fun n => by simpa using hy n) hnm
      rcases mb_or_sib hck (by omega : 1 ≤ j + 1) with ⟨n0, h1, h2⟩ | ⟨k', hk', τ', hsib⟩
      · exfalso
        apply hnm (n0 + 63 * τ)
        rw [show n0 + 63 * τ + τ = n0 + 64 * τ by ring, bz2_periodic, bz1_periodic, h1, h2]
        simp [zb]
      · by_cases hc : e 0 (j + 1) + zb (bx k (j + 1) (0 + τ)) = 0
        · refine ⟨k, hk, τ, fun n i hi => ?_⟩
          rcases Nat.lt_or_ge i (j + 1) with h | h
          · exact hfam n i (by omega)
          · obtain rfl : i = j + 1 := by omega
            have := hdiff n
            simp only [hc] at this
            have h3 : e n (j + 1) = zb (bx k (j + 1) (n + τ)) := by
              have h4 : e n (j + 1) + zb (bx k (j + 1) (n + τ)) = 0 := this
              exact (eq_neg_of_add_eq_zero_left h4).trans (by
                generalize zb (bx k (j + 1) (n + τ)) = z; revert z; decide +kernel)
            exact h3
        · refine ⟨k', hk', τ + τ', fun n i hi => ?_⟩
          rcases Nat.lt_or_ge i (j + 1) with h | h
          · rw [hfam n i (by omega), ← add_assoc, ← (hsib (n + τ)).1 i h]
          · obtain rfl : i = j + 1 := by omega
            have h5 := hdiff n
            have hc1 : e 0 (j + 1) + zb (bx k (j + 1) (0 + τ)) = 1 := by
              generalize e 0 (j + 1) + zb (bx k (j + 1) (0 + τ)) = z at hc ⊢
              revert z; decide +kernel
            simp only [hc1] at h5
            rw [← add_assoc, (hsib (n + τ)).2, zb_not]
            have h6 : e n (j + 1) + zb (bx k (j + 1) (n + τ)) = 1 := h5
            generalize e n (j + 1) = u at h6 ⊢
            generalize zb (bx k (j + 1) (n + τ)) = v at h6 ⊢
            revert u v; decide +kernel

private theorem chk_all : ∀ k < 6, chk k = true := by
  intro k hk
  interval_cases k
  exacts [chk_zero, chk_one, chk_two, chk_three, chk_four, chk_five]

private theorem bx_zero {k : ℕ} (hk : chk k = true) (n : ℕ) : bx k 0 n = true := by
  have hA := chk_A hk
  unfold chkA at hA
  rw [Bool.and_eq_true, beq_iff_eq] at hA
  unfold bx btn
  rw [ext_of_lt (by have := chk_facts hk; omega), hA.1, testBit_mask]
  simp [Nat.mod_lt _ (by norm_num : 0 < 64)]

/-! ## The bound -/

/-- **Every purely periodic family of window cells at rule `110` has every column of period
dividing `64`** ([RuleSpace] §5). Along a family of window cells that obeys the recurrence and is
purely periodic, a column driven by two others either reads the pair `(0, 1)` at some step, after
which a periodic column is determined, or reads it never and then is the same column or its
complement. The families are therefore the finitely many tabulated in the data module, each
shift-symmetric from some column on, and the kernel checks the tables. -/
theorem periodicColumnsBounded_wolfram110 : PeriodicColumnsBounded (wolframRule 110) 64 := by
  intro e W t hrec h0 ht hper n j hj
  obtain ⟨k, _, τ, h⟩ := exists_family chk_all hrec h0 ht hper j hj
  rw [h n j le_rfl, h (n + 64) j le_rfl, show n + 64 + τ = (n + τ) + 64 * 1 by ring,
    bx_periodic]

/-- **The hypotheses of the bound are jointly satisfiable** at every width: the first tabulated
family is a purely periodic family of window cells with its first cell set. -/
theorem periodicColumnsBounded_wolfram110_nonvacuous (W : ℕ) :
    ∃ (e : ℕ → ℕ → ZMod 2) (t : ℕ),
      (∀ n j, j < W → e (n + 1) j = wolframRule 110
        (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) ∧
      e 0 0 = 1 ∧ 0 < t ∧ (∀ n j, j < W → e (n + t) j = e n j) := by
  have hck := chk_all 0 (by norm_num)
  refine ⟨fun n j => zb (bx 0 j n), 64, ?_, ?_, by norm_num, ?_⟩
  · intro n j _
    simp only
    have h2 : (if 2 ≤ j then zb (bx 0 (j - 2) n) else 0) = zb (bz2 0 j n) := by
      unfold bz2; split_ifs <;> simp [zb]
    have h1 : (if 1 ≤ j then zb (bx 0 (j - 1) n) else 0) = zb (bz1 0 j n) := by
      unfold bz1; split_ifs <;> simp [zb]
    rw [h2, h1, rule110_zb, bx_rec hck]
  · simp [bx_zero hck, zb]
  · intro n j _
    simp only
    rw [show n + 64 = n + 64 * 1 by ring, bx_periodic]

/-- **Rule `110` reproduces no pattern** ([RuleSpace] §5). -/
theorem not_reproduces_wolfram110 :
    ∀ (hq : wolframRule 110 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 110) hq) p :=
  not_reproduces_wolfram110_of_bounded periodicColumnsBounded_wolfram110

/-- **Rule `124` reproduces no pattern** ([RuleSpace] §5), by reflection from rule `110`. -/
theorem not_reproduces_wolfram124 :
    ∀ (hq : wolframRule 124 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 124) hq) p :=
  not_reproduces_wolfram124_of_bounded periodicColumnsBounded_wolfram110

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsBounded_wolfram110' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsBounded_wolfram110

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsBounded_wolfram110_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsBounded_wolfram110_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram110' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram110

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram124' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram124
