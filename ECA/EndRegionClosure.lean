module

public import ECA.EndRegionCert
public import ECA.PersistentWordCount
public import ECA.Growth
public import Mathlib.Tactic.IntervalCases

/-!
# The end-region closure

Extends [RuleSpace] §6, Proposition 6.1 (row RS-10) and the count of its class (row RS-26).
At twelve radius-one rules outside the class of those rows — `24, 38, 46, 52, 66, 116, 139, 155,
189, 209, 211, 231` — no state of the line erases within `2` at any scale, so the proposition's
conclusion holds there vacuously, and the class counts `164`.

The argument follows the last five cells of the window of the scale-`τ` value at a cell. Flipping a
pattern of them changes, at time `t`, only a region of five cells that moves one cell left a step,
read through two context cells that no flip reaches; at time `τ - 1` the value at the cell is the
rule at the region's last three cells. A **certificate** is a finite list of region maps, each
encoded as thirty-two five-bit words in a natural number, that holds every base map and is closed
under the step up to relabeling of the flip pattern, and whose members are all **good**: at every
pattern, some flip of at most two cells changes the apex. `certOK` checks a list by evaluation on
natural numbers, so the kernel decides it.

## Main results

* `not_erasesWithin_two_of_certOK` — a passing certificate at a rule means no state erases within
  `2` at any scale.
* `certOK_38`, `certOK_46`, `certOK_66`, `certOK_139`, `certOK_155`, `certOK_189` — the six
  certificates pass, by kernel evaluation; `certOK_refuses_128` — the check is load-bearing.
* `erasesWithin_iterate_mirrorRule` — reflecting the line reflects erasure; the other six rules
  are mirrors.
* `not_erasesWithin_two_of_mem_endClosureRules`,
  `LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure` — the twelve
  rules and the conclusion over the extended class.
* `card_forcingClass_or_endClosure` — the extended class has `164` members.
* `not_erasesWithin_two_of_certOK_nonvacuous`,
  `LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure_nonvacuous` —
  joint satisfiability witnesses.
-/

@[expose] public section

namespace ECA

open Configuration LocalRule

/-- The bit of a Boolean as a natural number. -/
def bitN (p : Bool) : ℕ := cond p 1 0

/-- The five-bit word at pattern `s` of a region map `H`, sitting at bits `5 s .. 5 s + 4`. -/
def word (H s : ℕ) : ℕ := (H >>> (5 * s)) &&& 31

/-- The partial assembly of a region map from a word function, over the patterns `< m`. -/
def mkPart (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => mkPart g m ||| ((g m &&& 31) <<< (5 * m))

/-- The region map assembled from a word function over the thirty-two patterns. -/
def mkMap (g : ℕ → ℕ) : ℕ := mkPart g 32

/-- One step of the region under a context pair: `b` is the cell two left of the region and
`a` the cell one left, the region word `w` has index `4` the last cell of the window. -/
def stepCode (tf b a w : ℕ) : ℕ :=
  let w0 := bitN (w.testBit 0)
  let w1 := bitN (w.testBit 1)
  let w2 := bitN (w.testBit 2)
  let w3 := bitN (w.testBit 3)
  let w4 := bitN (w.testBit 4)
  bitN (tf.testBit (4 * b + 2 * a + w0)) ||| (bitN (tf.testBit (4 * a + 2 * w0 + w1)) <<< 1) |||
    (bitN (tf.testBit (4 * w0 + 2 * w1 + w2)) <<< 2) |||
    (bitN (tf.testBit (4 * w1 + 2 * w2 + w3)) <<< 3) |||
    (bitN (tf.testBit (4 * w2 + 2 * w3 + w4)) <<< 4)

/-- The step of a region map under a context pair. -/
def stepMap (tf b a H : ℕ) : ℕ := mkMap fun s => stepCode tf b a (word H s)

/-- The apex of a region word: the rule at its last three cells. -/
def apex (tf w : ℕ) : Bool := tf.testBit (4 * bitN (w.testBit 2) + 2 * bitN (w.testBit 3) +
  bitN (w.testBit 4))

/-- The flip patterns of weight at most two on five cells. -/
def twoBall : List ℕ := [1, 2, 4, 8, 16, 3, 5, 9, 17, 6, 10, 18, 12, 20, 24]

/-- A region map is good when every pattern has a flip of weight at most two changing the apex. -/
def goodMap (tf H : ℕ) : Bool :=
  (List.range 32).all fun s => twoBall.any fun d => apex tf (word H (s ^^^ d)) != apex tf (word H s)

/-- Relabeling of the flip patterns of a region map by `u`. -/
def relabel (H u : ℕ) : ℕ := mkMap fun s => word H (s ^^^ u)

/-- Membership in the list up to relabeling. -/
def inCert (L : List ℕ) (H : ℕ) : Bool := (List.range 32).any fun u => L.elem (relabel H u)

/-- The certificate check: the list holds every base map up to relabeling, only good maps, and
is closed under the step under all four context pairs. -/
def certOK (tf : ℕ) (L : List ℕ) : Bool :=
  (List.range 32).all (fun b => inCert L (mkMap fun s => b ^^^ s)) &&
  L.all fun H => goodMap tf H && (List.range 4).all fun c => inCert L (stepMap tf (c / 2) (c % 2) H)

/-! ## Bit-level facts -/

private theorem testBit_31 (j : ℕ) : (31 : ℕ).testBit j = decide (j < 5) := by
  have := Nat.testBit_two_pow_sub_one 5 j
  simpa using this

/-- The partial assembly reads off the words it was built from. -/
private theorem mkPart_testBit (g : ℕ → ℕ) (m k : ℕ) :
    (mkPart g m).testBit k = (decide (k < 5 * m) && (g (k / 5)).testBit (k % 5)) := by
  induction m with
  | zero => simp [mkPart]
  | succ m ih =>
    simp only [mkPart, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, testBit_31, ih]
    rcases Nat.lt_or_ge k (5 * m) with h | h
    · have h1 : ¬ (5 * m ≤ k) := by omega
      have h2 : k < 5 * (m + 1) := by omega
      simp [h, h1, h2]
    · rcases Nat.lt_or_ge k (5 * m + 5) with h' | h'
      · have e1 : k / 5 = m := by omega
        have e2 : k % 5 = k - 5 * m := by omega
        have h1 : ¬ (k < 5 * m) := by omega
        have h2 : k < 5 * (m + 1) := by omega
        have h3 : k - 5 * m < 5 := by omega
        simp [h1, h2, h3, e1, e2, h]
      · have h1 : ¬ (k < 5 * m) := by omega
        have h2 : ¬ (k < 5 * (m + 1)) := by omega
        have h3 : ¬ (k - 5 * m < 5) := by omega
        simp [h1, h2, h3]

private theorem word_lt (H s : ℕ) : word H s < 32 := by
  have : word H s < 2 ^ 5 := Nat.and_lt_two_pow _ (by norm_num)
  simpa using this

private theorem word_and (H s : ℕ) : word H s &&& 31 = word H s := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, testBit_31]
  by_cases h : j < 5
  · simp [h]
  · have : (word H s).testBit j = false := by
      apply Nat.testBit_lt_two_pow
      calc word H s < 2 ^ 5 := by simpa using word_lt H s
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [h, this]

/-- The word at a pattern of an assembled map is the assembling word, for patterns below
thirty-two. -/
theorem word_mkMap (g : ℕ → ℕ) {s : ℕ} (hs : s < 32) : word (mkMap g) s = g s &&& 31 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [word, mkMap, Nat.testBit_and, Nat.testBit_shiftRight, testBit_31,
    mkPart_testBit]
  by_cases hj : j < 5
  · have e1 : (5 * s + j) / 5 = s := by omega
    have e2 : (5 * s + j) % 5 = j := by omega
    have h1 : 5 * s + j < 5 * 32 := by omega
    simp [e1, e2, h1, hj]
  · simp [hj]

private theorem mkPart_congr (g g' : ℕ → ℕ) (m : ℕ) (h : ∀ s < m, g s &&& 31 = g' s &&& 31) :
    mkPart g m = mkPart g' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [mkPart]
    rw [ih (fun s hs => h s (by omega)), h m (by omega)]

/-- An assembled map depends on its word function only through the five low bits at the
thirty-two patterns. -/
theorem mkMap_congr (g g' : ℕ → ℕ) (h : ∀ s < 32, g s &&& 31 = g' s &&& 31) :
    mkMap g = mkMap g' := mkPart_congr g g' 32 h

/-! ## The step and relabeling -/

/-- The cell read at index `j` of the context row `b, a, w₀, …, w₄`. -/
def ctxCell (b a w : ℕ) : ℕ → ℕ
  | 0 => b
  | 1 => a
  | k + 2 => bitN (w.testBit k)

private theorem and_31_of_lt {n : ℕ} (h : n < 32) : n &&& 31 = n := by
  have := Nat.and_two_pow_sub_one_eq_mod n 5
  simpa [Nat.mod_eq_of_lt h] using this

private theorem stepCode_lt (tf b a w : ℕ) : stepCode tf b a w < 32 := by
  have h : ∀ (p : Bool) (i : ℕ), i < 5 → bitN p <<< i < 2 ^ 5 := by
    intro p i hi
    interval_cases i <;> cases p <;> simp [bitN]
  suffices h5 : stepCode tf b a w < 2 ^ 5 by simpa using h5
  unfold stepCode
  simp only
  refine Nat.or_lt_two_pow
    (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ ?_) ?_) ?_) ?_
  · have := h (tf.testBit (4 * b + 2 * a + bitN (w.testBit 0))) 0 (by norm_num)
    simpa using this
  · exact h _ 1 (by norm_num)
  · exact h _ 2 (by norm_num)
  · exact h _ 3 (by norm_num)
  · exact h _ 4 (by norm_num)

private theorem testBit_bitN (p : Bool) (k : ℕ) : (bitN p).testBit k = (decide (k = 0) && p) := by
  cases p
  · simp [bitN]
  · cases k
    · simp [bitN]
    · simp only [bitN, Bool.cond_true]
      rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
      simp

private theorem testBit_bitN_shl (p : Bool) (i j : ℕ) :
    (bitN p <<< i).testBit j = (decide (j = i) && p) := by
  rw [Nat.testBit_shiftLeft, testBit_bitN]
  by_cases h : i ≤ j
  · by_cases h' : j = i
    · simp [h']
    · have : j - i ≠ 0 := by omega
      simp [h, h', this]
  · have h' : j ≠ i := by omega
    simp [h, h']

/-- The bits of a step word are the rule applied along the context row. -/
theorem stepCode_testBit (tf b a w : ℕ) (j : ℕ) (hj : j < 5) :
    (stepCode tf b a w).testBit j =
      tf.testBit (4 * ctxCell b a w j + 2 * ctxCell b a w (j + 1) + ctxCell b a w (j + 2)) := by
  unfold stepCode
  simp only [Nat.testBit_or, testBit_bitN, testBit_bitN_shl]
  interval_cases j <;> simp [ctxCell]

/-- The word of a stepped map at a pattern is the step of the word. -/
theorem word_stepMap (tf b a H : ℕ) {s : ℕ} (hs : s < 32) :
    word (stepMap tf b a H) s = stepCode tf b a (word H s) := by
  rw [stepMap, word_mkMap _ hs]
  exact and_31_of_lt (stepCode_lt _ _ _ _)

private theorem word_relabel (H : ℕ) {u s : ℕ} (_hu : u < 32) (hs : s < 32) :
    word (relabel H u) s = word H (s ^^^ u) := by
  rw [relabel, word_mkMap _ hs, word_and]

private theorem xor_lt_32 {a b : ℕ} (ha : a < 32) (hb : b < 32) : a ^^^ b < 32 := by
  have := Nat.xor_lt_two_pow (n := 5) (x := a) (y := b) (by simpa using ha) (by simpa using hb)
  simpa using this

private theorem relabel_relabel (K : ℕ) {u u' : ℕ} (_hu : u < 32) (hu' : u' < 32) :
    relabel (relabel K u) u' = relabel K (u' ^^^ u) := by
  unfold relabel
  apply mkMap_congr
  intro s hs
  rw [word_mkMap _ (xor_lt_32 hs hu')]
  simp only [word_and, Nat.xor_assoc]

private theorem stepMap_relabel (tf b a H : ℕ) {u : ℕ} (hu : u < 32) :
    stepMap tf b a (relabel H u) = relabel (stepMap tf b a H) u := by
  unfold stepMap
  conv_rhs => unfold relabel
  apply mkMap_congr
  intro s hs
  have hsu : s ^^^ u < 32 := xor_lt_32 hs hu
  rw [word_relabel H hu hs, word_mkMap _ hsu, Nat.and_assoc, Nat.and_self]

private theorem inCert_of_relabel (L : List ℕ) (K : ℕ) {u : ℕ} (hu : u < 32)
    (h : inCert L (relabel K u) = true) : inCert L K = true := by
  unfold inCert at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨u', hu', hm⟩ := h
  rw [List.mem_range] at hu'
  refine ⟨u' ^^^ u, List.mem_range.mpr (xor_lt_32 hu' hu), ?_⟩
  rwa [← relabel_relabel K hu hu']

private theorem mem_of_inCert (L : List ℕ) (H : ℕ) (h : inCert L H = true) :
    ∃ u < 32, relabel H u ∈ L := by
  unfold inCert at h
  rw [List.any_eq_true] at h
  obtain ⟨u, hu, hm⟩ := h
  exact ⟨u, List.mem_range.mp hu, by simpa using hm⟩

private theorem goodMap_of_relabel (tf H : ℕ) {u : ℕ} (hu : u < 32)
    (h : goodMap tf (relabel H u) = true) : goodMap tf H = true := by
  unfold goodMap at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro s hs
  have hs' := List.mem_range.mp hs
  have hsu : s ^^^ u < 32 := xor_lt_32 hs' hu
  have h1 := h (s ^^^ u) (List.mem_range.mpr hsu)
  rw [List.any_eq_true] at h1 ⊢
  obtain ⟨d, hd, hne⟩ := h1
  have hd32 : d < 32 := by
    have : ∀ d ∈ twoBall, d < 32 := by decide
    exact this d hd
  refine ⟨d, hd, ?_⟩
  have e1 : (s ^^^ u) ^^^ d ^^^ u = s ^^^ d := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases s.testBit i <;> cases u.testBit i <;> cases d.testBit i <;> rfl
  have e2 : (s ^^^ u) ^^^ u = s := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases s.testBit i <;> cases u.testBit i <;> rfl
  rw [word_relabel H hu hsu, word_relabel H hu (xor_lt_32 hsu hd32), e1, e2] at hne
  exact hne

/-- What the certificate check delivers: it holds every base map, and each member is
good and steps back into the list up to relabeling. -/
theorem certOK_spec {tf : ℕ} {L : List ℕ} (hc : certOK tf L = true) :
    (∀ b < 32, inCert L (mkMap fun s => b ^^^ s) = true) ∧
    (∀ H ∈ L, goodMap tf H = true ∧
      ∀ c < 4, inCert L (stepMap tf (c / 2) (c % 2) H) = true) := by
  unfold certOK at hc
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hc
  obtain ⟨h1, h2⟩ := hc
  refine ⟨fun b hb => h1 b (List.mem_range.mpr hb), fun H hH => ?_⟩
  have := h2 H hH
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨this.1, fun c hc => this.2 c (List.mem_range.mpr hc)⟩

/-- Membership up to relabeling is closed under the step, under every context pair. -/
theorem inCert_step {tf : ℕ} {L : List ℕ} (hc : certOK tf L = true) {H : ℕ}
    (hH : inCert L H = true) {b a : ℕ} (hb : b < 2) (ha : a < 2) :
    inCert L (stepMap tf b a H) = true := by
  obtain ⟨u, hu, hm⟩ := mem_of_inCert L H hH
  obtain ⟨-, h2⟩ := certOK_spec hc
  have hc4 : 2 * b + a < 4 := by omega
  have := (h2 _ hm).2 (2 * b + a) hc4
  rw [show (2 * b + a) / 2 = b by omega, show (2 * b + a) % 2 = a by omega,
    stepMap_relabel _ _ _ _ hu] at this
  exact inCert_of_relabel L _ hu this

/-- Every map in the list up to relabeling is good. -/
theorem goodMap_of_inCert {tf : ℕ} {L : List ℕ} (hc : certOK tf L = true) {H : ℕ}
    (hH : inCert L H = true) : goodMap tf H = true := by
  obtain ⟨u, hu, hm⟩ := mem_of_inCert L H hH
  obtain ⟨-, h2⟩ := certOK_spec hc
  exact goodMap_of_relabel tf H hu (h2 _ hm).1

/-! ## The region model -/

/-- The rule with Wolfram number `n`: the value at `(a, b, c)` is bit `4 a + 2 b + c` of `n`. -/
def ruleOfNat (n : ℕ) : LocalRule :=
  fun a b c => if n.testBit (4 * a.val + 2 * b.val + c.val) then 1 else 0

private theorem decide_ruleOfNat (n : ℕ) (a b c : ZMod 2) :
    decide (ruleOfNat n a b c = 1) = n.testBit (4 * a.val + 2 * b.val + c.val) := by
  unfold ruleOfNat
  by_cases h : n.testBit (4 * a.val + 2 * b.val + c.val) = true <;> simp [h]

private theorem val_eq_bitN (z : ZMod 2) : z.val = bitN (decide (z = 1)) := by
  revert z; decide

/-- The element of `ZMod 2` of a Boolean. -/
def bitZ (p : Bool) : ZMod 2 := cond p 1 0

private theorem zmod_xor (z : ZMod 2) (p : Bool) :
    decide (z + bitZ p = 1) = xor (decide (z = 1)) p := by
  revert z; cases p <;> decide

private theorem exists_word (p : ℕ → Bool) : ∀ n : ℕ, ∃ b < 2 ^ n, ∀ j < n, b.testBit j = p j := by
  intro n
  induction n with
  | zero => exact ⟨0, by norm_num, fun j hj => by omega⟩
  | succ n ih =>
    obtain ⟨b, hb, hbj⟩ := ih
    refine ⟨b ||| (if p n then 2 ^ n else 0), ?_, ?_⟩
    · apply Nat.or_lt_two_pow
      · calc b < 2 ^ n := hb
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      · split_ifs
        · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        · positivity
    · intro j hj
      rw [Nat.testBit_or]
      by_cases hjn : j = n
      · subst hjn
        have : b.testBit j = false := Nat.testBit_lt_two_pow hb
        by_cases hp : p j = true <;> simp [hp, this]
      · have hj' : j < n := by omega
        rw [hbj j hj']
        by_cases hp : p n = true
        · have hnj : n ≠ j := Ne.symm hjn
          simp [hp, hnj]
        · simp [hp]

private theorem LocalRule.lineRule_iterate_congr (f : LocalRule) (τ : ℕ) (i : ℤ)
    (x x' : Configuration) (h : ∀ j : ℤ, i - (τ : ℤ) ≤ j → j ≤ i + (τ : ℤ) → x j = x' j) :
    (lineRule f)^[τ] x i = (lineRule f)^[τ] x' i := by
  induction τ generalizing i with
  | zero => simpa using h i (by simp) (by simp)
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change f _ _ _ = f _ _ _
    rw [ih (i - 1) (fun j hj1 hj2 => h j (by push_cast; omega) (by push_cast; omega)),
      ih i (fun j hj1 hj2 => h j (by push_cast; omega) (by push_cast; omega)),
      ih (i + 1) (fun j hj1 hj2 => h j (by push_cast; omega) (by push_cast; omega))]

/-- The state `x` with the cell `τ - 4 + j` of the window's last five cells flipped when bit `j`
of the pattern `s` is set. -/
private def Configuration.flipAt (τ : ℕ) (x : Configuration) (s : ℕ) : Configuration := fun i =>
  x i + bitZ (decide (0 ≤ i - ((τ : ℤ) - 4)) && s.testBit (i - ((τ : ℤ) - 4)).toNat)

private theorem flipAt_eq_of_lt (τ : ℕ) (x : Configuration) (s : ℕ) {j : ℤ} (hj : j < (τ : ℤ) - 4) :
    flipAt τ x s j = x j := by
  have h : ¬ (0 ≤ j - ((τ : ℤ) - 4)) := by omega
  have h' : decide (0 ≤ j - ((τ : ℤ) - 4)) = false := decide_eq_false h
  simp only [flipAt, h', Bool.false_and, bitZ, Bool.cond_false, add_zero]

private theorem flipAt_zero (τ : ℕ) (x : Configuration) : flipAt τ x 0 = x := by
  funext i
  simp [flipAt, bitZ]

/-- The cell index of the region's left end at time `t`. -/
private def origin (τ t : ℕ) : ℤ := (τ : ℤ) - 4 - t

private theorem iterate_flipAt (tf τ : ℕ) (x : Configuration) (s t : ℕ) (i : ℤ)
    (hi : i + t < (τ : ℤ) - 4) :
    (lineRule (ruleOfNat tf))^[t] (flipAt τ x s) i = (lineRule (ruleOfNat tf))^[t] x i :=
  lineRule_iterate_congr _ t i _ _ (fun j _ hj => flipAt_eq_of_lt τ x s (by omega))

/-- The two context cells at time `t`, as natural numbers. -/
private def regionCtx (tf τ : ℕ) (x : Configuration) (t : ℕ) : ℕ × ℕ :=
  (((lineRule (ruleOfNat tf))^[t] x (origin τ t - 2)).val,
    ((lineRule (ruleOfNat tf))^[t] x (origin τ t - 1)).val)

/-- The region map at time `t`: the base map at `w₀` stepped under the contexts. -/
private def regionMap (tf w₀ : ℕ) (ctx : ℕ → ℕ × ℕ) : ℕ → ℕ
  | 0 => mkMap fun s => w₀ ^^^ s
  | t + 1 => stepMap tf (ctx t).1 (ctx t).2 (regionMap tf w₀ ctx t)

private theorem region_sound (tf τ : ℕ) (x : Configuration) (w₀ : ℕ)
    (hw : ∀ j < 5, w₀.testBit j = decide (x ((τ : ℤ) - 4 + j) = 1)) :
    ∀ t, ∀ s < 32, ∀ j < 5, (word (regionMap tf w₀ (regionCtx tf τ x) t) s).testBit j =
      decide ((lineRule (ruleOfNat tf))^[t] (flipAt τ x s) (origin τ t + j) = 1) := by
  intro t
  induction t with
  | zero =>
    intro s hs j hj
    rw [regionMap, word_mkMap _ hs]
    have e : origin τ 0 + (j : ℤ) = (τ : ℤ) - 4 + j := by simp [origin]
    have e2 : (τ : ℤ) - 4 + j - ((τ : ℤ) - 4) = j := by ring
    simp only [Function.iterate_zero, id, e, flipAt, e2, Int.toNat_natCast, zmod_xor,
      Nat.testBit_and, Nat.testBit_xor, testBit_31, hw j hj, hj, decide_true, Bool.and_true]
    simp
  | succ t ih =>
    intro s hs j hj
    rw [regionMap, word_stepMap _ _ _ _ hs, stepCode_testBit _ _ _ _ _ hj,
      Function.iterate_succ_apply']
    change _ = decide (ruleOfNat tf _ _ _ = 1)
    rw [decide_ruleOfNat]
    have key : ∀ k : ℕ, k < 7 →
        ctxCell (regionCtx tf τ x t).1 (regionCtx tf τ x t).2
          (word (regionMap tf w₀ (regionCtx tf τ x) t) s) k =
        ((lineRule (ruleOfNat tf))^[t] (flipAt τ x s) (origin τ t - 2 + (k : ℤ))).val := by
      intro k hk
      match k, hk with
      | 0, _ =>
        simp only [ctxCell, regionCtx, Nat.cast_zero, add_zero]
        rw [iterate_flipAt _ _ _ _ _ _ (by unfold origin; omega)]
      | 1, _ =>
        simp only [ctxCell, regionCtx, Nat.cast_one]
        rw [iterate_flipAt _ _ _ _ _ _ (by unfold origin; omega)]
        congr 3
        ring_nf
      | k + 2, hk =>
        simp only [ctxCell]
        rw [ih s hs k (by omega), ← val_eq_bitN]
        congr 3
        push_cast
        ring_nf
    have e0 : origin τ (t + 1) + (j : ℤ) - 1 = origin τ t - 2 + (j : ℤ) := by
      unfold origin; push_cast; ring
    have e1 : origin τ (t + 1) + (j : ℤ) = origin τ t - 2 + ((j + 1 : ℕ) : ℤ) := by
      unfold origin; push_cast; ring
    have e2 : origin τ (t + 1) + (j : ℤ) + 1 = origin τ t - 2 + ((j + 2 : ℕ) : ℤ) := by
      unfold origin; push_cast; ring
    rw [e2, e0, e1, key j (by omega), key (j + 1) (by omega), key (j + 2) (by omega)]

private theorem apex_region (tf n : ℕ) (x : Configuration) (w₀ : ℕ)
    (hw : ∀ j < 5, w₀.testBit j = decide (x (((n + 1 : ℕ) : ℤ) - 4 + j) = 1)) {s : ℕ}
    (hs : s < 32) :
    apex tf (word (regionMap tf w₀ (regionCtx tf (n + 1) x) n) s) =
      decide ((lineRule (ruleOfNat tf))^[n + 1] (flipAt (n + 1) x s) 0 = 1) := by
  have h2 := region_sound tf (n + 1) x w₀ hw n s hs 2 (by norm_num)
  have h3 := region_sound tf (n + 1) x w₀ hw n s hs 3 (by norm_num)
  have h4 := region_sound tf (n + 1) x w₀ hw n s hs 4 (by norm_num)
  have e2 : origin (n + 1) n + ((2 : ℕ) : ℤ) = 0 - 1 := by unfold origin; push_cast; ring
  have e3 : origin (n + 1) n + ((3 : ℕ) : ℤ) = 0 := by unfold origin; push_cast; ring
  have e4 : origin (n + 1) n + ((4 : ℕ) : ℤ) = 0 + 1 := by unfold origin; push_cast; ring
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [apex, h2, h3, h4, ← val_eq_bitN, ← val_eq_bitN, ← val_eq_bitN,
    Function.iterate_succ_apply']
  change _ = decide (ruleOfNat tf _ _ _ = 1)
  rw [decide_ruleOfNat]

private theorem word_xor_zero (H d : ℕ) : word H (0 ^^^ d) = word H d := by rw [Nat.zero_xor]

private theorem two_ball_card : ∀ d ∈ twoBall,
    ((Finset.range 5).filter fun j => d.testBit j = true).card ≤ 2 := by decide

private theorem two_ball_lt : ∀ d ∈ twoBall, d < 32 := by decide

/-- **The end-region closure from a certificate**: if the certificate check passes at the rule
with Wolfram number `tf`, no state of the line erases within `2` at any scale — flipping at most
two of the last five cells of the window of the scale-`τ` value at a cell always changes it. -/
theorem not_erasesWithin_two_of_certOK (tf : ℕ) (L : List ℕ) (hc : certOK tf L = true)
    (τ : ℕ) (x : Configuration) : ¬ ErasesWithin ((lineRule (ruleOfNat tf))^[τ]) x 2 := by
  intro hx
  rcases Nat.eq_zero_or_pos τ with rfl | hτ
  · have h := hx (Function.update x 0 (x 0 + 1))
      ⟨{0}, by simp, fun j hj => by
        simp only [Finset.mem_singleton] at hj
        simp [Function.update, hj]⟩
    have h0 := congrFun h 0
    simp only [Function.iterate_zero, id, Function.update_self] at h0
    have : ∀ z : ZMod 2, z + 1 ≠ z := by decide
    exact this _ h0
  · obtain ⟨n, rfl⟩ : ∃ n, τ = n + 1 := ⟨τ - 1, by omega⟩
    obtain ⟨w₀, hw₀lt, hw₀⟩ := exists_word (fun j => decide (x (((n + 1 : ℕ) : ℤ) - 4 + j) = 1)) 5
    have hw : ∀ j < 5, w₀.testBit j = decide (x (((n + 1 : ℕ) : ℤ) - 4 + j) = 1) :=
      fun j hj => hw₀ j hj
    have hmem : ∀ t, inCert L (regionMap tf w₀ (regionCtx tf (n + 1) x) t) = true := by
      intro t
      induction t with
      | zero =>
        exact (certOK_spec hc).1 w₀ (by simpa using hw₀lt)
      | succ t ih =>
        exact inCert_step hc ih (ZMod.val_lt (n := 2) _)
          (ZMod.val_lt (n := 2) _)
    have hgood := goodMap_of_inCert hc (hmem n)
    unfold goodMap at hgood
    rw [List.all_eq_true] at hgood
    have h0 := hgood 0 (List.mem_range.mpr (by norm_num))
    rw [List.any_eq_true] at h0
    obtain ⟨d, hd, hne⟩ := h0
    have hne' := bne_iff_ne.mp hne
    have hd32 := two_ball_lt d hd
    rw [word_xor_zero, apex_region tf n x w₀ hw hd32, apex_region tf n x w₀ hw (by norm_num),
      flipAt_zero] at hne'
    have hD : ∀ j, j ∉ (((Finset.range 5).filter fun j => d.testBit j = true).image
        fun j : ℕ => ((n + 1 : ℕ) : ℤ) - 4 + j) → flipAt (n + 1) x d j = x j := by
      intro j hj
      unfold flipAt
      have hb : (decide (0 ≤ j - (((n + 1 : ℕ) : ℤ) - 4)) &&
          d.testBit (j - (((n + 1 : ℕ) : ℤ) - 4)).toNat) = false := by
        by_contra hcon
        have hcon' := Bool.eq_true_of_ne_false hcon
        rw [Bool.and_eq_true, decide_eq_true_eq] at hcon'
        obtain ⟨hnn, htb⟩ := hcon'
        apply hj
        rw [Finset.mem_image]
        refine ⟨(j - (((n + 1 : ℕ) : ℤ) - 4)).toNat, ?_, by omega⟩
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, htb⟩
        by_contra hge
        have : d.testBit (j - (((n + 1 : ℕ) : ℤ) - 4)).toNat = false := by
          apply Nat.testBit_lt_two_pow
          calc d < 2 ^ 5 := by simpa using hd32
            _ ≤ 2 ^ (j - (((n + 1 : ℕ) : ℤ) - 4)).toNat :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [this] at htb
        exact absurd htb (by simp)
      rw [hb]
      simp [bitZ]
    have hcard : (((Finset.range 5).filter fun j => d.testBit j = true).image
        fun j : ℕ => ((n + 1 : ℕ) : ℤ) - 4 + j).card ≤ 2 :=
      (Finset.card_image_le).trans (two_ball_card d hd)
    have herase := hx (flipAt (n + 1) x d) ⟨_, hcard, hD⟩
    rw [herase] at hne'
    exact hne' rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- the kernel evaluation of the certificate check needs more than the default limits.
/-- The certificate at rule `38` passes the check. -/
theorem certOK_38 : certOK 38 cert38 = true := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see `certOK_38`.
/-- The certificate at rule `46` passes the check. -/
theorem certOK_46 : certOK 46 cert46 = true := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see `certOK_38`.
/-- The certificate at rule `66` passes the check. -/
theorem certOK_66 : certOK 66 cert66 = true := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see `certOK_38`.
/-- The certificate at rule `139` passes the check. -/
theorem certOK_139 : certOK 139 cert139 = true := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see `certOK_38`.
/-- The certificate at rule `155` passes the check. -/
theorem certOK_155 : certOK 155 cert155 = true := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see `certOK_38`.
/-- The certificate at rule `189` passes the check. -/
theorem certOK_189 : certOK 189 cert189 = true := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see `certOK_38`.
/-- **The check is load-bearing**: a certificate is refused at rule `128`, which sends only
`(1, 1, 1)` to `1` and so holds two-flip plateaus; the member clause fails there. -/
theorem certOK_refuses_128 : certOK 128 cert38 = false := by decide +kernel

/-- **The hypotheses of the closure are jointly satisfiable**: at rule `38` the check passes and
the all-zero state, like every state, does not erase within `2` at scale `2`. -/
theorem not_erasesWithin_two_of_certOK_nonvacuous :
    certOK 38 cert38 = true ∧
      ¬ ErasesWithin ((lineRule (ruleOfNat 38))^[2]) (fun _ : ℤ => (0 : ZMod 2)) 2 :=
  ⟨certOK_38, not_erasesWithin_two_of_certOK 38 _ certOK_38 2 _⟩

/-! ## The mirror -/

/-- The iterate of the mirror rule is the iterate of the rule on the reflected state,
reflected back. -/
theorem LocalRule.lineRule_mirrorRule_iterate (f : LocalRule) (τ : ℕ)
    (x : Configuration) :
    (lineRule (mirrorRule f))^[τ] x =
      fun i => (lineRule f)^[τ] (fun j => x (-j)) (-i) := by
  induction τ with
  | zero => funext i; simp
  | succ τ ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext i
    change f _ _ _ = f _ _ _
    beta_reduce
    rw [show -(i + 1) = -i - 1 by ring, show -(i - 1) = -i + 1 by ring]

/-- **Reflecting the line reflects erasure**: the scale-`τ` iterate of the mirror rule erases a
state within `e` exactly when the iterate of the rule erases its reflection within `e`. -/
theorem erasesWithin_iterate_mirrorRule (f : LocalRule) (τ e : ℕ)
    (x : Configuration) :
    ErasesWithin ((lineRule (mirrorRule f))^[τ]) x e ↔
      ErasesWithin ((lineRule f)^[τ]) (fun i => x (-i)) e := by
  have key : ∀ (g : LocalRule) (y : Configuration),
      ErasesWithin ((lineRule (mirrorRule g))^[τ]) y e →
        ErasesWithin ((lineRule g)^[τ]) (fun i => y (-i)) e := by
    intro g y h z ⟨D, hD, hz⟩
    have hk := h (fun i => z (-i)) ⟨D.image Neg.neg, (Finset.card_image_le).trans hD,
      fun j hj => by
        simpa using hz (-j) (fun hmem => hj (Finset.mem_image.mpr ⟨-j, hmem, neg_neg j⟩))⟩
    funext i
    have := congrFun hk (-i)
    rw [lineRule_mirrorRule_iterate, lineRule_mirrorRule_iterate] at this
    simpa using this
  refine ⟨key f x, fun h => ?_⟩
  have h2 := key (mirrorRule f) (fun i => x (-i))
  have h3 : ErasesWithin ((lineRule (mirrorRule (mirrorRule f)))^[τ])
      (fun i => x (-i)) e := by
    exact h
  simpa using h2 h3

/-! ## The twelve rules -/

/-- The rule with Wolfram number `38` is `f38` of the one-tap-width module. -/
theorem ruleOfNat_38 : ruleOfNat 38 = f38 := by
  funext a b c; revert a b c; decide

/-- The rule with Wolfram number `46` is `f46` of the one-tap-width module. -/
theorem ruleOfNat_46 : ruleOfNat 46 = f46 := by
  funext a b c; revert a b c; decide

/-- The rule with Wolfram number `66` is `f66` of the one-tap-width module. -/
theorem ruleOfNat_66 : ruleOfNat 66 = f66 := by
  funext a b c; revert a b c; decide

private theorem LocalRule.mirrorRule_ruleOfNat (n m : ℕ) (h : ∀ a b c : ZMod 2,
    ruleOfNat m a b c = ruleOfNat n c b a) :
    mirrorRule (ruleOfNat n) = ruleOfNat m := by
  funext a b c
  exact (h a b c).symm

/-- **At rule `38` no state erases within `2`, at any scale.** -/
theorem not_erasesWithin_two_f38 (τ : ℕ) (x : Configuration) :
    ¬ ErasesWithin ((lineRule f38)^[τ]) x 2 := by
  rw [← ruleOfNat_38]
  exact not_erasesWithin_two_of_certOK 38 _ certOK_38 τ x

/-- **At rule `46` no state erases within `2`, at any scale.** -/
theorem not_erasesWithin_two_f46 (τ : ℕ) (x : Configuration) :
    ¬ ErasesWithin ((lineRule f46)^[τ]) x 2 := by
  rw [← ruleOfNat_46]
  exact not_erasesWithin_two_of_certOK 46 _ certOK_46 τ x

/-- **At rule `66` no state erases within `2`, at any scale.** -/
theorem not_erasesWithin_two_f66 (τ : ℕ) (x : Configuration) :
    ¬ ErasesWithin ((lineRule f66)^[τ]) x 2 := by
  rw [← ruleOfNat_66]
  exact not_erasesWithin_two_of_certOK 66 _ certOK_66 τ x

/-- The twelve rules of the end-region closure: the six that close at the right end and their
mirrors. -/
def endClosureRules : List LocalRule :=
  [24, 38, 46, 52, 66, 116, 139, 155, 189, 209, 211, 231].map ruleOfNat

/-- **At each of the twelve rules no state erases within `2`, at any scale.** -/
theorem not_erasesWithin_two_of_mem_endClosureRules (f : LocalRule)
    (hf : f ∈ endClosureRules) (τ : ℕ) (x : Configuration) :
    ¬ ErasesWithin ((lineRule f)^[τ]) x 2 := by
  have mir : ∀ (n m : ℕ) (L : List ℕ), certOK n L = true →
      (∀ a b c : ZMod 2, ruleOfNat m a b c = ruleOfNat n c b a) →
      ¬ ErasesWithin ((lineRule (ruleOfNat m))^[τ]) x 2 := by
    intro n m L hL hm h
    rw [← mirrorRule_ruleOfNat n m hm] at h
    exact not_erasesWithin_two_of_certOK n L hL τ _
      ((erasesWithin_iterate_mirrorRule _ τ 2 x).mp h)
  simp only [endClosureRules, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mir 66 24 _ certOK_66 (by decide)
  · exact not_erasesWithin_two_of_certOK 38 _ certOK_38 τ x
  · exact not_erasesWithin_two_of_certOK 46 _ certOK_46 τ x
  · exact mir 38 52 _ certOK_38 (by decide)
  · exact not_erasesWithin_two_of_certOK 66 _ certOK_66 τ x
  · exact mir 46 116 _ certOK_46 (by decide)
  · exact not_erasesWithin_two_of_certOK 139 _ certOK_139 τ x
  · exact not_erasesWithin_two_of_certOK 155 _ certOK_155 τ x
  · exact not_erasesWithin_two_of_certOK 189 _ certOK_189 τ x
  · exact mir 139 209 _ certOK_139 (by decide)
  · exact mir 155 211 _ certOK_155 (by decide)
  · exact mir 189 231 _ certOK_189 (by decide)

/-- **The conclusion of `LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcing`
at the twelve rules, vacuously**: two states each erasing within
`2` have the same successor because no state erases within `2`. -/
theorem LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_mem_endClosureRules
    (f : LocalRule) (hf : f ∈ endClosureRules) (τ : ℕ)
    (x y : Configuration) (hx : ErasesWithin ((lineRule f)^[τ]) x 2)
    (_hy : ErasesWithin ((lineRule f)^[τ]) y 2) :
    (lineRule f)^[τ] x = (lineRule f)^[τ] y :=
  absurd hx (not_erasesWithin_two_of_mem_endClosureRules f hf τ x)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- the ambient type has 256 members; kernel reduction of the nested Pi-Fintype instance, of the
-- bounded search and of the list membership needs more than the defaults of both limits.
/-- **The class extended by the twelve rules holds at `164` of the `256` rules.** -/
theorem card_forcingClass_or_endClosure :
    Fintype.card {f : LocalRule //
      ReturnsWithinTwo f ∨ LeftPermutive f ∨
        RightPermutive f ∨ f ∈ endClosureRules} = 164 := by
  decide

/-- **The conclusion of `LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcing`
over the extended class**: at every scale, two states each erasing
within `2` have the same successor, at every rule that returns within two, is permutive at an
end, or is one of the twelve rules of the end-region closure. -/
theorem LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure
    (f : LocalRule)
    (hf : ReturnsWithinTwo f ∨ LeftPermutive f ∨
      RightPermutive f ∨ f ∈ endClosureRules) (τ : ℕ) (x y : Configuration)
    (hx : ErasesWithin ((lineRule f)^[τ]) x 2) (hy : ErasesWithin ((lineRule f)^[τ]) y 2) :
    (lineRule f)^[τ] x = (lineRule f)^[τ] y := by
  rcases hf with h | h | h | h
  · exact lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass f (Or.inl h)
      τ x y
      hx hy
  · exact lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass f
      (Or.inr (Or.inl h)) τ x y hx hy
  · exact lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass f
      (Or.inr (Or.inr h)) τ x y hx hy
  · exact lineRule_iterate_eq_of_erasesWithin_two_of_mem_endClosureRules f h τ x y hx hy

/-- **The extended corollary's hypotheses are jointly satisfiable**: at the product rule, which
returns within two, the states `0` and the single `1` at the origin each erase within `2` at
scale `2` and differ — the end-region disjunct is not what makes the corollary non-vacuous. -/
theorem LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure_nonvacuous :
    (ReturnsWithinTwo (fun a b c : ZMod 2 => a * b * c) ∨
      LeftPermutive (fun a b c : ZMod 2 => a * b * c) ∨
      RightPermutive (fun a b c : ZMod 2 => a * b * c) ∨
      (fun a b c : ZMod 2 => a * b * c) ∈ endClosureRules) ∧
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2]) (fun _ : ℤ => 0) 2 ∧
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2])
      (fun j : ℤ => if j = 0 then 1 else 0) 2 ∧
    (fun _ : ℤ => (0 : ZMod 2)) ≠ (fun j : ℤ => if j = 0 then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_nonvacuous
  exact ⟨Or.inl h1, h2, h3, h4⟩


end ECA

/-! ## Axiom audit

Every public capstone above is `#print axioms`-checked; the guards make that build-enforced. -/

set_option linter.style.longLine false in
/-- info: 'ECA.not_erasesWithin_two_of_certOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_erasesWithin_two_of_certOK

/-- info: 'ECA.certOK_38' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.certOK_38

/-- info: 'ECA.certOK_46' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.certOK_46

/-- info: 'ECA.certOK_66' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.certOK_66

/-- info: 'ECA.certOK_139' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.certOK_139

/-- info: 'ECA.certOK_155' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.certOK_155

/-- info: 'ECA.certOK_189' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.certOK_189

/-- info: 'ECA.certOK_refuses_128' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.certOK_refuses_128

set_option linter.style.longLine false in
/-- info: 'ECA.not_erasesWithin_two_of_certOK_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_erasesWithin_two_of_certOK_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.erasesWithin_iterate_mirrorRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.erasesWithin_iterate_mirrorRule

set_option linter.style.longLine false in
/-- info: 'ECA.not_erasesWithin_two_f38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_erasesWithin_two_f38

set_option linter.style.longLine false in
/-- info: 'ECA.not_erasesWithin_two_f46' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_erasesWithin_two_f46

set_option linter.style.longLine false in
/-- info: 'ECA.not_erasesWithin_two_f66' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_erasesWithin_two_f66

set_option linter.style.longLine false in
/-- info: 'ECA.not_erasesWithin_two_of_mem_endClosureRules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_erasesWithin_two_of_mem_endClosureRules

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_mem_endClosureRules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_mem_endClosureRules

set_option linter.style.longLine false in
/-- info: 'ECA.card_forcingClass_or_endClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_forcingClass_or_endClosure

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ECA.LocalRule.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure_nonvacuous
