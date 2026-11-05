module

public import ECA.Rule106Roots
import all ECA.Rule106Roots
import all ECA.ReproducedPatterns
import all ECA.ReproductionBracket
import all ECA.Growth
import all ECA.EndpointClasses

/-!
# Rule `106` at the leftmost cell
([RuleSpace] §5)

Rule `106` sends the cells `(a, b, c)` to `c + a * b` over `ZMod 2`, so the cell `i` of the image
of `x` is `x (i + 1) + x (i - 1) * x i`. A state with no predecessor is called a root; a
reproduced state is a root or descends from one (`reproduces_wolfram106_iff_root`), and this
module gives a necessary condition on a reproduced root and decides one family of roots.

Read from the left, a predecessor is, across a stretch of three or more cells the image leaves
clear, either clear at two adjacent cells or set throughout. A predecessor of two blocks that far
apart therefore splits at that stretch: in the first case its left part is a predecessor of the
left block, and in the second its right part is a predecessor of the right block with its
leftmost set cell cleared.

## Main results

* `FiniteConfiguration.dropLeftmost` — the state with its leftmost set cell cleared.
* `mem_range_or_dropLeftmost_mem_range_wolfram106` — **the split**: a state with a predecessor
  that is two blocks, the second at least three cells right of the first, has a predecessor of the
  first block or a predecessor of the second block with its leftmost set cell cleared.
* `Reproduces.dropLeftmost_mem_range_wolfram106` — **the condition**: a reproduced state with no
  predecessor has, once its leftmost set cell is cleared, a predecessor;
  `Reproduces.dropLeftmost_mem_range_wolfram106_root_load_bearing` shows the hypothesis of having
  no predecessor cannot be dropped.
* `FiniteConfiguration.RightPairOnly` — a state whose only adjacent set cells are its two
  rightmost; `FiniteConfiguration.RightPairOnly.notMem_range_wolfram106` — such a state has no
  predecessor.
* `FiniteConfiguration.RightPairOnly.reproduces_wolfram106_iff` — **the class decided**: such a
  state is reproduced exactly when it is the pair `11` up to translation, that is, when its
  diameter is `2`; `not_reproduces_wolfram106_single_zero_add_single_two_add_single_three` is the
  state `1011`.
* the statements are not vacuous: `mem_range_or_dropLeftmost_mem_range_wolfram106_nonvacuous`,
  `Reproduces.dropLeftmost_mem_range_wolfram106_nonvacuous` and
  `FiniteConfiguration.RightPairOnly.notMem_range_wolfram106_nonvacuous`.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## Clearing the leftmost set cell -/

/-- The state with its leftmost set cell cleared; the zero state at the zero state. -/
noncomputable def FiniteConfiguration.dropLeftmost (s : FiniteConfiguration) :
    FiniteConfiguration :=
  if h : s.support.Nonempty then s.erase (s.support.min' h) else 0

/-- Clearing the leftmost set cell of the zero state leaves the zero state. -/
theorem FiniteConfiguration.dropLeftmost_zero : dropLeftmost (0 : FiniteConfiguration) = 0 := by
  simp [dropLeftmost]

/-- The cells of a nonzero state with its leftmost set cell cleared: zero at that cell, the
state's elsewhere. -/
theorem FiniteConfiguration.dropLeftmost_apply {s : FiniteConfiguration}
    (hne : s.support.Nonempty) (i : ℤ) :
    dropLeftmost s i = if i = s.support.min' hne then 0 else s i := by
  simp [dropLeftmost, hne, Finsupp.erase_apply]

/-- A state whose only adjacent set cells are its two rightmost: its rightmost set cell `r` and
`r - 1` are set, and any two adjacent set cells are those two. -/
def FiniteConfiguration.RightPairOnly (s : FiniteConfiguration) : Prop :=
  ∃ r : ℤ, s r ≠ 0 ∧ s (r - 1) ≠ 0 ∧ (∀ i, r < i → s i = 0) ∧
    ∀ i, s i ≠ 0 → s (i + 1) ≠ 0 → i = r - 1

/-- Clearing the leftmost set cell commutes with translation. -/
theorem FiniteConfiguration.dropLeftmost_translate (d : ℤ) (s : FiniteConfiguration) :
    dropLeftmost (translate d s) = translate d (dropLeftmost s) := by
  by_cases hs : s = 0
  · subst hs
    rw [(translate_ne_zero_iff d).mpr rfl, dropLeftmost_zero,
      (translate_ne_zero_iff d).mpr rfl]
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hne' : (translate d s).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (fun h => hs ((translate_ne_zero_iff d).mp h))
  ext i
  rw [dropLeftmost_apply hne', translate_apply' d (dropLeftmost s) i, dropLeftmost_apply hne,
    translate_support_min' d hne hne', translate_apply' d s i]
  by_cases h : i = s.support.min' hne + d
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- Clearing the leftmost set cell of a nonzero block followed by cells strictly to its right
clears the leftmost set cell of the block. -/
theorem FiniteConfiguration.dropLeftmost_add {X Y : FiniteConfiguration} (hX : X ≠ 0)
    (hXY : ∀ i j, X i ≠ 0 → Y j ≠ 0 → i < j) :
    dropLeftmost (X + Y) = dropLeftmost X + Y := by
  have hXne : X.support.Nonempty := Finsupp.support_nonempty_iff.mpr hX
  have hm : X (X.support.min' hXne) ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hXne)
  have hY0 : Y (X.support.min' hXne) = 0 := by
    by_contra hy
    exact lt_irrefl _ (hXY _ _ hm hy)
  have hsum : (X + Y) (X.support.min' hXne) ≠ 0 := by
    rw [Finsupp.add_apply, hY0, add_zero]
    exact hm
  have hne : (X + Y).support.Nonempty := ⟨_, Finsupp.mem_support_iff.mpr hsum⟩
  have hmin : (X + Y).support.min' hne = X.support.min' hXne := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hsum)
    · apply Finset.le_min'
      intro y hy
      have hy' := Finsupp.mem_support_iff.mp hy
      rw [Finsupp.add_apply] at hy'
      by_cases hxy : X y = 0
      · rw [hxy, zero_add] at hy'
        have := hXY _ _ hm hy'
        omega
      · exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hxy)
  ext i
  rw [dropLeftmost_apply hne, hmin, Finsupp.add_apply, Finsupp.add_apply (dropLeftmost X) Y i,
    dropLeftmost_apply hXne]
  by_cases h : i = X.support.min' hXne
  · rw [ite_eq_left h, ite_eq_left h, h, hY0, add_zero]
  · rw [ite_eq_right h, ite_eq_right h]

/-! ## The split -/

private theorem zmod2_add_eq_zero (u v : ZMod 2) (h : u + v = 0) : u = v := by
  revert u v
  decide

/-- **The split at rule `106`**: if a state with a predecessor is the sum of a block `A` and a block
`B` lying at least three cells right of it, then `A` has a predecessor, or `B` with its leftmost set
cell cleared has one ([RuleSpace] §5). -/
theorem mem_range_or_dropLeftmost_mem_range_wolfram106 (hq : wolframRule 106 0 0 0 = 0)
    {A B : FiniteConfiguration} (hgap : ∀ i j, A i ≠ 0 → B j ≠ 0 → i + 3 ≤ j)
    (h : A + B ∈ Set.range (finRule (wolframRule 106) hq)) :
    A ∈ Set.range (finRule (wolframRule 106) hq) ∨
      B.dropLeftmost ∈ Set.range (finRule (wolframRule 106) hq) := by
  by_cases hB : B = 0
  · right
    subst hB
    rw [dropLeftmost_zero]
    exact ⟨0, finRule_zero' _ hq⟩
  by_cases hA : A = 0
  · left
    subst hA
    exact ⟨0, finRule_zero' _ hq⟩
  obtain ⟨x, hx⟩ := h
  have hAne : A.support.Nonempty := Finsupp.support_nonempty_iff.mpr hA
  have hBne : B.support.Nonempty := Finsupp.support_nonempty_iff.mpr hB
  obtain ⟨a, ha⟩ : ∃ a, a = A.support.max' hAne := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = B.support.min' hBne := ⟨_, rfl⟩
  have hAa : A a ≠ 0 := by
    rw [ha]
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ hAne)
  have hBb : B b ≠ 0 := by
    rw [hb]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem _ hBne)
  have hab : a + 3 ≤ b := hgap a b hAa hBb
  have hAgt : ∀ i, a < i → A i = 0 := fun i hi => above_max'_eq_zero hAne (by omega)
  have hBlt : ∀ i, i < b → B i = 0 := fun i hi => below_min'_eq_zero hBne (by omega)
  have hcell : ∀ i, x (i + 1) + x (i - 1) * x i = A i + B i := fun i => by
    rw [← finRule_wolfram106_apply hq x i, hx, Finsupp.add_apply]
  have hmid : ∀ i, a < i → i < b → x (i + 1) = x (i - 1) * x i := fun i h1 h2 => by
    have := hcell i
    rw [hAgt i h1, hBlt i h2, add_zero] at this
    exact zmod2_add_eq_zero _ _ this
  by_cases hcase : ∃ m, a < m ∧ m ≤ b ∧ x (m - 1) = 0 ∧ x m = 0
  · left
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := hcase
    refine ⟨x.filter (· < m), ?_⟩
    ext i
    rw [finRule_wolfram106_apply]
    simp only [Finsupp.filter_apply]
    have hi := hcell i
    by_cases h1 : i + 1 < m
    · rw [ite_eq_left h1, ite_eq_left (by omega : i - 1 < m), ite_eq_left (by omega : i < m), hi,
        hBlt i (by omega), add_zero]
    · rw [ite_eq_right h1]
      rcases (by omega : i = m - 1 ∨ m ≤ i) with h2 | h2
      · have hxi : x i = 0 := by rw [h2]; exact hm3
        have hxi1 : x (i + 1) = 0 := by rw [show i + 1 = m by omega]; exact hm4
        rw [hxi, hxi1, hBlt i (by omega), add_zero, mul_zero, add_zero] at hi
        rw [ite_eq_left (by omega : i - 1 < m), ite_eq_left (by omega : i < m), hxi, ← hi]
        simp
      · rw [ite_eq_right (by omega : ¬ i < m), mul_zero, zero_add, hAgt i (by omega)]
  · right
    push Not at hcase
    have hm : ∀ m, a < m → m ≤ b → ¬ (x (m - 1) = 0 ∧ x m = 0) := fun m h1 h2 h3 =>
      hcase m h1 h2 h3.1 h3.2
    have e1 : x (a + 2) = x a * x (a + 1) := by
      have := hmid (a + 1) (by omega) (by omega)
      rwa [show a + 1 + 1 = a + 2 by ring, show a + 1 - 1 = a by ring] at this
    have e2 : x (a + 3) = x (a + 1) * x (a + 2) := by
      have := hmid (a + 2) (by omega) (by omega)
      rwa [show a + 2 + 1 = a + 3 by ring, show a + 2 - 1 = a + 1 by ring] at this
    have n1 : ¬ (x a = 0 ∧ x (a + 1) = 0) := by
      have := hm (a + 1) (by omega) (by omega)
      rwa [show a + 1 - 1 = a by ring] at this
    have n2 : ¬ (x (a + 1) = 0 ∧ x (a + 2) = 0) := by
      have := hm (a + 2) (by omega) (by omega)
      rwa [show a + 2 - 1 = a + 1 by ring] at this
    have n3 : ¬ (x (a + 2) = 0 ∧ x (a + 3) = 0) := by
      have := hm (a + 3) (by omega) (by omega)
      rwa [show a + 3 - 1 = a + 2 by ring] at this
    have hpq : x a = 1 ∧ x (a + 1) = 1 := by
      revert e1 e2 n1 n2 n3
      generalize x a = p
      generalize x (a + 1) = q
      generalize x (a + 2) = r
      generalize x (a + 3) = s
      revert p q r s
      decide
    have hall : ∀ n : ℕ, a + n + 1 ≤ b → x (a + n) = 1 ∧ x (a + n + 1) = 1 := by
      intro n
      induction n with
      | zero =>
        intro _
        simpa using hpq
      | succ n ih =>
        intro hn
        obtain ⟨h1, h2⟩ := ih (by omega)
        have h3 := hmid (a + n + 1) (by omega) (by omega)
        rw [show a + n + 1 + 1 = a + ((n + 1 : ℕ) : ℤ) + 1 by push_cast; ring,
          show a + n + 1 - 1 = a + n by ring, h1, h2] at h3
        refine ⟨?_, ?_⟩
        · rw [show a + ((n + 1 : ℕ) : ℤ) = a + n + 1 by push_cast; ring]
          exact h2
        · rw [h3]
          decide
    obtain ⟨hb1, hb2⟩ := hall (b - a - 1).toNat (by omega)
    rw [show a + ((b - a - 1).toNat : ℤ) = b - 1 by omega] at hb1
    rw [show a + ((b - a - 1).toNat : ℤ) + 1 = b by omega] at hb2
    have hBb1 : B b = 1 := zmod2_eq_one_of_ne_zero' _ hBb
    have hxb1 : x (b + 1) = 0 := by
      have := hcell b
      rw [hb1, hb2, hAgt b (by omega), hBb1] at this
      revert this
      generalize x (b + 1) = u
      revert u
      decide
    refine ⟨x.filter (b + 1 ≤ ·), ?_⟩
    ext i
    rw [finRule_wolfram106_apply, dropLeftmost_apply hBne, ← hb]
    simp only [Finsupp.filter_apply]
    by_cases hi1 : i < b
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), hBlt i hi1]
      simp
    · by_cases hi2 : i = b
      · subst hi2
        rw [ite_eq_left rfl, ite_eq_left (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), hxb1]
        simp
      · rw [ite_eq_right hi2]
        have hi := hcell i
        rcases (by omega : i = b + 1 ∨ b + 2 ≤ i) with h2 | h2
        · subst h2
          have hxb1' : x (b + 1) = 0 := hxb1
          rw [ite_eq_left (by omega), ite_eq_right (by omega : ¬ (b + 1 ≤ b + 1 - 1)),
            ite_eq_left le_rfl, zero_mul, add_zero]
          rw [hxb1', mul_zero, add_zero, hAgt (b + 1) (by omega), zero_add] at hi
          exact hi
        · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega), hi,
            hAgt i (by omega), zero_add]

/-- Clearing the leftmost set cell of a single cell leaves the zero state. -/
theorem FiniteConfiguration.dropLeftmost_single (a : ℤ) (c : ZMod 2) :
    dropLeftmost (Finsupp.single a c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, Finsupp.single_zero, dropLeftmost_zero]
  · have hs : (Finsupp.single a c).support = {a} := Finsupp.support_single a hc
    have hne : (Finsupp.single a c).support.Nonempty := by
      rw [hs]
      exact Finset.singleton_nonempty a
    ext i
    rw [dropLeftmost_apply hne]
    simp only [hs, Finset.min'_singleton, Finsupp.coe_zero, Pi.zero_apply]
    by_cases h : i = a
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, Finsupp.single_apply, ite_eq_right (Ne.symm h)]

/-- A single set cell followed by cells strictly to its right loses that cell. -/
theorem FiniteConfiguration.dropLeftmost_single_add {a : ℤ} {Y : FiniteConfiguration}
    (hY : ∀ j, Y j ≠ 0 → a < j) :
    dropLeftmost (Finsupp.single a (1 : ZMod 2) + Y) = Y := by
  have hX : (Finsupp.single a (1 : ZMod 2)) ≠ 0 := by
    intro h
    have := congrArg (fun f : FiniteConfiguration => f a) h
    simp at this
  rw [dropLeftmost_add hX (fun i j hi hj => ?_), dropLeftmost_single, zero_add]
  have : i = a := by
    by_contra hne
    exact hi (by rw [Finsupp.single_apply, ite_eq_right (Ne.symm hne)])
  rw [this]
  exact hY j hj

private theorem pair_apply_ne_zero {b c j : ℤ}
    (h : (Finsupp.single b (1 : ZMod 2) + Finsupp.single c 1 : FiniteConfiguration) j ≠ 0) :
    j = b ∨ j = c := by
  by_contra hn
  push Not at hn
  apply h
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hn.1),
    ite_eq_right (Ne.symm hn.2), add_zero]

/-- Clearing the leftmost set cell of a pair of cells leaves the right one. -/
theorem FiniteConfiguration.dropLeftmost_single_add_single {a b : ℤ} (h : a < b) :
    dropLeftmost (Finsupp.single a (1 : ZMod 2) + Finsupp.single b 1) = Finsupp.single b 1 := by
  apply dropLeftmost_single_add
  intro j hj
  have : j = b := by
    by_contra hne
    exact hj (by rw [Finsupp.single_apply, ite_eq_right (Ne.symm hne)])
  omega

/-- A cell of the state with its leftmost set cell cleared is a cell of the state. -/
theorem FiniteConfiguration.ne_zero_of_dropLeftmost_ne_zero {s : FiniteConfiguration} {i : ℤ}
    (h : dropLeftmost s i ≠ 0) : s i ≠ 0 := by
  by_cases hs : s.support.Nonempty
  · rw [dropLeftmost_apply hs] at h
    by_cases hi : i = s.support.min' hs
    · rw [ite_eq_left hi] at h
      exact absurd rfl h
    · rwa [ite_eq_right hi] at h
  · have : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst this
    rw [dropLeftmost_zero] at h
    exact absurd rfl h

/-- The pair `11` has no predecessor at rule `106`. -/
theorem pair_notMem_range_wolfram106 (hq : wolframRule 106 0 0 0 = 0) :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∉
      Set.range (finRule (wolframRule 106) hq) := by
  rintro ⟨x, hx⟩
  refine seedOneOne_notMem_range_f106 ⟨x, ?_⟩
  rw [← finRule_wolfram106_eq hq]
  exact hx

/-- **The split has a fixed instance**: with the pair `11` and the pair at cells `4` and `5`, the
three-cell gap holds, the sum has a predecessor, the pair has none, and the right pair with its
leftmost cell cleared has one. -/
theorem mem_range_or_dropLeftmost_mem_range_wolfram106_nonvacuous
    (hq : wolframRule 106 0 0 0 = 0) :
    (∀ i j, (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 : FiniteConfiguration) i ≠ 0 →
        (Finsupp.single (4 : ℤ) (1 : ZMod 2) + Finsupp.single 5 1 : FiniteConfiguration) j ≠ 0 →
        i + 3 ≤ j) ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) +
          (Finsupp.single (4 : ℤ) (1 : ZMod 2) + Finsupp.single 5 1) ∈
        Set.range (finRule (wolframRule 106) hq) ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∉
        Set.range (finRule (wolframRule 106) hq) ∧
      (Finsupp.single (4 : ℤ) (1 : ZMod 2) + Finsupp.single 5 1 :
          FiniteConfiguration).dropLeftmost ∈ Set.range (finRule (wolframRule 106) hq) := by
  refine ⟨fun i j hi hj => ?_, ⟨Finsupp.single (1 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1 +
    Finsupp.single 3 1 + Finsupp.single 4 1 + Finsupp.single 6 1, ?_⟩,
    pair_notMem_range_wolfram106 hq, ?_⟩
  · rcases pair_apply_ne_zero hi with h1 | h1 <;> rcases pair_apply_ne_zero hj with h2 | h2 <;>
      omega
  · ext i
    rw [finRule_wolfram106_apply]
    rcases (by omega : i < -1 ∨ (-1 ≤ i ∧ i ≤ 8) ∨ 8 < i) with h | h | h
    · simp (disch := omega) only [Finsupp.add_apply, Finsupp.single_eq_of_ne, add_zero, mul_zero]
    · obtain ⟨h1, h2⟩ := h
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      interval_cases i <;> decide
    · simp (disch := omega) only [Finsupp.add_apply, Finsupp.single_eq_of_ne, add_zero, mul_zero]
  · rw [dropLeftmost_single_add_single (by omega : (4 : ℤ) < 5)]
    refine ⟨Finsupp.single (6 : ℤ) (1 : ZMod 2), ?_⟩
    ext i
    rw [finRule_wolfram106_apply]
    rcases (by omega : i < 4 ∨ (4 ≤ i ∧ i ≤ 8) ∨ 8 < i) with h | h | h
    · simp (disch := omega) only [Finsupp.single_eq_of_ne, add_zero, mul_zero]
    · obtain ⟨h1, h2⟩ := h
      simp only [Finsupp.single_apply]
      interval_cases i <;> decide
    · simp (disch := omega) only [Finsupp.single_eq_of_ne, add_zero, mul_zero]

/-! ## A reproduced state with no predecessor -/

private theorem translate_mem_range_wolfram106 (hq : wolframRule 106 0 0 0 = 0) (d : ℤ)
    {X : FiniteConfiguration} :
    translate d X ∈ Set.range (finRule (wolframRule 106) hq) ↔
      X ∈ Set.range (finRule (wolframRule 106) hq) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨translate (-d) y, ?_⟩
    rw [finRule_translate, hy, translate_translate', add_neg_cancel, translate_zero']
  · rintro ⟨x, hx⟩
    exact ⟨translate d x, by rw [finRule_translate, hx]⟩

/-- Cells of the first of `n + 2` well-separated copies lie at least three cells left of the cells
of the later copies. -/
private theorem blocks_gap {ρ : FiniteConfiguration} {n : ℕ} {c : ℕ → ℤ}
    (hc : ∀ j, j + 1 < n + 2 → c j + diam ρ + (2 : ℕ) ≤ c (j + 1)) {A : FiniteConfiguration}
    (hA : ∀ i, A i ≠ 0 → ρ (i - c 0) ≠ 0) (i j : ℤ) (hi : A i ≠ 0)
    (hj : ((Finset.range (n + 1)).sum fun m => translate (c (m + 1)) ρ) j ≠ 0) : i + 3 ≤ j := by
  rw [Finsupp.finsetSum_apply] at hj
  obtain ⟨m, hm, hm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  rw [translate_apply'] at hm'
  have := copies_cells_apart (p := ρ) (k := n + 2) (G := 2) (c := c) le_rfl hc
    (j := 0) (j' := m + 1) (by omega) (by have := Finset.mem_range.mp hm; omega) (hA i hi) hm'
  omega

/-- The later copies of `n + 2` well-separated copies, with the leftmost cell of the earliest of
them cleared: that copy loses its cell and the rest is untouched. -/
private theorem blocks_drop {ρ : FiniteConfiguration} (hρ0 : ρ ≠ 0) {n : ℕ} {c : ℕ → ℤ}
    (hc : ∀ j, j + 1 < n + 2 → c j + diam ρ + (2 : ℕ) ≤ c (j + 1)) :
    ((Finset.range (n + 1)).sum fun m => translate (c (m + 1)) ρ).dropLeftmost =
      translate (c 1) ρ.dropLeftmost + (Finset.range n).sum fun m => translate (c (m + 2)) ρ := by
  rw [Finset.sum_range_succ', add_comm]
  rw [dropLeftmost_add ((translate_ne_zero_iff _).not.mpr hρ0), dropLeftmost_translate]
  · intro i j hi hj
    rw [Finsupp.finsetSum_apply] at hj
    obtain ⟨m, hm, hm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
    rw [translate_apply'] at hm'
    rw [translate_apply'] at hi
    have := copies_cells_apart (p := ρ) (k := n + 2) (G := 2) (c := c) le_rfl hc
      (j := 1) (j' := m + 2) (by omega) (by have := Finset.mem_range.mp hm; omega) hi hm'
    have e1 : c (0 + 1) = c 1 := rfl
    have e2 : c (m + 1 + 1) = c (m + 2) := rfl
    omega

private theorem dropLeftmost_mem_range_of_blocks (hq : wolframRule 106 0 0 0 = 0)
    {ρ : FiniteConfiguration} (hρ0 : ρ ≠ 0) :
    ∀ (n : ℕ) (c : ℕ → ℤ), (∀ j, j + 1 < n + 1 → c j + diam ρ + (2 : ℕ) ≤ c (j + 1)) →
      translate (c 0) ρ.dropLeftmost + (Finset.range n).sum (fun m => translate (c (m + 1)) ρ) ∈
        Set.range (finRule (wolframRule 106) hq) →
      ρ.dropLeftmost ∈ Set.range (finRule (wolframRule 106) hq) := by
  intro n
  induction n with
  | zero =>
    intro c _ h
    rw [Finset.sum_range_zero, add_zero, translate_mem_range_wolfram106] at h
    exact h
  | succ n ih =>
    intro c hc h
    have hsplit := mem_range_or_dropLeftmost_mem_range_wolfram106 hq (A := translate (c 0)
      ρ.dropLeftmost) (B := (Finset.range (n + 1)).sum fun m => translate (c (m + 1)) ρ)
      (blocks_gap (n := n) hc (fun i hi => by
        have := ne_zero_of_dropLeftmost_ne_zero (translate_apply' _ _ _ ▸ hi)
        exact this)) h
    rcases hsplit with h1 | h1
    · exact (translate_mem_range_wolfram106 hq _).mp h1
    · rw [blocks_drop hρ0 hc] at h1
      exact ih (fun m => c (m + 1)) (fun j hj => hc (j + 1) (by omega)) h1

/-- **The condition on a reproduced state with no predecessor**: if rule `106` reproduces a state
with no predecessor, the state with its leftmost set cell cleared has one. Some iterate past the
first is at least two copies of the state, at gaps of at least two clear cells; the split at the
first copy, which has no predecessor, and then at each later copy with its leftmost cell cleared,
leaves the cleared state with a predecessor ([RuleSpace] §5). -/
theorem Reproduces.dropLeftmost_mem_range_wolfram106 (hq : wolframRule 106 0 0 0 = 0)
    {ρ : FiniteConfiguration} (hρ : ρ ∉ Set.range (finRule (wolframRule 106) hq))
    (h : Reproduces (finRule (wolframRule 106) hq) ρ) :
    ρ.dropLeftmost ∈ Set.range (finRule (wolframRule 106) hq) := by
  have hρ0 := h.1
  obtain ⟨t, k, hk, c, hc, hs⟩ := h.2 2 2
  have ht : t ≠ 0 := by
    rintro rfl
    have h1 := copies_diam_le hρ0 ⟨c, hc, hs⟩ (by omega)
    have h2 := one_le_diam_of_ne_zero hρ0
    rw [Function.iterate_zero, id] at h1
    nlinarith
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hmem : ((Finset.range (n + 2)).sum fun j => FiniteConfiguration.translate (c j) ρ) ∈
      Set.range (finRule (wolframRule 106) hq) := by
    rw [← hs]
    obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
    exact ⟨(finRule (wolframRule 106) hq)^[t'] ρ, Function.iterate_succ_apply' _ _ _ ▸ rfl⟩
  rw [Finset.sum_range_succ', add_comm] at hmem
  have hsplit := mem_range_or_dropLeftmost_mem_range_wolfram106 hq
    (A := FiniteConfiguration.translate (c 0) ρ)
    (B := (Finset.range (n + 1)).sum fun m => FiniteConfiguration.translate (c (m + 1)) ρ)
    (blocks_gap (n := n) hc (fun i hi => by rwa [translate_apply'] at hi)) hmem
  rcases hsplit with h1 | h1
  · exact absurd ((translate_mem_range_wolfram106 hq _).mp h1) hρ
  · rw [blocks_drop hρ0 hc] at h1
    exact dropLeftmost_mem_range_of_blocks hq hρ0 n (fun m => c (m + 1))
      (fun j hj => hc (j + 1) (by omega)) h1

/-- The condition has a fixed instance: the pair `11` has no predecessor and is reproduced, and the
pair with its leftmost cell cleared, the cell `1`, has a predecessor. -/
theorem Reproduces.dropLeftmost_mem_range_wolfram106_nonvacuous (hq : wolframRule 106 0 0 0 = 0) :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∉
        Set.range (finRule (wolframRule 106) hq) ∧
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 : FiniteConfiguration).dropLeftmost
        = Finsupp.single 1 1 ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 : FiniteConfiguration).dropLeftmost
        ∈ Set.range (finRule (wolframRule 106) hq) := by
  have hrep : Reproduces (finRule (wolframRule 106) hq)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) := by
    simpa using reproduces_wolfram106_orbit hq 0
  have hd := dropLeftmost_single_add_single (by omega : (0 : ℤ) < 1)
  refine ⟨pair_notMem_range_wolfram106 hq, hrep, hd, ?_⟩
  exact Reproduces.dropLeftmost_mem_range_wolfram106 hq (pair_notMem_range_wolfram106 hq) hrep

/-- **The hypothesis that the state has no predecessor is load-bearing**: the image of the pair
`11` is the three cells `-1`, `0` and `1`; it is reproduced and has a predecessor, and with its
leftmost cell cleared, the pair, it has none. -/
theorem Reproduces.dropLeftmost_mem_range_wolfram106_root_load_bearing
    (hq : wolframRule 106 0 0 0 = 0) :
    finRule (wolframRule 106) hq (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) =
        Finsupp.single (-1 : ℤ) (1 : ZMod 2) + Finsupp.single 0 1 + Finsupp.single 1 1 ∧
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.single (-1 : ℤ) (1 : ZMod 2) + Finsupp.single 0 1 + Finsupp.single 1 1) ∧
      (Finsupp.single (-1 : ℤ) (1 : ZMod 2) + Finsupp.single 0 1 + Finsupp.single 1 1 :
          FiniteConfiguration) ∈ Set.range (finRule (wolframRule 106) hq) ∧
      (Finsupp.single (-1 : ℤ) (1 : ZMod 2) + Finsupp.single 0 1 + Finsupp.single 1 1 :
          FiniteConfiguration).dropLeftmost =
        Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 ∧
      (Finsupp.single (-1 : ℤ) (1 : ZMod 2) + Finsupp.single 0 1 + Finsupp.single 1 1 :
          FiniteConfiguration).dropLeftmost ∉ Set.range (finRule (wolframRule 106) hq) := by
  have himg : finRule (wolframRule 106) hq
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) =
      Finsupp.single (-1 : ℤ) (1 : ZMod 2) + Finsupp.single 0 1 + Finsupp.single 1 1 := by
    ext i
    rw [finRule_wolfram106_apply]
    rcases (by omega : i < -2 ∨ (-2 ≤ i ∧ i ≤ 3) ∨ 3 < i) with h | h | h
    · simp (disch := omega) only [Finsupp.single_eq_of_ne, Finsupp.add_apply, add_zero, mul_zero]
    · obtain ⟨h1, h2⟩ := h
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      interval_cases i <;> decide
    · simp (disch := omega) only [Finsupp.single_eq_of_ne, Finsupp.add_apply, add_zero, mul_zero]
  have hdrop : (Finsupp.single (-1 : ℤ) (1 : ZMod 2) + Finsupp.single 0 1 + Finsupp.single 1 1 :
      FiniteConfiguration).dropLeftmost =
      Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 := by
    rw [add_assoc]
    apply dropLeftmost_single_add
    intro j hj
    rcases pair_apply_ne_zero hj with h | h <;> omega
  refine ⟨himg, ?_, ?_, hdrop, ?_⟩
  · have := reproduces_wolfram106_orbit hq 1
    rwa [Function.iterate_one, himg] at this
  · exact ⟨_, himg⟩
  · rw [hdrop]
    exact pair_notMem_range_wolfram106 hq

/-! ## The states whose only adjacent set cells are their two rightmost -/

private theorem zmod2_sum_eq_zero_one (u : ZMod 2) (h : u + 1 * 1 = 0) : u = 1 := by
  revert u
  decide

/-- **A state whose only adjacent set cells are its two rightmost has no predecessor at rule
`106`**: a predecessor copies the state shifted by one cell up to the pair, where it is set at the
pair's cells and from then on set forever, against finite support ([RuleSpace] §5). -/
theorem FiniteConfiguration.RightPairOnly.notMem_range_wolfram106
    (hq : wolframRule 106 0 0 0 = 0) {s : FiniteConfiguration} (hs : s.RightPairOnly) :
    s ∉ Set.range (finRule (wolframRule 106) hq) := by
  obtain ⟨r, hr, hr1, hrz, hadj⟩ := hs
  rintro ⟨x, hx⟩
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [finRule_zero' _ hq] at hx
    exact hr (by rw [← hx]; rfl)
  have hne : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hxne
  obtain ⟨L, hL⟩ : ∃ L, L = x.support.min' hne := ⟨_, rfl⟩
  have hlow : ∀ i, i < L → x i = 0 := fun i hi => below_min'_eq_zero hne (by omega)
  have hcell : ∀ j, x j + x (j - 2) * x (j - 1) = s (j - 1) := fun j => by
    have := finRule_wolfram106_apply hq x (j - 1)
    rw [hx, show j - 1 + 1 = j by ring, show j - 1 - 1 = j - 2 by ring] at this
    exact this.symm
  have hprod : ∀ j, j ≤ r + 1 → s (j - 3) * s (j - 2) = 0 := fun j hj => by
    by_contra h0
    have h1 : s (j - 3) ≠ 0 := left_ne_zero_of_mul h0
    have h2 : s (j - 3 + 1) ≠ 0 := by
      rw [show j - 3 + 1 = j - 2 by ring]
      exact right_ne_zero_of_mul h0
    have := hadj (j - 3) h1 h2
    omega
  have hP : ∀ n : ℕ, ∀ j, j ≤ r + 1 → j ≤ L + n → x j = s (j - 1) := by
    intro n
    induction n with
    | zero =>
      intro j _ hj
      have := hcell j
      rw [hlow (j - 1) (by omega), mul_zero, add_zero] at this
      exact this
    | succ n ih =>
      intro j hj1 hj2
      by_cases hj3 : j ≤ L + n
      · exact ih j hj1 hj3
      · have h := hcell j
        rw [ih (j - 2) (by omega) (by omega), ih (j - 1) (by omega) (by omega),
          show j - 2 - 1 = j - 3 by ring, show j - 1 - 1 = j - 2 by ring, hprod j hj1,
          add_zero] at h
        exact h
  have hxr : x r = 1 := by
    rw [hP (r + 1 - L).toNat r (by omega) (by omega)]
    exact zmod2_eq_one_of_ne_zero' _ hr1
  have hxr1 : x (r + 1) = 1 := by
    rw [hP (r + 1 - L).toNat (r + 1) le_rfl (by omega), show r + 1 - 1 = r by ring]
    exact zmod2_eq_one_of_ne_zero' _ hr
  have hup : ∀ n : ℕ, x (r + n) = 1 ∧ x (r + n + 1) = 1 := by
    intro n
    induction n with
    | zero => simpa using ⟨hxr, hxr1⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have h := hcell (r + n + 2)
      rw [show r + n + 2 - 2 = r + n by ring, show r + n + 2 - 1 = r + n + 1 by ring, h1, h2,
        hrz _ (by omega)] at h
      refine ⟨by push_cast; rw [show r + (n + 1) = r + n + 1 by ring]; exact h2, ?_⟩
      push_cast
      rw [show r + (n + 1) + 1 = r + n + 2 by ring]
      exact zmod2_sum_eq_zero_one _ h
  obtain ⟨hu1, -⟩ := hup (x.support.max' hne - r + 1).toNat
  have h0 : x (r + ((x.support.max' hne - r + 1).toNat : ℤ)) = 0 :=
    above_max'_eq_zero hne (by omega)
  rw [h0] at hu1
  exact absurd hu1 (by decide)

/-- Clearing the leftmost set cell of such a state of diameter more than two leaves such a
state. -/
theorem FiniteConfiguration.RightPairOnly.dropLeftmost {s : FiniteConfiguration}
    (hs : s.RightPairOnly) (h2 : 2 < diam s) : s.dropLeftmost.RightPairOnly := by
  obtain ⟨r, hr, hr1, hrz, hadj⟩ := hs
  have hne : s.support.Nonempty := ⟨r, Finsupp.mem_support_iff.mpr hr⟩
  have hmax : s.support.max' hne = r := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      by_contra h
      exact (Finsupp.mem_support_iff.mp hy) (hrz y (by omega))
    · exact Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hr)
  have hmin : s.support.min' hne ≤ r - 1 :=
    Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hr1)
  have hd := diam_eq' hne
  have hlt : s.support.min' hne < r - 1 := by omega
  refine ⟨r, ?_, ?_, fun i hi => ?_, fun i hi hi1 => ?_⟩
  · rw [dropLeftmost_apply hne, ite_eq_right (by omega)]
    exact hr
  · rw [dropLeftmost_apply hne, ite_eq_right (by omega)]
    exact hr1
  · rw [dropLeftmost_apply hne]
    by_cases h : i = s.support.min' hne
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact hrz i hi
  · exact hadj i (ne_zero_of_dropLeftmost_ne_zero hi) (ne_zero_of_dropLeftmost_ne_zero hi1)

private theorem triple_apply_ne_zero {a b c j : ℤ}
    (h : (Finsupp.single a (1 : ZMod 2) + Finsupp.single b 1 + Finsupp.single c 1 :
      FiniteConfiguration) j ≠ 0) : j = a ∨ j = b ∨ j = c := by
  by_contra hn
  push Not at hn
  apply h
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
    Finsupp.single_apply, ite_eq_right (Ne.symm hn.1), ite_eq_right (Ne.symm hn.2.1),
    ite_eq_right (Ne.symm hn.2.2), add_zero, add_zero]

private theorem triple_rightPairOnly :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1 + Finsupp.single 3 1 :
      FiniteConfiguration).RightPairOnly := by
  refine ⟨3, by simp, by simp, fun i hi => ?_,
    fun i hi hi1 => ?_⟩
  · simp (disch := omega) only [Finsupp.add_apply, Finsupp.single_eq_of_ne, add_zero]
  · rcases triple_apply_ne_zero hi with h | h | h
    · subst h
      exact absurd hi1 (by simp)
    · omega
    · subst h
      exact absurd hi1 (by simp)

/-- The family has a fixed instance: the state with cells `0`, `2` and `3` is such a state, and has
no predecessor at rule `106`. -/
theorem FiniteConfiguration.RightPairOnly.notMem_range_wolfram106_nonvacuous
    (hq : wolframRule 106 0 0 0 = 0) :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1 + Finsupp.single 3 1 :
        FiniteConfiguration).RightPairOnly ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1 + Finsupp.single 3 1 :
        FiniteConfiguration) ∉ Set.range (finRule (wolframRule 106) hq) :=
  ⟨triple_rightPairOnly, triple_rightPairOnly.notMem_range_wolfram106 hq⟩

/-- **Rule `106` reproduces a state whose only adjacent set cells are its two rightmost exactly
when it is the pair**: such a state has no predecessor, and so does the state with its leftmost
cell cleared when the state is wider than the pair, against the condition on a reproduced state
with no predecessor; the pair, and so each of its translates, is reproduced ([RuleSpace] §5). -/
theorem FiniteConfiguration.RightPairOnly.reproduces_wolfram106_iff
    (hq : wolframRule 106 0 0 0 = 0) {s : FiniteConfiguration} (hs : s.RightPairOnly) :
    Reproduces (finRule (wolframRule 106) hq) s ↔ diam s = 2 := by
  obtain ⟨r, hr, hr1, hrz, hadj⟩ := hs
  have hs' : s.RightPairOnly := ⟨r, hr, hr1, hrz, hadj⟩
  have hne : s.support.Nonempty := ⟨r, Finsupp.mem_support_iff.mpr hr⟩
  have hmax : s.support.max' hne = r := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      by_contra h
      exact (Finsupp.mem_support_iff.mp hy) (hrz y (by omega))
    · exact Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hr)
  have hge := le_diam_of_cells hr1 hr
  constructor
  · intro h
    by_contra hd
    have h3 := Reproduces.dropLeftmost_mem_range_wolfram106 hq
      (hs'.notMem_range_wolfram106 hq) h
    exact (hs'.dropLeftmost (by omega)).notMem_range_wolfram106 hq h3
  · intro hd
    have hmin : s.support.min' hne = r - 1 := by
      have := diam_eq' hne
      have hle : s.support.min' hne ≤ r - 1 :=
        Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hr1)
      omega
    have hlow : ∀ i, i < r - 1 → s i = 0 := fun i hi => below_min'_eq_zero hne (by omega)
    have heq : s = FiniteConfiguration.translate (r - 1)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) := by
      ext i
      rw [translate_apply', Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      rcases (by omega : i < r - 1 ∨ i = r - 1 ∨ i = r ∨ r < i) with h | h | h | h
      · rw [hlow i h, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
      · subst h
        rw [ite_eq_left (by omega), ite_eq_right (by omega), add_zero]
        exact zmod2_eq_one_of_ne_zero' _ hr1
      · subst h
        rw [ite_eq_right (by omega), ite_eq_left (by omega), zero_add]
        exact zmod2_eq_one_of_ne_zero' _ hr
      · rw [hrz i h, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
    rw [heq]
    exact Reproduces.translate (wolframRule 106) hq
      (by simpa using reproduces_wolfram106_orbit hq 0) (r - 1)

/-- **Rule `106` does not reproduce the state `1011`**, the cells `0`, `2` and `3`: it is wider than
the pair. -/
theorem not_reproduces_wolfram106_single_zero_add_single_two_add_single_three
    (hq : wolframRule 106 0 0 0 = 0) :
    ¬ Reproduces (finRule (wolframRule 106) hq)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1 + Finsupp.single 3 1) := by
  intro h
  have h2 := (triple_rightPairOnly.reproduces_wolfram106_iff hq).mp h
  have h3 := le_diam_of_cells (s := (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1 +
    Finsupp.single 3 1 : FiniteConfiguration)) (a := 0) (b := 3) (by simp)
    (by simp)
  omega

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.dropLeftmost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.dropLeftmost_zero

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.dropLeftmost_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.dropLeftmost_apply

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.dropLeftmost_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.dropLeftmost_translate

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.dropLeftmost_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.dropLeftmost_add

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.dropLeftmost_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.dropLeftmost_single

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.dropLeftmost_single_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.dropLeftmost_single_add

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.dropLeftmost_single_add_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.dropLeftmost_single_add_single

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.ne_zero_of_dropLeftmost_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.ne_zero_of_dropLeftmost_ne_zero

set_option linter.style.longLine false in
/-- info: 'ECA.pair_notMem_range_wolfram106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.pair_notMem_range_wolfram106

set_option linter.style.longLine false in
/-- info: 'ECA.mem_range_or_dropLeftmost_mem_range_wolfram106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.mem_range_or_dropLeftmost_mem_range_wolfram106

set_option linter.style.longLine false in
/-- info: 'ECA.mem_range_or_dropLeftmost_mem_range_wolfram106_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.mem_range_or_dropLeftmost_mem_range_wolfram106_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.dropLeftmost_mem_range_wolfram106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.dropLeftmost_mem_range_wolfram106

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.dropLeftmost_mem_range_wolfram106_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.dropLeftmost_mem_range_wolfram106_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.dropLeftmost_mem_range_wolfram106_root_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.dropLeftmost_mem_range_wolfram106_root_load_bearing

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.RightPairOnly.notMem_range_wolfram106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.RightPairOnly.notMem_range_wolfram106

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.RightPairOnly.dropLeftmost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.RightPairOnly.dropLeftmost

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.RightPairOnly.notMem_range_wolfram106_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.RightPairOnly.notMem_range_wolfram106_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.RightPairOnly.reproduces_wolfram106_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.RightPairOnly.reproduces_wolfram106_iff

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram106_single_zero_add_single_two_add_single_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram106_single_zero_add_single_two_add_single_three
