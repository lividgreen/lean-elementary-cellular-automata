module

public import ECA.ReproducedPatterns
public import ECA.EndpointClasses
import all ECA.EndpointClasses
import all ECA.ReproductionBracket
import all ECA.ReproducedPatterns

/-!
# Two defect counts, and the patterns a rule cannot reproduce
([RuleSpace] §5)

[RuleSpace] §5 Proposition 5.25 shows that a rule agreeing with rule `90` off adjacent cells
reproduces every nonzero pattern whose set cells differ by even amounts, and that a rule agreeing
with it at equal adjacent cells reproduces every nonzero doubled pattern. This module shows the
converse for a rule whose defect count never increases in one step.

* `FiniteConfiguration.kinkCount` — the number of set cells whose next set cell lies at odd
  distance: the kinks `1 0^(2n) 1` of Sabrié and Törmä (2023), after Kůrka (2003). It vanishes
  exactly on the states of one parity (`FiniteConfiguration.kinkCount_eq_zero_iff`).
* `FiniteConfiguration.oddRunCount` — the number of maximal runs of set cells and of internal clear
  runs of odd length, the kink count of the boundary state. It vanishes exactly on the translates of
  a doubled state (`FiniteConfiguration.oddRunCount_eq_zero_iff`).
* `not_reproduces_of_count_mono` — a count that one step never increases, and that `k` copies at a
  positive gap carry at least `k` times, excludes the reproduction of any pattern of positive
  count.
* `LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity` and
  `LocalRule.DoubledAgree.reproduces_iff_dbl` — under the monotonicity of the count and the copies
  bound, the patterns the rule reproduces are exactly the nonzero ones of the class
  ([RuleSpace] §5 Proposition 5.25).

* `kinkCountCopies` and `oddRunCountCopies` — the copies bounds `KinkCountCopies` and
  `OddRunCountCopies` are proved: `k` copies carry at least `k` times the count of one, the
  odd-run bound at every positive gap.

The two theorems at the class take the monotonicity of the count under one step, stated as
`LocalRule.KinkCountMono` and `LocalRule.OddRunCountMono`, and the copies bound as hypotheses.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The counts -/

/-- **The kink count**: the number of set cells of `s` whose next set cell lies at odd distance,
that is, the number of words `1 0^(2n) 1` of `s` (Sabrié and Törmä 2023, after Kůrka 2003). -/
def FiniteConfiguration.kinkCount (s : FiniteConfiguration) : ℕ :=
  (s.support.filter fun i =>
    ∃ j ∈ s.support, i < j ∧ Odd (j - i) ∧ ∀ m ∈ s.support, m ≤ i ∨ j ≤ m).card

/-- **The boundary of a state**: the cells `i` with `s i ≠ s (i + 1)`, as the finitely supported
state `i ↦ s i + s (i + 1)`. A run of set cells occupying `a..b` has boundaries at `a - 1` and
`b`. -/
noncomputable def FiniteConfiguration.boundary (s : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.onFinset (s.support ∪ s.support.image (· - 1)) (fun i => s i + s (i + 1)) (by
    intro i hi
    by_cases h : s i = 0
    · rw [h, zero_add] at hi
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i + 1, ?_, by ring⟩)
      exact Finsupp.mem_support_iff.mpr hi
    · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))

/-- **The odd-run count**: the number of maximal runs of set cells and of internal clear runs of
odd length, the kink count of the boundary state. -/
noncomputable def FiniteConfiguration.oddRunCount (s : FiniteConfiguration) : ℕ :=
  kinkCount (boundary s)

/-- The boundary state at a cell. -/
theorem FiniteConfiguration.boundary_apply (s : FiniteConfiguration) (i : ℤ) :
    boundary s i = s i + s (i + 1) := by
  simp [boundary, Finsupp.onFinset_apply]

/-! ## The counts on small states -/

private theorem support_of_cells {s : FiniteConfiguration} {S : Finset ℤ}
    (h : ∀ i, s i ≠ 0 ↔ i ∈ S) : s.support = S := by
  ext i
  rw [Finsupp.mem_support_iff, h]

private theorem kinkCount_of_support {s : FiniteConfiguration} {S : Finset ℤ}
    (h : s.support = S) : kinkCount s = (S.filter fun i =>
      ∃ j ∈ S, i < j ∧ Odd (j - i) ∧ ∀ m ∈ S, m ≤ i ∨ j ≤ m).card := by
  unfold kinkCount
  rw [h]

/-- Closes the cell-by-cell description of a small state's boundary. -/
local macro "cells_iff" : tactic =>
  `(tactic| (split_ifs <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;>
    first | omega | (constructor <;> intro h <;>
      first | omega | exact absurd h (by decide) | decide)))

private theorem oddRunCount_of_boundary {s : FiniteConfiguration} {S : Finset ℤ}
    (h : ∀ i, s i + s (i + 1) ≠ 0 ↔ i ∈ S) : oddRunCount s = (S.filter fun i =>
      ∃ j ∈ S, i < j ∧ Odd (j - i) ∧ ∀ m ∈ S, m ≤ i ∨ j ≤ m).card :=
  kinkCount_of_support (support_of_cells fun i => by rw [boundary_apply]; exact h i)

private noncomputable abbrev unitCell : FiniteConfiguration := Finsupp.single (0 : ℤ) (1 : ZMod 2)

example : kinkCount (unitCell + Finsupp.single 1 1) = 1 := by
  rw [kinkCount_of_support (S := {0, 1}) (support_of_cells fun i => by
    simp only [unitCell, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> simp_all <;> omega)]
  decide

example : kinkCount (unitCell + Finsupp.single 2 1) = 0 := by
  rw [kinkCount_of_support (S := {0, 2}) (support_of_cells fun i => by
    simp only [unitCell, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> simp_all <;> omega)]
  decide

example : kinkCount (unitCell + Finsupp.single 3 1) = 1 := by
  rw [kinkCount_of_support (S := {0, 3}) (support_of_cells fun i => by
    simp only [unitCell, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> simp_all <;> omega)]
  decide

example : oddRunCount unitCell = 1 := by
  rw [oddRunCount_of_boundary (S := {-1, 0}) fun i => by
    simp only [unitCell, Finsupp.single_apply]; cells_iff]
  decide

example : oddRunCount (unitCell + Finsupp.single 1 1) = 0 := by
  rw [oddRunCount_of_boundary (S := {-1, 1}) fun i => by
    simp only [unitCell, Finsupp.add_apply, Finsupp.single_apply]; cells_iff]
  decide

example : oddRunCount (unitCell + Finsupp.single 1 1 + Finsupp.single 2 1) = 1 := by
  rw [oddRunCount_of_boundary (S := {-1, 2}) fun i => by
    simp only [unitCell, Finsupp.add_apply, Finsupp.single_apply]; cells_iff]
  decide

example : oddRunCount (unitCell + Finsupp.single 3 1) = 2 := by
  rw [oddRunCount_of_boundary (S := {-1, 0, 2, 3}) fun i => by
    simp only [unitCell, Finsupp.add_apply, Finsupp.single_apply]; cells_iff]
  decide

/-! ## The counts vanish exactly on the classes -/

/-- **The kink count vanishes exactly on the states of one parity**: with no two consecutive set
cells at odd distance, the chain of set cells from one to the next steps by even amounts. -/
theorem FiniteConfiguration.kinkCount_eq_zero_iff (s : FiniteConfiguration) :
    kinkCount s = 0 ↔ OneParity s := by
  unfold kinkCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    have key : ∀ d : ℕ, ∀ i j : ℤ, i ∈ s.support → j ∈ s.support → i < j →
        (j - i).toNat = d → Even (j - i) := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro i j hi hj hij hd
        have hne : (s.support.filter (fun m => i < m)).Nonempty := ⟨j, by simp [hj, hij]⟩
        have hnmem := Finset.min'_mem _ hne
        rw [Finset.mem_filter] at hnmem
        have hnle : (s.support.filter (fun m => i < m)).min' hne ≤ j :=
          Finset.min'_le _ _ (by simp [hj, hij])
        have hmin : ∀ m ∈ s.support, m ≤ i ∨ (s.support.filter (fun m => i < m)).min' hne ≤ m := by
          intro m hm
          by_cases hmi : m ≤ i
          · exact Or.inl hmi
          · exact Or.inr (Finset.min'_le _ _ (by simp [hm]; omega))
        have hev : Even ((s.support.filter (fun m => i < m)).min' hne - i) := by
          by_contra hodd
          rw [Int.not_even_iff_odd] at hodd
          exact h hi ⟨_, hnmem.1, hnmem.2, hodd, hmin⟩
        rcases eq_or_lt_of_le hnle with heq | hlt
        · rw [← heq]; exact hev
        · have h2 := ih (j - (s.support.filter (fun m => i < m)).min' hne).toNat
            (by have := hnmem.2; omega) _ j hnmem.1 hj hlt rfl
          have h3 : j - i = (j - (s.support.filter (fun m => i < m)).min' hne) +
              ((s.support.filter (fun m => i < m)).min' hne - i) := by ring
          rw [h3]
          exact h2.add hev
    intro i j hi hj
    have hi' := Finsupp.mem_support_iff.mpr hi
    have hj' := Finsupp.mem_support_iff.mpr hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have := key _ i j hi' hj' hlt rfl
      have h2 := this.neg
      rwa [neg_sub] at h2
    · simp
    · exact key _ j i hj' hi' hgt rfl
  · intro hop i hi ⟨j, hj, _, hodd, _⟩
    have h1 := hop i j (Finsupp.mem_support_iff.mp hi) (Finsupp.mem_support_iff.mp hj)
    have h2 := h1.neg
    rw [neg_sub] at h2
    exact (Int.not_even_iff_odd.mpr hodd) h2

private theorem ZMod2_eq_of_add_eq_zero (a b : ZMod 2) (h : a + b = 0) : a = b := by
  revert a b; decide

private theorem translate_zero_state (c : ℤ) : translate c (0 : FiniteConfiguration) = 0 := by
  simp [translate]

private theorem dbl_zero_state : dbl (0 : FiniteConfiguration) = 0 := by
  ext j
  simp [dbl_apply]

/-- **The odd-run count vanishes exactly on the translates of a doubled state**: all boundaries of
one parity make every run and every internal gap even. -/
theorem FiniteConfiguration.oddRunCount_eq_zero_iff (s : FiniteConfiguration) :
    oddRunCount s = 0 ↔ ∃ x c, s = translate c (dbl x) := by
  unfold oddRunCount
  rw [kinkCount_eq_zero_iff]
  constructor
  · intro hop
    by_cases hs : s = 0
    · exact ⟨0, 0, by rw [hs, dbl_zero_state, translate_zero_state]⟩
    have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    set c := s.support.min' hne with hcdef
    have hc : s c ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
    have hbelow : s (c - 1) = 0 := by
      by_contra hne'
      have := Finset.min'_le s.support (c - 1) (Finsupp.mem_support_iff.mpr hne')
      omega
    have hb0 : boundary s (c - 1) ≠ 0 := by
      rw [boundary_apply, hbelow, zero_add, sub_add_cancel]
      exact hc
    have hbq : ∀ q : ℤ, s (c + 2 * q) = s (c + 2 * q + 1) := by
      intro q
      have h0 : boundary s (c + 2 * q) = 0 := by
        by_contra hb
        have := hop _ _ hb hb0
        obtain ⟨r, hr⟩ := this
        omega
      rw [boundary_apply] at h0
      exact ZMod2_eq_of_add_eq_zero _ _ h0
    obtain ⟨x, hx⟩ : ∃ x : FiniteConfiguration, ∀ j, x j = s (c + 2 * j) :=
      ⟨Finsupp.comapDomain (fun j : ℤ => c + 2 * j) s (by
        intro a _ b _ h; simp only at h; omega), fun j => rfl⟩
    refine ⟨x, c, ?_⟩
    ext i
    rw [translate_apply', dbl_apply, hx]
    obtain ⟨q, hq⟩ : ∃ q, i - c = 2 * q ∨ i - c = 2 * q + 1 := ⟨(i - c) / 2, by omega⟩
    rcases hq with hq | hq
    · have : (i - c) / 2 = q := by omega
      rw [this]
      have : i = c + 2 * q := by omega
      rw [this]
    · have : (i - c) / 2 = q := by omega
      rw [this]
      have : i = c + 2 * q + 1 := by omega
      rw [this]
      exact (hbq q).symm
  · rintro ⟨x, c, rfl⟩
    have hodd : ∀ i, boundary (translate c (dbl x)) i ≠ 0 → Odd (i - c) := by
      intro i hi
      by_contra hev
      rw [Int.not_odd_iff_even] at hev
      obtain ⟨q, hq⟩ := hev
      apply hi
      rw [boundary_apply, translate_apply', translate_apply', dbl_apply, dbl_apply]
      have e1 : (i - c) / 2 = q := by omega
      have e2 : (i + 1 - c) / 2 = q := by omega
      rw [e1, e2]
      exact CharTwo.add_self_eq_zero _
    intro i j hi hj
    have := (hodd i hi).sub_odd (hodd j hj)
    rwa [show i - c - (j - c) = i - j by ring] at this

/-! ## A count that one step never increases excludes reproduction -/

/-- **The kink count never increases in one step of the rule**: `f` is quiescent by `hq`, and the
image of every state has at most as many kinks as the state. -/
def LocalRule.KinkCountMono (f : LocalRule) (hq : f 0 0 0 = 0) : Prop :=
  ∀ s : FiniteConfiguration, kinkCount (finRule f hq s) ≤ kinkCount s

/-- **`k` copies of a pattern carry at least `k` times its kinks**, at every gap: the consecutive
set cells of each copy stay consecutive in the sum. -/
def KinkCountCopies : Prop :=
  ∀ (p s : FiniteConfiguration) (k G : ℕ), Copies p s k G → k * kinkCount p ≤ kinkCount s

/-- **The odd-run count never increases in one step of the rule**: `f` is quiescent by `hq`, and
the image of every state has at most as many odd runs as the state. -/
def LocalRule.OddRunCountMono (f : LocalRule) (hq : f 0 0 0 = 0) : Prop :=
  ∀ s : FiniteConfiguration, oddRunCount (finRule f hq s) ≤ oddRunCount s

/-- **`k` copies of a pattern at a positive gap carry at least `k` times its odd runs**: the runs
of each copy stay maximal in the sum when a clear cell separates the copies. -/
def OddRunCountCopies : Prop :=
  ∀ (p s : FiniteConfiguration) (k G : ℕ), 1 ≤ G → Copies p s k G →
    k * oddRunCount p ≤ oddRunCount s

/-- **A count that one step never increases, and that `k` copies at a positive gap carry at least
`k` times, excludes reproduction of every pattern of positive count**: along the orbit of `p` the
count stays at most that of `p`, while at least `count p + 1` copies carry more. -/
theorem not_reproduces_of_count_mono (U : FiniteConfiguration → FiniteConfiguration)
    (Φ : FiniteConfiguration → ℕ) (hmono : ∀ s, Φ (U s) ≤ Φ s)
    (hcopies : ∀ p s k G, 1 ≤ G → Copies p s k G → k * Φ p ≤ Φ s)
    {p : FiniteConfiguration} (hp : 1 ≤ Φ p) : ¬ Reproduces U p := by
  rintro ⟨_, h⟩
  obtain ⟨t, k, hk, hc⟩ := h (Φ p + 1) 1
  have hit : ∀ t, Φ (U^[t] p) ≤ Φ p := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Function.iterate_succ_apply']; exact (hmono _).trans ih
  have h1 := hcopies p _ k 1 le_rfl hc
  have h2 := hit t
  nlinarith

private theorem exists_ends_defect {p : FiniteConfiguration} (hp : p ≠ 0) :
    ∃ a b : ℤ, (∀ i, p i ≠ 0 → a ≤ i ∧ i ≤ b) ∧ (diam p : ℤ) = b - a + 1 := by
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmM := Finset.min'_le_max' p.support hpne
  refine ⟨p.support.min' hpne, p.support.max' hpne, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hi)
  · exact Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hi)
  · unfold diam
    rw [dite_eq_left hpne]
    have : (0 : ℤ) ≤ p.support.max' hpne - p.support.min' hpne := by omega
    omega

/-- **Copies of a pattern carry at least `k` times its set cells**: the supports of the copies are
disjoint. -/
theorem card_support_copies_le {p s : FiniteConfiguration} {k G : ℕ} (h : Copies p s k G) :
    k * p.support.card ≤ s.support.card := by
  obtain ⟨c, hc, rfl⟩ := h
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨a, b, hab, hd⟩ := exists_ends_defect hp
  have hord : ∀ j l, j < l → l < k → c j + diam p ≤ c l := by
    intro j l hjl hlk
    obtain ⟨n, rfl⟩ : ∃ n, l = j + (n + 1) := ⟨l - j - 1, by omega⟩
    have := offsets_mono hc (n + 1) j hlk
    push_cast at this
    have h1 : (0 : ℤ) ≤ n * diam p := by positivity
    linarith
  have hev : ∀ x, ((Finset.range k).sum fun j => translate (c j) p) x
      = (Finset.range k).sum fun j => p (x - c j) := by
    intro x
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun j _ => translate_apply' _ _ _
  have hcard : (Finset.range k ×ˢ p.support).card = k * p.support.card := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun q => q.2 + c q.1) (fun q hq => ?_)
    (fun q hq q' hq' he => ?_)
  · obtain ⟨hj, hi⟩ := Finset.mem_product.mp hq
    have hj' := Finset.mem_range.mp hj
    have hi' := Finsupp.mem_support_iff.mp hi
    have hbd := hab _ hi'
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hev, Finset.sum_eq_single q.1]
    · simpa using hi'
    · intro l hl hlj
      have hl' := Finset.mem_range.mp hl
      by_contra hne
      beta_reduce at hne
      have := hab _ hne
      rcases lt_or_gt_of_ne hlj with hlt | hgt
      · have := hord l q.1 hlt hj'
        omega
      · have := hord q.1 l hgt hl'
        omega
    · intro hn; exact absurd (Finset.mem_range.mpr hj') hn
  · obtain ⟨hj, hi⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hq)
    obtain ⟨hj2, hi2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hq')
    have hj' := Finset.mem_range.mp hj
    have hj2' := Finset.mem_range.mp hj2
    have hb1 := hab _ (Finsupp.mem_support_iff.mp hi)
    have hb2 := hab _ (Finsupp.mem_support_iff.mp hi2)
    simp only at he
    have hq1 : q.1 = q'.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hord _ _ hlt hj2'
        omega
      · have := hord _ _ hgt hj'
        omega
    have : q.2 = q'.2 := by rw [hq1] at he; omega
    exact Prod.ext hq1 this

/-! ## The classes, from above -/

/-- **A rule whose kink count never increases and whose copies carry the kinks reproduces exactly
the nonzero one-parity patterns**: a rule agreeing with rule `90` off adjacent cells reproduces
every nonzero pattern of one parity ([RuleSpace] §5 Proposition 5.25), and a pattern with a kink
is excluded by the kink count. -/
theorem LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity (f : LocalRule)
    (h : AgreesOffAdjacent f) (hm : KinkCountMono f h.1) (hc : KinkCountCopies)
    (p : FiniteConfiguration) :
    Reproduces (finRule f h.1) p ↔ p ≠ 0 ∧ OneParity p := by
  constructor
  · intro hr
    refine ⟨hr.1, ?_⟩
    by_contra hnp
    have h1 : 1 ≤ kinkCount p :=
      Nat.pos_of_ne_zero fun h0 => hnp ((kinkCount_eq_zero_iff p).mp h0)
    exact not_reproduces_of_count_mono (finRule f h.1) kinkCount hm
      (fun p s k G _ => hc p s k G) h1 hr
  · rintro ⟨hp, hs⟩
    exact LocalRule.AgreesOffAdjacent.reproduces_of_oneParity f h hs hp

/-- **A rule whose odd-run count never increases and whose copies at a positive gap carry the odd
runs reproduces exactly the nonzero translates of doubled patterns**: a rule agreeing with rule
`90` at equal adjacent cells reproduces every nonzero doubled pattern ([RuleSpace] §5 Proposition
5.25) and every translate of one ([RuleSpace] §5 Proposition 5.26), and a pattern with an odd run
is excluded by the odd-run count. -/
theorem LocalRule.DoubledAgree.reproduces_iff_dbl (f : LocalRule) (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (hm : OddRunCountMono f hq) (hc : OddRunCountCopies)
    (p : FiniteConfiguration) :
    Reproduces (finRule f hq) p ↔ p ≠ 0 ∧ ∃ x c, p = translate c (dbl x) := by
  constructor
  · intro hr
    refine ⟨hr.1, ?_⟩
    by_contra hnp
    have h1 : 1 ≤ oddRunCount p :=
      Nat.pos_of_ne_zero fun h0 => hnp ((oddRunCount_eq_zero_iff p).mp h0)
    exact not_reproduces_of_count_mono (finRule f hq) oddRunCount hm
      (fun p s k G hG => hc p s k G hG) h1 hr
  · rintro ⟨hp, x, c, rfl⟩
    have hx : x ≠ 0 := by
      rintro rfl
      exact hp (by rw [dbl_zero_state, translate_zero_state])
    exact Reproduces.translate f hq (LocalRule.DoubledAgree.reproduces_dbl f hq hA hx) c

/-! ## Fixed instances and the guard of the gap -/

/-- The exclusion has a fixed instance meeting its three hypotheses: the zero rule, the number of
set cells, and a single set cell. -/
theorem not_reproduces_of_count_mono_nonvacuous :
    ∃ (U : FiniteConfiguration → FiniteConfiguration) (Φ : FiniteConfiguration → ℕ)
      (p : FiniteConfiguration), p ≠ 0 ∧ (∀ s, Φ (U s) ≤ Φ s) ∧
      (∀ p s k G, 1 ≤ G → Copies p s k G → k * Φ p ≤ Φ s) ∧ 1 ≤ Φ p ∧ ¬ Reproduces U p := by
  have hmono : ∀ s : FiniteConfiguration,
      (finRule (fun _ _ _ => (0 : ZMod 2)) rfl s).support.card ≤ s.support.card := by
    intro s
    have : finRule (fun _ _ _ => (0 : ZMod 2)) rfl s = 0 := by
      ext i
      rw [finRule_apply]
      rfl
    rw [this]
    simp
  have hcopies : ∀ (p s : FiniteConfiguration) (k G : ℕ), 1 ≤ G → Copies p s k G →
      k * p.support.card ≤ s.support.card := fun p s k G _ h => card_support_copies_le h
  have hp1 : 1 ≤ (Finsupp.single (0 : ℤ) (1 : ZMod 2)).support.card := by
    simp
  refine ⟨finRule (fun _ _ _ => (0 : ZMod 2)) rfl, fun s => s.support.card,
    Finsupp.single (0 : ℤ) (1 : ZMod 2), ?_, hmono, hcopies, hp1,
    not_reproduces_of_count_mono _ _ hmono hcopies hp1⟩
  intro h0
  have := congrArg (fun x => x 0) h0
  simp at this

/-- **The gap is load-bearing in the odd-run bound**: two copies of the single cell at gap `0` are
the pair of adjacent cells, one even run, while the single cell is one odd run. -/
theorem oddRunCountCopies_gap_load_bearing :
    Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2))
        (Finsupp.single 0 1 + Finsupp.single 1 1) 2 0 ∧
      oddRunCount (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) <
        2 * oddRunCount (Finsupp.single (0 : ℤ) (1 : ZMod 2)) := by
  refine ⟨⟨fun j => (j : ℤ), fun j hj => ?_, ?_⟩, ?_⟩
  · rw [diam_single_zero_one]
    push_cast
    omega
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, translate_single]
    simp
  · have e1 : oddRunCount (unitCell + Finsupp.single 1 1) = 0 := by
      rw [oddRunCount_of_boundary (S := {-1, 1}) fun i => by
        simp only [unitCell, Finsupp.add_apply, Finsupp.single_apply]; cells_iff]
      decide
    have e2 : oddRunCount unitCell = 1 := by
      rw [oddRunCount_of_boundary (S := {-1, 0}) fun i => by
        simp only [unitCell, Finsupp.single_apply]; cells_iff]
      decide
    simp only [unitCell] at e1 e2
    rw [e1, e2]
    omega

/-! ## The copies bounds -/

private theorem copies_ord {p : FiniteConfiguration} {c : ℕ → ℤ} {k G : ℕ}
    (hc : ∀ j, j + 1 < k → c j + diam p + G ≤ c (j + 1)) {j l : ℕ} (hjl : j < l) (hlk : l < k) :
    c j + diam p + G ≤ c l := by
  obtain ⟨n, rfl⟩ : ∃ n, l = j + (n + 1) := ⟨l - j - 1, by omega⟩
  have h := offsets_mono (d := diam p + G) (G := 0) (k := k) (c := c)
    (fun j hj => by push_cast; have := hc j hj; linarith) (n + 1) j hlk
  push_cast at h
  have h1 : (0 : ℤ) ≤ n * ((diam p : ℤ) + G) := by positivity
  have h2 : ((n : ℤ) + 1) * ((diam p : ℤ) + G) = n * ((diam p : ℤ) + G) + ((diam p : ℤ) + G) := by
    ring
  linarith

/-- On the cells within `g ≤ G` of the hull of copy `j`, a sum of copies at gap `G` reads copy `j`
alone. -/
private theorem copies_apply {p : FiniteConfiguration} {c : ℕ → ℤ} {k G : ℕ}
    (hpne : p.support.Nonempty)
    (hc : ∀ j, j + 1 < k → c j + diam p + G ≤ c (j + 1)) {g : ℕ} (hg : g ≤ G) {j : ℕ}
    (hj : j < k) {x : ℤ} (h1 : p.support.min' hpne - g ≤ x) (h2 : x ≤ p.support.max' hpne + g) :
    ((Finset.range k).sum fun j => translate (c j) p) (x + c j) = p x := by
  have hd : (diam p : ℤ) = p.support.max' hpne - p.support.min' hpne + 1 := by
    have hmM := Finset.min'_le_max' p.support hpne
    unfold diam
    rw [dite_eq_left hpne]
    omega
  have hout : ∀ y : ℤ, (y < p.support.min' hpne ∨ p.support.max' hpne < y) → p y = 0 := by
    intro y hy
    by_contra hne
    have hm := Finsupp.mem_support_iff.mpr hne
    have := Finset.min'_le _ _ hm
    have := Finset.le_max' _ _ hm
    omega
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · rw [translate_apply']
    simp
  · intro l hl hlj
    rw [translate_apply']
    have hl' := Finset.mem_range.mp hl
    apply hout
    rcases lt_or_gt_of_ne hlj with hlt | hgt
    · have := copies_ord hc hlt hj
      omega
    · have := copies_ord hc hgt hl'
      omega
  · intro hn
    exact absurd (Finset.mem_range.mpr hj) hn

/-- **The engine of both copies bounds**: if a state `r` reads a state `q` on the hulls `[a, b]`
of `k` translates of `q`, which are pairwise disjoint and ordered, then `r` has at least `k`
times the kinks of `q`. -/
private theorem kinkCount_mul_le {q r : FiniteConfiguration} {c : ℕ → ℤ} {k : ℕ} {a b : ℤ}
    (hsupp : ∀ i, q i ≠ 0 → a ≤ i ∧ i ≤ b)
    (hagree : ∀ j < k, ∀ i, a ≤ i → i ≤ b → r (i + c j) = q i)
    (hord : ∀ j l, j < l → l < k → c j + b < c l + a) :
    k * kinkCount q ≤ kinkCount r := by
  unfold kinkCount
  rw [← Finset.card_range k, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun x => x.2 + c x.1) (fun x hx => ?_)
    (fun x hx y hy he => ?_)
  · obtain ⟨hj, hi⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
    have hj' := Finset.mem_range.mp hj
    obtain ⟨hiS, j', hj'S, hlt, hodd, hmin⟩ := Finset.mem_filter.mp hi
    have hb1 := hsupp _ (Finsupp.mem_support_iff.mp hiS)
    have hb2 := hsupp _ (Finsupp.mem_support_iff.mp hj'S)
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, j' + c x.1, ?_, by simp only; omega, ?_, ?_⟩
    · rw [Finsupp.mem_support_iff, hagree _ hj' _ hb1.1 hb1.2]
      exact Finsupp.mem_support_iff.mp hiS
    · rw [Finsupp.mem_support_iff, hagree _ hj' _ hb2.1 hb2.2]
      exact Finsupp.mem_support_iff.mp hj'S
    · have : j' + c x.1 - (x.2 + c x.1) = j' - x.2 := by ring
      simpa only [this] using hodd
    · intro m hm
      by_cases hle : m ≤ x.2 + c x.1
      · exact Or.inl hle
      by_cases hge : j' + c x.1 ≤ m
      · exact Or.inr hge
      exfalso
      have hm' : r m ≠ 0 := Finsupp.mem_support_iff.mp hm
      have e := hagree _ hj' (m - c x.1) (by omega) (by omega)
      rw [show m - c x.1 + c x.1 = m by ring] at e
      have hq : q (m - c x.1) ≠ 0 := by rw [← e]; exact hm'
      rcases hmin _ (Finsupp.mem_support_iff.mpr hq) with h | h <;> omega
  · obtain ⟨hj, hi⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
    obtain ⟨hj2, hi2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hy)
    have hj' := Finset.mem_range.mp hj
    have hj2' := Finset.mem_range.mp hj2
    have hb1 := hsupp _ (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hi).1)
    have hb2 := hsupp _ (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hi2).1)
    simp only at he
    have hq1 : x.1 = y.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hord _ _ hlt hj2'
        omega
      · have := hord _ _ hgt hj'
        omega
    have : x.2 = y.2 := by rw [hq1] at he; omega
    exact Prod.ext hq1 this

/-- **`k` copies of a pattern carry at least `k` times its kinks**, at every gap. -/
theorem kinkCountCopies : KinkCountCopies := by
  intro p s k G h
  obtain ⟨c, hc, rfl⟩ := h
  by_cases hp : p = 0
  · subst hp
    have : kinkCount (0 : FiniteConfiguration) = 0 := by
      unfold kinkCount; simp
    simp [this]
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  refine kinkCount_mul_le (a := p.support.min' hpne) (b := p.support.max' hpne)
    (fun i hi => ⟨Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hi),
      Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hi)⟩)
    (fun j hj i h1 h2 => copies_apply hpne hc (g := 0) (Nat.zero_le _) hj (by simpa using h1)
      (by simpa using h2)) (fun j l hjl hlk => ?_)
  have h1 := copies_ord hc hjl hlk
  have hmM := Finset.min'_le_max' p.support hpne
  unfold diam at h1
  rw [dite_eq_left hpne] at h1
  omega

/-- **`k` copies of a pattern at a positive gap carry at least `k` times its odd runs**. -/
theorem oddRunCountCopies : OddRunCountCopies := by
  intro p s k G hG h
  obtain ⟨c, hc, rfl⟩ := h
  by_cases hp : p = 0
  · subst hp
    have : oddRunCount (0 : FiniteConfiguration) = 0 := by
      unfold oddRunCount kinkCount; simp [boundary_apply]
    simp [this]
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hout : ∀ y : ℤ, (y < p.support.min' hpne ∨ p.support.max' hpne < y) → p y = 0 := by
    intro y hy
    by_contra hne
    have hm := Finsupp.mem_support_iff.mpr hne
    have := Finset.min'_le _ _ hm
    have := Finset.le_max' _ _ hm
    omega
  unfold oddRunCount
  refine kinkCount_mul_le (c := c) (a := p.support.min' hpne - 1) (b := p.support.max' hpne)
    (fun i hi => ?_) (fun j hj i h1 h2 => ?_) (fun j l hjl hlk => ?_)
  · rw [boundary_apply] at hi
    by_contra hbad
    have e1 : p i = 0 := hout i (by omega)
    have e2 : p (i + 1) = 0 := hout (i + 1) (by omega)
    exact hi (by rw [e1, e2, add_zero])
  · rw [boundary_apply, boundary_apply]
    have e1 := copies_apply hpne hc (g := 1) hG hj (x := i) (by omega) (by omega)
    have e2 := copies_apply hpne hc (g := 1) hG hj (x := i + 1) (by omega) (by omega)
    rw [show i + 1 + c j = i + c j + 1 by ring] at e2
    rw [e1, e2]
  · have h1 := copies_ord hc hjl hlk
    have hmM := Finset.min'_le_max' p.support hpne
    unfold diam at h1
    rw [dite_eq_left hpne] at h1
    omega

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.kinkCount_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.kinkCount_eq_zero_iff

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.oddRunCount_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.oddRunCount_eq_zero_iff

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_of_count_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_count_mono

set_option linter.style.longLine false in
/-- info: 'ECA.card_support_copies_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_support_copies_le

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_of_count_mono_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_count_mono_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.reproduces_iff_oneParity

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.DoubledAgree.reproduces_iff_dbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.DoubledAgree.reproduces_iff_dbl

set_option linter.style.longLine false in
/-- info: 'ECA.oddRunCountCopies_gap_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.oddRunCountCopies_gap_load_bearing

set_option linter.style.longLine false in
/-- info: 'ECA.kinkCountCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.kinkCountCopies

set_option linter.style.longLine false in
/-- info: 'ECA.oddRunCountCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.oddRunCountCopies

end ECA
