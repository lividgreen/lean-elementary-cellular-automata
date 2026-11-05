module

public import ECA.ReproductionBracket
import all ECA.ReproductionBracket
import all ECA.Growth
import all ECA.EndpointClasses

/-!
# The reproduced patterns, at every pattern of each class
([RuleSpace] §5)

The identities under which the fifteen reproducing rules other than `106` and `120` reproduce a
pattern hold at every state of the class they are stated for, and the pattern enters each proof only
through its being nonzero. So the single-pattern theorems of `ECA.ReproductionBracket`
([RuleSpace] §5 Proposition 5.9) hold at every pattern of their class.

## Main results

* `LocalRule.LinearTaps.reproduces_of_ne_zero` — a linear rule (rules `60`, `90`, `102` and `150`)
  reproduces every nonzero pattern, by the Frobenius identity in characteristic two
  (`LocalRuleColumns.iterate_two_pow_step_linear`).
* `LocalRule.AgreesOffAdjacent.reproduces_of_oneParity` — a rule agreeing with rule `90` off
  adjacent cells (rules `18`, `26`, `82`, `146`, `154`, `210`, `218` among them) reproduces every
  nonzero pattern whose set cells differ by even amounts.
* `LocalRule.DoubledAgree.reproduces_dbl` — a rule agreeing with rule `90` at equal adjacent
  cells (rules `94`, `122` and `126`) reproduces every doubled nonzero pattern.
* `reproduces_f22_of_supportInCoset` — rule `22` reproduces every nonzero pattern supported in one
  coset of `4ℤ`.
* `finRule_copies` — a quiescent rule on `k` copies of a pattern at gap at least two is `k` copies
  of the image at gap two less, with a guard at rule `18` that the gap condition is load-bearing.
* `Reproduces.step`, `Reproduces.iterate` and `Reproduces.translate` — the set of patterns a
  quiescent rule reproduces is closed under the rule, so under its iterates, and under translation.
* `reproduces_f22_iterate_of_supportInCoset` — rule `22` reproduces every state on the orbit of a
  nonzero pattern supported in one coset of `4ℤ`.
* Each statement has a `_nonvacuous` witness at a fixed rule and a fixed pattern.

A pattern outside the class of a statement is not addressed here.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The linear rules -/

/-- **A linear rule reproduces every nonzero pattern**: at `t = 2 ^ M₁ + … + 2 ^ Mᵣ` with the
exponents well spaced, the iterate is `|T| ^ r` copies of the pattern, `T` the set of taps
([RuleSpace] §5). -/
theorem LocalRule.LinearTaps.reproduces_of_ne_zero (f : LocalRule) (hq : f 0 0 0 = 0)
    (h : LinearTaps f) {p : FiniteConfiguration} (hp : p ≠ 0) :
    Reproduces (finRule f hq) p := by
  obtain ⟨α, β, γ, hT, hf⟩ := h
  have Φ := iterate_two_pow_linear (hq := hq) hf
  have hid : ∀ M t (i : ℤ), ((finRule f hq)^[2 ^ M + t] p) i
      = α * ((finRule f hq)^[t] p) (i - 2 ^ M) +
        β * ((finRule f hq)^[t] p) i +
        γ * ((finRule f hq)^[t] p) (i + 2 ^ M) := by
    intro M t i
    rw [Function.iterate_add_apply, Φ]
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases α with rfl | rfl <;> rcases hcases β with rfl | rfl <;>
    rcases hcases γ with rfl | rfl
  · exact absurd hT (by decide)
  · exact absurd hT (by decide)
  · exact absurd hT (by decide)
  · refine reproduces_of_doubling_identity hp (q := 2) (b := 1) (-1) le_rfl le_rfl
      fun M t i => ?_
    rw [hid]
    simp [Finset.sum_range_succ]
    abel_nf
  · exact absurd hT (by decide)
  · refine reproduces_of_doubling_identity hp (q := 2) (b := 2) (-1) le_rfl (by omega)
      fun M t i => ?_
    rw [hid]
    simp [Finset.sum_range_succ]
    ring_nf
  · refine reproduces_of_doubling_identity hp (q := 2) (b := 1) 0 le_rfl le_rfl
      fun M t i => ?_
    rw [hid]
    simp [Finset.sum_range_succ]
    abel_nf
  · refine reproduces_of_doubling_identity hp (q := 3) (b := 1) (-1) (by omega) le_rfl
      fun M t i => ?_
    rw [hid]
    simp [Finset.sum_range_succ]
    ring_nf

/-! ## The rules agreeing with rule `90` off adjacent cells -/

/-- **A rule agreeing with rule `90` off adjacent cells reproduces every nonzero one-parity
pattern**: the doubling identity of rule `90` holds over the one-parity states
([RuleSpace] §4 Proposition 4.2(iv)). -/
theorem LocalRule.AgreesOffAdjacent.reproduces_of_oneParity (f : LocalRule)
    (h : AgreesOffAdjacent f) {p : FiniteConfiguration} (hs : OneParity p) (hp : p ≠ 0) :
    Reproduces (finRule f h.1) p := by
  refine reproduces_of_doubling_identity hp (q := 2) (b := 2) (-1) le_rfl (by omega)
    fun M t i => ?_
  have := FiniteConfiguration.OneParity.iterate_two_pow_add f h _ hs M t i
  refine this.trans ?_
  simp [Finset.sum_range_succ]
  ring_nf

/-! ## The rules agreeing with rule `90` at equal adjacent cells -/

private theorem FiniteConfiguration.diam_dbl_le (p : FiniteConfiguration) :
    diam (dbl p) ≤ 2 * diam p := by
  by_cases hne : p.support.Nonempty
  · have hne' : (dbl p).support.Nonempty := by
      obtain ⟨a, ha⟩ := hne
      refine ⟨2 * a, Finsupp.mem_support_iff.mpr ?_⟩
      rw [dbl_apply]
      have : 2 * a / 2 = a := by omega
      rw [this]
      exact Finsupp.mem_support_iff.mp ha
    have h1 : (dbl p).support.max' hne' ≤ 2 * p.support.max' hne + 1 := by
      apply Finset.max'_le
      intro y hy
      have hy' := Finsupp.mem_support_iff.mp hy
      rw [dbl_apply] at hy'
      have := Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hy')
      omega
    have h2 : 2 * p.support.min' hne ≤ (dbl p).support.min' hne' := by
      apply Finset.le_min'
      intro y hy
      have hy' := Finsupp.mem_support_iff.mp hy
      rw [dbl_apply] at hy'
      have := Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hy')
      omega
    simp only [diam, hne, hne', ↓reduceDIte]
    omega
  · have hp0 : p = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact Finsupp.support_eq_empty.mp hne
    have hd : dbl p = 0 := by
      ext j
      rw [dbl_apply, hp0]
      simp
    rw [hd, hp0]
    simp [diam]

private theorem copies_dbl {p s : FiniteConfiguration} {k G : ℕ} (h : Copies p s k G) :
    Copies (dbl p) (dbl s) k G := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun j => 2 * c j, fun j hj => ?_, ?_⟩
  · have := hc j hj
    have h2 := FiniteConfiguration.diam_dbl_le p
    change 2 * c j + diam (dbl p) + G ≤ 2 * c (j + 1)
    omega
  · rw [FiniteConfiguration.dbl_sum']
    exact Finset.sum_congr rfl fun j _ => FiniteConfiguration.dbl_translate' _ _

private theorem dbl_ne_zero {x : FiniteConfiguration} (hx : x ≠ 0) : dbl x ≠ 0 := by
  intro h0
  apply hx
  ext j
  have := congrArg (fun y => y (2 * j)) h0
  simp only [dbl_apply] at this
  have e : 2 * j / 2 = j := by omega
  rw [e] at this
  simpa using this

/-- **A rule agreeing with rule `90` at equal adjacent cells reproduces every doubled nonzero
pattern**: two steps on a doubled state are one step of rule `90` on the half-size state
([RuleSpace] §5), so the copies of the half-size pattern that rule `90` reaches double to copies
of the doubled pattern. -/
theorem LocalRule.DoubledAgree.reproduces_dbl (f : LocalRule) (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) {x : FiniteConfiguration} (hx : x ≠ 0) :
    Reproduces (finRule f hq) (dbl x) := by
  have h90 := LocalRule.LinearTaps.reproduces_of_ne_zero f90 hq90 (by decide) hx
  refine ⟨dbl_ne_zero hx, fun N G => ?_⟩
  obtain ⟨t, k, hk, hcop⟩ := h90.2 N G
  refine ⟨2 * t, k, hk, ?_⟩
  rw [iterate_two_mul_dbl f hq hA]
  exact copies_dbl hcop

/-! ## Rule `22` on a coset of `4ℤ` -/

/-- **Rule `22` reproduces every nonzero pattern supported in one coset of `4ℤ`**: its second
iterate satisfies the doubling identity at offsets `∓ 2 ^ (M + 1)`, being rule `90`'s second
iterate on this coset ([RuleSpace] §5 Proposition 5.9). -/
theorem reproduces_f22_of_supportInCoset {p : FiniteConfiguration}
    (hs : Rule22Sparse.SupportInCoset 4 ⇑p) (hp : p ≠ 0) :
    Reproduces (finRule f22 hq22) p := by
  apply Reproduces.of_iterate_two
  refine reproduces_of_doubling_identity hp (q := 2) (b := 4) (-2) le_rfl (by omega)
    fun M t i => ?_
  rw [← Function.iterate_mul, ← Function.iterate_mul,
    finRule_f22_iterate_two_mul_eq_f90 _ hs, finRule_f22_iterate_two_mul_eq_f90 _ hs,
    show 2 * (2 ^ M + t) = 2 ^ (M + 1) + 2 * t by ring, f90_iterate_two_pow_add]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_succ]
  push_cast
  rw [add_comm]
  congr 2
  ring

/-! ## Witnesses -/

/-- The linear statement has a fixed instance: rule `60` and the pattern of cells `0`, `1`
and `3`. -/
theorem LocalRule.LinearTaps.reproduces_of_ne_zero_nonvacuous :
    ∃ (f : LocalRule) (hq : f 0 0 0 = 0), LinearTaps f ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) +
          Finsupp.single 3 (1 : ZMod 2)) ≠ 0 ∧
      Reproduces (finRule f hq)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) +
          Finsupp.single 3 (1 : ZMod 2)) := by
  have hp : (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) +
      Finsupp.single 3 (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun x => x 0) h0
    simp at this
  exact ⟨f60, hq60, by decide, hp, LocalRule.LinearTaps.reproduces_of_ne_zero f60 hq60
    (by decide) hp⟩

/-- The one-parity statement has a fixed instance: rule `18` and the two cells at `0` and `4`. -/
theorem LocalRule.AgreesOffAdjacent.reproduces_of_oneParity_nonvacuous :
    ∃ (f : LocalRule) (h : AgreesOffAdjacent f),
      OneParity (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) ≠ 0 ∧
      Reproduces (finRule f h.1)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) := by
  have hs : OneParity
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) := by
    intro i j hi hj
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
    rw [even_iff_two_dvd]
    split_ifs at hi hj <;> first | omega | simp_all
  have hp : (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun x => x 0) h0
    simp at this
  exact ⟨f18, agreesOffAdjacent_f18, hs, hp,
    LocalRule.AgreesOffAdjacent.reproduces_of_oneParity f18 agreesOffAdjacent_f18 hs hp⟩

/-- The doubled statement has a fixed instance: rule `94` and the doubled pair of cells `0`
and `2`. -/
theorem LocalRule.DoubledAgree.reproduces_dbl_nonvacuous :
    ∃ (f : LocalRule) (hq : f 0 0 0 = 0), DoubledAgree f ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) ≠ 0 ∧
      Reproduces (finRule f hq)
        (dbl (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2))) := by
  have hx : (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun x => x 0) h0
    simp at this
  exact ⟨f94, by decide, by decide, hx,
    LocalRule.DoubledAgree.reproduces_dbl f94 (by decide) (by decide) hx⟩

/-- The coset statement has a fixed instance: rule `22` and the two cells at `0` and `4`. -/
theorem reproduces_f22_of_supportInCoset_nonvacuous :
    Rule22Sparse.SupportInCoset 4
        ⇑(Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2) :
          FiniteConfiguration) ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) ≠ 0 ∧
      Reproduces (finRule f22 hq22)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) := by
  have hs : Rule22Sparse.SupportInCoset 4
      ⇑(Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2) :
          FiniteConfiguration) := by
    intro i j hi hj
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at hi hj
    split_ifs at hi hj <;> first | omega | simp_all
  have hp : (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun x => x 0) h0
    simp at this
  exact ⟨hs, hp, reproduces_f22_of_supportInCoset hs hp⟩

/-! ## The image and the orbit of a reproduced pattern -/

/-- The image of a state has diameter at most two more than the state's: its support lies within one
cell of the state's. -/
private theorem diam_finRule_le_add_two (f : LocalRule) (hq : f 0 0 0 = 0)
    (p : FiniteConfiguration) : diam (finRule f hq p) ≤ diam p + 2 := by
  by_cases hp : p.support.Nonempty
  · have hle := Finset.min'_le_max' p.support hp
    have key := diam_le_of_support_subset (t' := finRule f hq p)
      (m := p.support.min' hp - 1) (M := p.support.max' hp + 1) ?_ (by omega)
    · rw [diam_eq' hp]
      omega
    · intro x hx
      have hx' := Finsupp.mem_support_iff.mp hx
      rw [finRule_apply] at hx'
      have hcell : ∀ y, p y ≠ 0 → p.support.min' hp ≤ y ∧ y ≤ p.support.max' hp := fun y hy =>
        ⟨Finset.min'_le _ y (Finsupp.mem_support_iff.mpr hy),
          Finset.le_max' _ y (Finsupp.mem_support_iff.mpr hy)⟩
      by_cases h1 : p (x - 1) = 0
      · by_cases h2 : p x = 0
        · by_cases h3 : p (x + 1) = 0
          · exact absurd (by rw [h1, h2, h3]; exact hq) hx'
          · have := hcell _ h3
            omega
        · have := hcell _ h2
          omega
      · have := hcell _ h1
        omega
  · have hz : p = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hp)
    subst hz
    rw [finRule_zero']
    omega

/-- Every nonzero pattern has diameter at least one. -/
private theorem one_le_diam_of_ne_zero {p : FiniteConfiguration} (hp : p ≠ 0) : 1 ≤ diam p := by
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hp
  have := le_diam_of_cells (a := a) (b := a) (by simpa using ha) (by simpa using ha)
  omega

/-- Two cells of distinct copies at gap at least two are more than two apart. -/
private theorem copies_cells_apart {p : FiniteConfiguration} {k G : ℕ} {c : ℕ → ℤ}
    (hG : 2 ≤ G) (hc : ∀ j, j + 1 < k → c j + diam p + G ≤ c (j + 1)) {j j' : ℕ}
    (hjj' : j < j') (hj' : j' < k) {a b : ℤ} (ha : p a ≠ 0) (hb : p b ≠ 0) :
    a + c j + 2 < b + c j' := by
  obtain ⟨n, rfl⟩ : ∃ n, j' = j + (n + 1) := ⟨j' - j - 1, by omega⟩
  have hc' : ∀ j, j + 1 < k → c j + ((diam p + G : ℕ) : ℤ) + (0 : ℕ) ≤ c (j + 1) := fun j hj => by
    have := hc j hj
    push_cast
    omega
  have h1 := offsets_mono hc' (n + 1) j (by omega)
  have h2 := le_diam_of_cells hb ha
  have h3 : ((diam p + G : ℕ) : ℤ) ≤ ((n + 1 : ℕ) : ℤ) * ((diam p + G : ℕ) : ℤ) := by
    have hn : (1 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by push_cast; omega
    nlinarith [Int.natCast_nonneg (diam p + G)]
  push_cast at h1 h3
  omega

/-- The step on a sum of well-separated translates is the sum of the steps. -/
private theorem finRule_sum_translate (f : LocalRule) (hq : f 0 0 0 = 0) {p : FiniteConfiguration}
    {k G : ℕ} {c : ℕ → ℤ} (hG : 2 ≤ G) (hc : ∀ j, j + 1 < k → c j + diam p + G ≤ c (j + 1)) :
    finRule f hq ((Finset.range k).sum fun j => translate (c j) p) =
      (Finset.range k).sum fun j => translate (c j) (finRule f hq p) := by
  by_cases hp : p = 0
  · subst hp
    have h0 : ∀ i : ℤ, translate i (0 : FiniteConfiguration) = 0 := fun i =>
      (translate_ne_zero_iff i).mpr rfl
    simp [h0, finRule_zero']
  have hsep : ∀ (i : ℤ) j j', j < j' → j' < k →
      ¬ ((p (i - c j - 1) ≠ 0 ∨ p (i - c j) ≠ 0 ∨ p (i - c j + 1) ≠ 0) ∧
        (p (i - c j' - 1) ≠ 0 ∨ p (i - c j') ≠ 0 ∨ p (i - c j' + 1) ≠ 0)) := by
    intro i j j' hjj' hj' ⟨h1, h2⟩
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
      first
      | have := copies_cells_apart hG hc hjj' hj' h1 h2; omega
  ext i
  rw [finRule_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.finsetSum_apply, translate_apply', finRule_apply]
  by_cases hex : ∃ j0 ∈ Finset.range k,
      (p (i - c j0 - 1) ≠ 0 ∨ p (i - c j0) ≠ 0 ∨ p (i - c j0 + 1) ≠ 0)
  · obtain ⟨j0, hj0, hW⟩ := hex
    have hoth : ∀ j ∈ Finset.range k, j ≠ j0 →
        p (i - c j - 1) = 0 ∧ p (i - c j) = 0 ∧ p (i - c j + 1) = 0 := by
      intro j hj hne
      by_contra hcon
      have hW' : (p (i - c j - 1) ≠ 0 ∨ p (i - c j) ≠ 0 ∨ p (i - c j + 1) ≠ 0) := by
        by_contra hn
        push Not at hn
        exact hcon hn
      have hjk := Finset.mem_range.mp hj
      have hj0k := Finset.mem_range.mp hj0
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hsep i j j0 hlt hj0k ⟨hW', hW⟩
      · exact hsep i j0 j hgt hjk ⟨hW, hW'⟩
    have hs : ∀ x : ℤ, (∀ j ∈ Finset.range k, j ≠ j0 → p (x - c j) = 0) →
        ∑ j ∈ Finset.range k, p (x - c j) = p (x - c j0) := fun x hx =>
      Finset.sum_eq_single j0 hx fun h => absurd hj0 h
    rw [hs (i - 1) fun j hj hne => by rw [sub_right_comm]; exact (hoth j hj hne).1,
      hs i fun j hj hne => (hoth j hj hne).2.1,
      hs (i + 1) fun j hj hne => by rw [add_sub_right_comm]; exact (hoth j hj hne).2.2]
    rw [Finset.sum_eq_single j0]
    · rw [sub_right_comm, add_sub_right_comm]
    · intro j hj hne
      obtain ⟨h1, h2, h3⟩ := hoth j hj hne
      rw [h1, h2, h3]
      exact hq
    · exact fun h => absurd hj0 h
  · push Not at hex
    have hz : ∀ j ∈ Finset.range k, p (i - c j - 1) = 0 ∧ p (i - c j) = 0 ∧
        p (i - c j + 1) = 0 := fun j hj => hex j hj
    have e1 : ∑ j ∈ Finset.range k, p (i - 1 - c j) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [sub_right_comm]; exact (hz j hj).1
    have e2 : ∑ j ∈ Finset.range k, p (i - c j) = 0 :=
      Finset.sum_eq_zero fun j hj => (hz j hj).2.1
    have e3 : ∑ j ∈ Finset.range k, p (i + 1 - c j) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [add_sub_right_comm]; exact (hz j hj).2.2
    rw [e1, e2, e3, hq]
    exact (Finset.sum_eq_zero fun j hj => by
      obtain ⟨h1, h2, h3⟩ := hz j hj
      rw [h1, h2, h3]
      exact hq).symm

/-- **A quiescent rule on `k` copies of `p` at gap at least two is `k` copies of the image of `p`
at the same offsets, at gap two less**: each three-cell window meets at most one copy, so the rule
reads each copy alone and the zero cells between them
([RuleSpace] §5 Proposition 5.9). -/
theorem finRule_copies (f : LocalRule) (hq : f 0 0 0 = 0) {p s : FiniteConfiguration}
    {k G : ℕ} (hG : 2 ≤ G) (h : Copies p s k G) :
    Copies (finRule f hq p) (finRule f hq s) k (G - 2) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c, fun j hj => ?_, finRule_sum_translate f hq hG hc⟩
  have h1 := hc j hj
  have h2 := diam_finRule_le_add_two f hq p
  omega

/-- **A reproduced pattern has a nonzero image**: at least two copies of a nonzero pattern have
diameter at least twice the pattern's, which neither the pattern nor the zero state has
([RuleSpace] §5 Proposition 5.9). -/
theorem Reproduces.finRule_ne_zero (f : LocalRule) (hq : f 0 0 0 = 0) {p : FiniteConfiguration}
    (h : Reproduces (finRule f hq) p) : finRule f hq p ≠ 0 := by
  intro h0
  obtain ⟨hp, h2⟩ := h
  obtain ⟨t, k, hk, hcop⟩ := h2 2 0
  have hd := copies_diam_le hp hcop (by omega)
  have h1 := one_le_diam_of_ne_zero hp
  have hS : diam ((finRule f hq)^[t] p) ≤ diam p := by
    rcases t with _ | n
    · exact le_rfl
    · rw [Function.iterate_succ_apply, h0, Function.iterate_fixed (finRule_zero' f hq)]
      simp [diam_zero']
  nlinarith

/-- **A rule reproducing a pattern reproduces its image**: copies of `p` at gap `G + 2` step to
copies of the image at gap `G` ([RuleSpace] §5 Proposition 5.9). -/
theorem Reproduces.step (f : LocalRule) (hq : f 0 0 0 = 0) {p : FiniteConfiguration}
    (h : Reproduces (finRule f hq) p) : Reproduces (finRule f hq) (finRule f hq p) := by
  refine ⟨Reproduces.finRule_ne_zero f hq h, fun N G => ?_⟩
  obtain ⟨t, k, hk, hcop⟩ := h.2 N (G + 2)
  refine ⟨t, k, hk, ?_⟩
  have h1 := finRule_copies f hq (by omega) hcop
  rw [Nat.add_sub_cancel] at h1
  rwa [← Function.iterate_succ_apply (finRule f hq) t p, Function.iterate_succ_apply']

/-- **A rule reproducing a pattern reproduces every state on its orbit**
([RuleSpace] §5 Proposition 5.9). -/
theorem Reproduces.iterate (f : LocalRule) (hq : f 0 0 0 = 0) {p : FiniteConfiguration}
    (h : Reproduces (finRule f hq) p) (n : ℕ) :
    Reproduces (finRule f hq) ((finRule f hq)^[n] p) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact Reproduces.step f hq ih

/-- Copies of a translate are translates of copies. -/
private theorem copies_translate {p s : FiniteConfiguration} {k G : ℕ} (c : ℤ)
    (h : Copies p s k G) : Copies (translate c p) (translate c s) k G := by
  obtain ⟨d, hd, rfl⟩ := h
  refine ⟨d, fun j hj => ?_, ?_⟩
  · have h1 := hd j hj
    rw [diam_translate]
    exact h1
  · rw [translate_sum']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [translate_translate', translate_translate', add_comm]

/-- **Reproduction is invariant under translation**: the rule commutes with translation and copies
of a translate are translates of copies ([RuleSpace] §5 Proposition 5.9). -/
theorem Reproduces.translate (f : LocalRule) (hq : f 0 0 0 = 0) {p : FiniteConfiguration}
    (h : Reproduces (finRule f hq) p) (c : ℤ) :
    Reproduces (finRule f hq) (FiniteConfiguration.translate c p) := by
  refine ⟨fun h0 => h.1 ((translate_ne_zero_iff c).mp h0), fun N G => ?_⟩
  obtain ⟨t, k, hk, hcop⟩ := h.2 N G
  refine ⟨t, k, hk, ?_⟩
  rw [iterate_translate' (finRule_translate f hq) c p t]
  exact copies_translate c hcop

/-- **Reproduction pulls back along an injective step**: at a quiescent rule whose step is
injective, a state whose image is reproduced is itself reproduced. Copies of the image at gap
`G + diam q + 2` are copies of `q` at the same offsets, at gap `G + 2`, stepped by the rule, so
injectivity strips the step; no width comparison between `q` and its image is needed
([RuleSpace] §5). -/
theorem Reproduces.of_finRule (f : LocalRule) (hq : f 0 0 0 = 0)
    (hinj : Function.Injective (finRule f hq)) {q : FiniteConfiguration}
    (h : Reproduces (finRule f hq) (finRule f hq q)) : Reproduces (finRule f hq) q := by
  refine ⟨fun h0 => h.1 (by rw [h0]; exact finRule_zero' f hq), fun N G => ?_⟩
  obtain ⟨t, k, hk, c, hc, hs⟩ := h.2 N (G + diam q + 2)
  refine ⟨t, k, hk, c, fun j hj => ?_, ?_⟩
  · have := hc j hj
    omega
  · apply hinj
    rw [← Function.iterate_succ_apply' (finRule f hq) t q, Function.iterate_succ_apply, hs,
      finRule_sum_translate f hq (p := q) (G := G + 2) (by omega)
        (fun j hj => by have := hc j hj; omega)]

/-- **Reproduction of a state is reproduction of any iterate of it, at an injective rule**
([RuleSpace] §5). -/
theorem Reproduces.iterate_iff (f : LocalRule) (hq : f 0 0 0 = 0)
    (hinj : Function.Injective (finRule f hq)) {q : FiniteConfiguration} (n : ℕ) :
    Reproduces (finRule f hq) ((finRule f hq)^[n] q) ↔ Reproduces (finRule f hq) q := by
  refine ⟨fun h => ?_, fun h => Reproduces.iterate f hq h n⟩
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    exact ih (Reproduces.of_finRule f hq hinj h)

/-- **A state periodic up to translation is never reproduced**: if `m` steps of the rule at `p`
are a translate of `p`, with `0 < m`, then the diameters along the orbit of `p` are at most the
largest of the first `m`, because the rule commutes with translation and a translate has the same
diameter; while `N` copies of a nonzero pattern have diameter at least `N` times its own
([RuleSpace] §5). -/
theorem Reproduces.not_of_iterate_eq_translate (f : LocalRule) (hq : f 0 0 0 = 0)
    {p : FiniteConfiguration} {m : ℕ} {c : ℤ} (hm : 0 < m)
    (hp : (finRule f hq)^[m] p = FiniteConfiguration.translate c p) :
    ¬ Reproduces (finRule f hq) p := by
  intro h
  have hperiod : ∀ a : ℕ, ∃ d : ℤ,
      (finRule f hq)^[m * a] p = FiniteConfiguration.translate d p := by
    intro a
    induction a with
    | zero =>
      exact ⟨0, by
        rw [Nat.mul_zero, Function.iterate_zero, id, FiniteConfiguration.translate_zero]⟩
    | succ a ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨d + c, ?_⟩
      rw [Nat.mul_succ, Function.iterate_add_apply, hp,
        iterate_translate' (finRule_translate f hq) c p, hd,
        FiniteConfiguration.translate_translate']
  obtain ⟨hp0, hrep⟩ := h
  have hdiam : ∀ t : ℕ, diam ((finRule f hq)^[t] p) ≤
      (Finset.range m).sup fun b => diam ((finRule f hq)^[b] p) := by
    intro t
    obtain ⟨d, hd⟩ := hperiod (t / m)
    have ht : (finRule f hq)^[t] p =
        (finRule f hq)^[t % m] ((finRule f hq)^[m * (t / m)] p) := by
      rw [← Function.iterate_add_apply, Nat.mod_add_div]
    rw [ht, hd, iterate_translate' (finRule_translate f hq) d p, FiniteConfiguration.diam_translate]
    exact Finset.le_sup (f := fun b => diam ((finRule f hq)^[b] p))
      (Finset.mem_range.mpr (Nat.mod_lt t hm))
  obtain ⟨t, k, hk, hcop⟩ :=
    hrep (((Finset.range m).sup fun b => diam ((finRule f hq)^[b] p)) + 1) 0
  have h1 := copies_diam_le hp0 hcop (by omega)
  have h2 := hdiam t
  have h3 := one_le_diam_of_ne_zero hp0
  nlinarith

/-- **Rule `22` reproduces every state on the orbit of a nonzero pattern supported in one coset of
`4ℤ`**: at width up to 8 these orbits hold exactly the four patterns computation finds reproduced,
the two coset patterns `1` and `10001` and their first images `111` and `1110111`
([RuleSpace] §5). -/
theorem reproduces_f22_iterate_of_supportInCoset {p : FiniteConfiguration}
    (hs : Rule22Sparse.SupportInCoset 4 ⇑p) (hp : p ≠ 0) (n : ℕ) :
    Reproduces (finRule f22 hq22) ((finRule f22 hq22)^[n] p) :=
  Reproduces.iterate f22 hq22 (reproduces_f22_of_supportInCoset hs hp) n

/-! ## Witnesses and the guard -/

/-- Translating a single cell moves it. -/
private theorem translate_single (a i : ℤ) :
    translate i (Finsupp.single a (1 : ZMod 2)) = Finsupp.single (a + i) 1 :=
  Finsupp.mapDomain_single

/-- The copies statement has a fixed instance: at rule `60`, the cells `0` and `4` are two copies
of the cell `0` at gap `3`, and their image, the cells `0`, `1`, `4` and `5`, is two copies of the
image of the cell, the cells `0` and `1`, at gap `1`. -/
theorem finRule_copies_nonvacuous :
    Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2))
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) 2 3 ∧
      finRule f60 hq60 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) =
        Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) ∧
      finRule f60 hq60 (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) =
        Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) +
          (Finsupp.single 4 (1 : ZMod 2) + Finsupp.single 5 (1 : ZMod 2)) ∧
      Copies (finRule f60 hq60 (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (finRule f60 hq60 (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)))
        2 1 := by
  have hc : Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) 2 3 := by
    refine ⟨fun j => 4 * (j : ℤ), fun j hj => ?_, ?_⟩
    · rw [diam_single_zero_one]
      push_cast
      omega
    · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, translate_single]
      simp
  have himg : finRule f60 hq60 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) =
      Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) := by
    ext i
    simp only [finRule_apply, f60, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> first | decide | (exfalso; omega)
  have hsum : finRule f60 hq60
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) =
      Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) +
        (Finsupp.single 4 (1 : ZMod 2) + Finsupp.single 5 (1 : ZMod 2)) := by
    ext i
    simp only [finRule_apply, f60, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> first | decide | (exfalso; omega)
  exact ⟨hc, himg, hsum, finRule_copies f60 hq60 (by omega) hc⟩

/-- **The gap condition is load-bearing**: at rule `18`, the cells `0` and `2` are two copies of the
cell `0` at gap `1`, and their image, the cells `-1` and `3`, is not two copies of the image of the
cell, the cells `-1` and `1`, at gap `0`: two such copies have diameter at least `6`, the image has
diameter `5`. -/
theorem finRule_copies_gap_load_bearing :
    Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2))
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) 2 1 ∧
      ¬ Copies (finRule f18 hq18 (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (finRule f18 hq18 (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)))
        2 0 := by
  refine ⟨⟨fun j => 2 * (j : ℤ), fun j hj => ?_, ?_⟩, fun h => ?_⟩
  · rw [diam_single_zero_one]
    push_cast
    omega
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, translate_single]
    simp
  · have hm1 : finRule f18 hq18 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-1) ≠ 0 := by
      rw [finRule_apply]
      simp [f18]
    have hp1 : finRule f18 hq18 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 ≠ 0 := by
      rw [finRule_apply]
      simp [f18]
    have hne : finRule f18 hq18 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ≠ 0 := fun h0 => by
      rw [h0] at hm1
      exact hm1 rfl
    have hd := copies_diam_le hne h (by omega)
    have h3 := le_diam_of_cells hm1 hp1
    have h4 := diam_finRule_le_add_two f18 hq18
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2))
    have h5 : diam (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) ≤ 3 := by
      have := diam_le_of_support_subset
        (t' := Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2))
        (m := 0) (M := 2) (fun x hx => by
          have hx' := Finsupp.mem_support_iff.mp hx
          simp only [Finsupp.add_apply, Finsupp.single_apply] at hx'
          split_ifs at hx' <;> first | omega | (exfalso; exact hx' (by decide))) (by omega)
      simpa using this
    omega

/-- The step statement has a fixed instance: rule `18` reproduces the cells `0` and `4`, and so
their image, the cells `-1`, `1`, `3` and `5`. -/
theorem Reproduces.step_nonvacuous :
    Reproduces (finRule f18 hq18)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) ∧
      finRule f18 hq18 (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) =
        Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) +
          (Finsupp.single 3 (1 : ZMod 2) + Finsupp.single 5 (1 : ZMod 2)) ∧
      Reproduces (finRule f18 hq18)
        (Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) +
          (Finsupp.single 3 (1 : ZMod 2) + Finsupp.single 5 (1 : ZMod 2))) := by
  have hs : OneParity
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) := by
    intro i j hi hj
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
    rw [even_iff_two_dvd]
    split_ifs at hi hj <;> first | omega | simp_all
  have hp : (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun x => x 0) h0
    simp at this
  have h1 := LocalRule.AgreesOffAdjacent.reproduces_of_oneParity f18 agreesOffAdjacent_f18 hs hp
  have himg : finRule f18 hq18
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) =
      Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) +
        (Finsupp.single 3 (1 : ZMod 2) + Finsupp.single 5 (1 : ZMod 2)) := by
    ext i
    simp only [finRule_apply, f18, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> first | decide | (exfalso; omega)
  exact ⟨h1, himg, himg ▸ Reproduces.step f18 hq18 h1⟩

/-- The translation statement has a fixed instance: rule `60` reproduces the cell `0`, hence the
cell `3`. -/
theorem Reproduces.translate_nonvacuous :
    Reproduces (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ∧
      FiniteConfiguration.translate 3 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) =
        Finsupp.single 3 (1 : ZMod 2) ∧
      Reproduces (finRule f60 hq60) (Finsupp.single 3 (1 : ZMod 2)) := by
  have h : Reproduces (finRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) :=
    LocalRule.LinearTaps.reproduces f60 hq60 (by decide)
  refine ⟨h, by rw [translate_single]; simp, ?_⟩
  have := Reproduces.translate f60 hq60 h 3
  rwa [translate_single, zero_add] at this

/-- The orbit statement has a fixed instance: rule `22` on the cells `0` and `4`, after one step,
reproduces the cells `-1` to `1` and `3` to `5`. -/
theorem reproduces_f22_iterate_of_supportInCoset_nonvacuous :
    Rule22Sparse.SupportInCoset 4
        ⇑(Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2) :
          FiniteConfiguration) ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) ≠ 0 ∧
      (finRule f22 hq22)^[1]
          (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2)) =
        Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
          Finsupp.single 1 (1 : ZMod 2) + (Finsupp.single 3 (1 : ZMod 2) +
            Finsupp.single 4 (1 : ZMod 2) + Finsupp.single 5 (1 : ZMod 2)) ∧
      Reproduces (finRule f22 hq22)
        ((finRule f22 hq22)^[1]
          (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 4 (1 : ZMod 2))) := by
  obtain ⟨hs, hp, -⟩ := reproduces_f22_of_supportInCoset_nonvacuous
  refine ⟨hs, hp, ?_, reproduces_f22_iterate_of_supportInCoset hs hp 1⟩
  ext i
  rw [Function.iterate_one, finRule_apply]
  simp only [f22, wolframRule, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> first | decide | (exfalso; omega)

/-- The periodicity statement has a fixed instance: at rule `106` the single cell `0` moves one cell
left in one step, a translate of itself with `m = 1` and `c = -1`, and is not reproduced. -/
theorem Reproduces.not_of_iterate_eq_translate_nonvacuous (hq : wolframRule 106 0 0 0 = 0) :
    0 < 1 ∧
      (finRule (wolframRule 106) hq)^[1] (Finsupp.single (0 : ℤ) (1 : ZMod 2)) =
        FiniteConfiguration.translate (-1) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ∧
      ¬ Reproduces (finRule (wolframRule 106) hq) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) := by
  have himg : (finRule (wolframRule 106) hq)^[1] (Finsupp.single (0 : ℤ) (1 : ZMod 2)) =
      FiniteConfiguration.translate (-1) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) := by
    rw [Function.iterate_one, translate_single]
    ext i
    simp only [finRule_apply, wolframRule, Finsupp.single_apply]
    split_ifs <;> first | decide | (exfalso; omega)
  exact ⟨Nat.one_pos, himg,
    Reproduces.not_of_iterate_eq_translate (wolframRule 106) hq Nat.one_pos himg⟩

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.LinearTaps.reproduces_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.LinearTaps.reproduces_of_ne_zero

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.AgreesOffAdjacent.reproduces_of_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.reproduces_of_oneParity

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.DoubledAgree.reproduces_dbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.DoubledAgree.reproduces_dbl

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_f22_of_supportInCoset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_f22_of_supportInCoset

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.LinearTaps.reproduces_of_ne_zero_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.LinearTaps.reproduces_of_ne_zero_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.AgreesOffAdjacent.reproduces_of_oneParity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.reproduces_of_oneParity_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.DoubledAgree.reproduces_dbl_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.DoubledAgree.reproduces_dbl_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_f22_of_supportInCoset_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_f22_of_supportInCoset_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_copies

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_copies_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_copies_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_copies_gap_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_copies_gap_load_bearing

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.finRule_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.finRule_ne_zero

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.step

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.step_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.step_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.iterate

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.translate

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.translate_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.translate_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_f22_iterate_of_supportInCoset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_f22_iterate_of_supportInCoset

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_f22_iterate_of_supportInCoset_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_f22_iterate_of_supportInCoset_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.of_finRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.of_finRule

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.iterate_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.iterate_iff

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.not_of_iterate_eq_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.not_of_iterate_eq_translate

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.not_of_iterate_eq_translate_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.not_of_iterate_eq_translate_nonvacuous
