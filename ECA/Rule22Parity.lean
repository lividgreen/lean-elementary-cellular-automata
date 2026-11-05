module

public import ECA.KinkMonotone
public import ECA.ReproducedPatterns
import all ECA.ReproducedPatterns
import all ECA.ReproductionBracket

/-!
# Rule `22` on the patterns of one parity
([RuleSpace] §5)

Two steps of rule `22` on a state supported on the even cells are rule `146` on its reduction, the
state read at the even cells (Gravner and Griffeath 2010, Lemma 3.1;
`Rule22Sparse.iterate_step_rule22_two_mul_reduction`). So the patterns rule `22` reproduces among
those of one parity are read off rule `146`'s, which reproduces exactly the nonzero patterns of
one parity.

## Main results

* `FiniteConfiguration.reduction` — the state read at the even cells.
* `finRule_f22_iterate_two_mul_reduction` — the instance of the identity at finite configurations.
* `Reproduces.reduction_f146` — a pattern on the even cells that rule `22` reproduces has a
  reduction that rule `146` reproduces, the diameter of the pattern being twice the reduction's
  less one and the copies standing at even times and even offsets.
* `reproduces_f22_iff_supportInCoset_of_oneParity` — **a pattern of one parity is reproduced at
  rule `22` exactly when it is nonzero and lies in one coset of `4ℤ`**; the one-parity hypothesis
  is load-bearing (`reproduces_f22_iff_supportInCoset_of_oneParity_load_bearing`).
* `supportInCoset_of_reproduces_f22_of_iterate_oneParity` — a reproduced pattern with an iterate of
  one parity lies, or its image lies, in one coset of `4ℤ`.
* Each statement has a `_nonvacuous` witness or a load-bearing guard at a fixed pattern.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The reduction -/

/-- **The reduction** of a finite configuration: its state read at the even cells, the value at the
cell `y` being the value at `2 * y` (Gravner and Griffeath 2010, §3). -/
noncomputable def FiniteConfiguration.reduction (s : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.comapDomain (fun y : ℤ => 2 * y) s (fun a _ b _ h => by
    simp only at h
    omega)

/-- The reduction reads the state at the even cells. -/
theorem FiniteConfiguration.reduction_apply (s : FiniteConfiguration) (y : ℤ) :
    reduction s y = s (2 * y) :=
  rfl

/-- Rule `146` of the block is the classical package's `rule146`. -/
private theorem f146_eq_rule146 : f146 = Rule22Sparse.rule146 := by
  funext a b c
  revert a b c
  decide

/-- **The instance at finite configurations**: from a configuration supported on the even cells,
rule `22` at time `2 * t` is again supported on the even cells and its reduction is rule `146`'s
orbit at time `t` of the reduction (`Rule22Sparse.iterate_step_rule22_two_mul_reduction`, Gravner
and Griffeath 2010, Lemma 3.1). -/
theorem finRule_f22_iterate_two_mul_reduction (s : FiniteConfiguration)
    (hs : ∀ j, Odd j → s j = 0) (t : ℕ) :
    (∀ j, Odd j → ((finRule f22 hq22)^[2 * t] s) j = 0) ∧
      reduction ((finRule f22 hq22)^[2 * t] s) = (finRule f146 hq146)^[t] (reduction s) := by
  obtain ⟨h1, h2⟩ := Rule22Sparse.iterate_step_rule22_two_mul_reduction (x := ⇑s) hs t
  have e22 : ⇑((finRule f22 hq22)^[2 * t] s) =
      (LocalRuleColumns.step Rule22Sparse.rule22)^[2 * t] ⇑s := by
    rw [coe_finRule_iterate, f22_eq_rule22]
  have e146 : ⇑((finRule f146 hq146)^[t] (reduction s)) =
      (LocalRuleColumns.step Rule22Sparse.rule146)^[t] ⇑(reduction s) := by
    rw [coe_finRule_iterate, f146_eq_rule146]
  have hr : ⇑(reduction s) = Rule22Sparse.reduction ⇑s := funext (reduction_apply s)
  refine ⟨fun j hj => by rw [e22]; exact h1 j hj, ?_⟩
  ext y
  rw [reduction_apply, congrFun e146 y, hr, e22]
  exact congrFun h2 y

/-! ## Helpers on the patterns on the even cells and on copies -/

/-- A nonzero state on the even cells has a nonzero reduction. -/
private theorem reduction_ne_zero {s : FiniteConfiguration} (hs : ∀ j, Odd j → s j = 0)
    (hne : s ≠ 0) : reduction s ≠ 0 := by
  intro h0
  apply hne
  ext x
  rcases Int.even_or_odd' x with ⟨y, rfl | rfl⟩
  · have := congrArg (fun r => r y) h0
    simpa [reduction_apply] using this
  · simpa using hs _ ⟨y, rfl⟩

/-- The diameter of a nonzero state on the even cells is at least twice its reduction's less one. -/
private theorem two_mul_diam_reduction_le {s : FiniteConfiguration}
    (hs : ∀ j, Odd j → s j = 0) (hne : s ≠ 0) : 2 * diam (reduction s) ≤ diam s + 1 := by
  have hr := reduction_ne_zero hs hne
  have hrne : (reduction s).support.Nonempty := Finsupp.support_nonempty_iff.mpr hr
  have ha : s (2 * (reduction s).support.min' hrne) ≠ 0 := by
    have := Finset.min'_mem _ hrne
    rwa [Finsupp.mem_support_iff, reduction_apply] at this
  have hb : s (2 * (reduction s).support.max' hrne) ≠ 0 := by
    have := Finset.max'_mem _ hrne
    rwa [Finsupp.mem_support_iff, reduction_apply] at this
  have h1 := le_diam_of_cells ha hb
  have h2 : diam (reduction s) =
      ((reduction s).support.max' hrne - (reduction s).support.min' hrne).toNat + 1 := by
    simp only [diam, hrne, ↓reduceDIte]
  have hab := Finset.min'_le_max' (reduction s).support hrne
  omega

/-- A cell of a copy is a cell of the sum of copies at gap at least two, with the same value. -/
private theorem sum_translate_apply_copy {p : FiniteConfiguration} {k G : ℕ} {c : ℕ → ℤ}
    (hG : 2 ≤ G) (hc : ∀ j, j + 1 < k → c j + diam p + G ≤ c (j + 1)) {j : ℕ} (hj : j < k)
    {a : ℤ} (ha : p a ≠ 0) :
    ((Finset.range k).sum fun j => translate (c j) p) (a + c j) = p a := by
  rw [Finsupp.finsetSum_apply]
  simp only [translate_apply']
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' hj' hne
    by_contra hcon
    have hj'k := Finset.mem_range.mp hj'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := copies_cells_apart hG hc hlt hj (a := a + c j - c j') (b := a) hcon ha
      omega
    · have := copies_cells_apart hG hc hgt hj'k (a := a) (b := a + c j - c j') ha hcon
      omega
  · intro hj0
    exact absurd (Finset.mem_range.mpr hj) hj0

/-- A sum of copies, at gap at least two, of a pattern on the even cells has no two adjacent set
cells. -/
private theorem sum_translate_not_adjacent {p : FiniteConfiguration} {k G : ℕ} {c : ℕ → ℤ}
    (hG : 2 ≤ G) (hc : ∀ j, j + 1 < k → c j + diam p + G ≤ c (j + 1))
    (hp : ∀ j, Odd j → p j = 0) (i : ℤ) :
    ¬ (((Finset.range k).sum fun j => translate (c j) p) i ≠ 0 ∧
      ((Finset.range k).sum fun j => translate (c j) p) (i + 1) ≠ 0) := by
  rintro ⟨h1, h2⟩
  rw [Finsupp.finsetSum_apply] at h1 h2
  simp only [translate_apply'] at h1 h2
  obtain ⟨j, hj, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨j', hj', hj0'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  have hjk := Finset.mem_range.mp hj
  have hj'k := Finset.mem_range.mp hj'
  rcases lt_trichotomy j j' with hlt | rfl | hgt
  · have := copies_cells_apart hG hc hlt hj'k hj0 hj0'
    omega
  · rcases Int.even_or_odd (i - c j) with he | ho
    · exact hj0' (by
        have : Odd (i + 1 - c j) := by
          rcases he with ⟨r, hr⟩
          exact ⟨r, by omega⟩
        exact hp _ this)
    · exact hj0 (hp _ ho)
  · have := copies_cells_apart hG hc hgt hjk hj0' hj0
    omega

/-- One step of rule `22` on a nonzero state on the even cells sets two adjacent cells: the cells
just left of the leftmost set cell and at it. -/
private theorem exists_adjacent_finRule_f22 {w : FiniteConfiguration}
    (hw : ∀ j, Odd j → w j = 0) (hne : w ≠ 0) :
    ∃ i, finRule f22 hq22 w i ≠ 0 ∧ finRule f22 hq22 w (i + 1) ≠ 0 := by
  have hs : w.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  have hm : w (w.support.min' hs) ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs)
  have hlow : ∀ y, y < w.support.min' hs → w y = 0 := fun y hy => by
    by_contra h
    have := Finset.min'_le w.support y (Finsupp.mem_support_iff.mpr h)
    omega
  generalize w.support.min' hs = m at hm hlow
  have hmeven : m % 2 = 0 := by
    by_contra hcon
    exact hm (hw m (Int.odd_iff.mpr (by omega)))
  have hm1 : w (m + 1) = 0 := hw _ (Int.odd_iff.mpr (by omega))
  have hm1' : w m = 1 := by
    revert hm
    generalize w m = a
    revert a
    decide
  refine ⟨m - 1, ?_, ?_⟩
  · rw [finRule_apply, hlow (m - 1 - 1) (by omega), hlow (m - 1) (by omega),
      show m - 1 + 1 = m by ring, hm1']
    decide
  · rw [finRule_apply, show m - 1 + 1 = m by ring, hlow (m - 1) (by omega), hm1', hm1]
    decide

/-- The reduction of a sum of translates by even offsets is the sum of the translates of the
reduction by the halved offsets. -/
private theorem reduction_sum_translate {p : FiniteConfiguration} {k : ℕ} {c d : ℕ → ℤ}
    (hd : ∀ j, j < k → c j = 2 * d j) :
    reduction ((Finset.range k).sum fun j => translate (c j) p) =
      (Finset.range k).sum fun j => translate (d j) (reduction p) := by
  ext y
  rw [reduction_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [translate_apply', translate_apply', reduction_apply, hd j (Finset.mem_range.mp hj)]
  congr 1
  ring

/-! ## The reduction of a reproduced pattern on the even cells -/

/-- **A pattern on the even cells that rule `22` reproduces has a reduction that rule `146`
reproduces** ([RuleSpace] §5). One step of rule `22` on a nonzero state on the even cells sets two
adjacent cells, which copies of the pattern never have, so the copies stand at an even time; there
the reduction of the copies is copies of the reduction at half the offsets, the diameter of the
pattern being at least twice the reduction's less one. -/
theorem Reproduces.reduction_f146 {s : FiniteConfiguration} (hs : ∀ j, Odd j → s j = 0)
    (h : Reproduces (finRule f22 hq22) s) : Reproduces (finRule f146 hq146) (reduction s) := by
  have hsne := h.1
  refine ⟨reduction_ne_zero hs hsne, fun N G => ?_⟩
  obtain ⟨t, k, hk, c, hc, hS⟩ := h.2 N (2 * G + 2)
  rcases Nat.even_or_odd' t with ⟨u, rfl | rfl⟩
  · obtain ⟨hodd, hred⟩ := finRule_f22_iterate_two_mul_reduction s hs u
    have hceven : ∀ j, j < k → c j % 2 = 0 := by
      intro j hj
      obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hsne
      have ha' : s a ≠ 0 := by simpa using ha
      have h1 := sum_translate_apply_copy (G := 2 * G + 2) (by omega) hc hj ha'
      have h2 : ((finRule f22 hq22)^[2 * u] s) (a + c j) ≠ 0 := by
        rw [hS, h1]
        exact ha'
      have hnodd : ¬ Odd (a + c j) := fun ho => h2 (hodd _ ho)
      have hae : ¬ Odd a := fun ho => ha' (hs _ ho)
      rw [Int.not_odd_iff] at hnodd hae
      omega
    have hd : ∀ j, j < k → c j = 2 * (fun j => c j / 2) j := fun j hj => by
      have := hceven j hj
      simp only
      omega
    have hdiam := two_mul_diam_reduction_le hs hsne
    refine ⟨u, k, hk, fun j => c j / 2, fun j hj => ?_, ?_⟩
    · have h1 := hc j hj
      have e1 := hceven j (by omega)
      have e2 := hceven (j + 1) hj
      simp only
      omega
    · rw [← hred, hS]
      exact reduction_sum_translate hd
  · exfalso
    have hw := Reproduces.iterate f22 hq22 h (2 * u)
    obtain ⟨hodd, -⟩ := finRule_f22_iterate_two_mul_reduction s hs u
    obtain ⟨i, hi1, hi2⟩ := exists_adjacent_finRule_f22 hodd hw.1
    rw [Function.iterate_succ_apply'] at hS
    rw [hS] at hi1 hi2
    exact sum_translate_not_adjacent (G := 2 * G + 2) (by omega) hc hs i ⟨hi1, hi2⟩

/-- The cells `-1`, `0` and `1`: the image of the single cell at rule `22`. -/
private noncomputable def threeCells : FiniteConfiguration :=
  Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
    Finsupp.single 1 (1 : ZMod 2)

private theorem supportInCoset_single_zero :
    Rule22Sparse.SupportInCoset 4 ⇑(Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration) := by
  intro i j hi hj
  simp only [Finsupp.single_apply] at hi hj
  split_ifs at hi hj <;> first | omega | simp_all

private theorem threeCells_apply (x : ℤ) :
    threeCells x = if -1 ≤ x ∧ x ≤ 1 then 1 else 0 := by
  simp only [threeCells, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> first | omega | decide

private theorem finRule_f22_single_zero :
    finRule f22 hq22 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = threeCells := by
  ext i
  rw [finRule_apply]
  simp only [threeCells, f22, wolframRule, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> first | decide | (exfalso; omega)

private theorem reproduces_f22_threeCells : Reproduces (finRule f22 hq22) threeCells := by
  have h := reproduces_f22_iterate_of_supportInCoset supportInCoset_single_zero
    (show (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ≠ 0 by simp) 1
  rwa [Function.iterate_one, finRule_f22_single_zero] at h

private theorem not_supportInCoset_threeCells : ¬ Rule22Sparse.SupportInCoset 4 ⇑threeCells := by
  intro h
  have := h (-1) 0 (by simp [threeCells]) (by simp [threeCells])
  omega

/-- The reduction statement has a fixed instance: the single cell `0` is on the even cells, rule
`22` reproduces it, its reduction is the single cell `0`, and rule `146` reproduces that. -/
theorem Reproduces.reduction_f146_nonvacuous :
    (∀ j, Odd j → (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration) j = 0) ∧
      Reproduces (finRule f22 hq22) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ∧
      reduction (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = Finsupp.single 0 1 ∧
      Reproduces (finRule f146 hq146) (reduction (Finsupp.single (0 : ℤ) (1 : ZMod 2))) := by
  have hodd : ∀ j, Odd j → (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration) j = 0 := by
    intro j hj
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h
      exact absurd hj (by decide)
    · rfl
  have hrep := reproduces_f22_of_supportInCoset supportInCoset_single_zero
    (show (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ≠ 0 by simp)
  have hred : reduction (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = Finsupp.single 0 1 := by
    ext y
    rw [reduction_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> first | rfl | omega
  exact ⟨hodd, hrep, hred, Reproduces.reduction_f146 hodd hrep⟩

/-! ## The patterns of one parity -/

/-- **A pattern of one parity is reproduced at rule `22` exactly when it is nonzero and lies in one
coset of `4ℤ`** ([RuleSpace] §5). A pattern of one parity is a translate by `0` or `1` of a state
on the even cells; its reduction is of one parity at rule `146`, which reproduces exactly the
nonzero patterns of one parity, and a reduction of one parity is a state in one coset of `4ℤ`. -/
theorem reproduces_f22_iff_supportInCoset_of_oneParity {p : FiniteConfiguration}
    (hp : OneParity p) :
    Reproduces (finRule f22 hq22) p ↔ p ≠ 0 ∧ Rule22Sparse.SupportInCoset 4 ⇑p := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp h.1
    have ha' : p a ≠ 0 := by simpa using ha
    obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = a % 2 := ⟨_, rfl⟩
    have hq : Reproduces (finRule f22 hq22) (translate (-ε) p) :=
      Reproduces.translate f22 hq22 h (-ε)
    have hqodd : ∀ j, Odd j → translate (-ε) p j = 0 := by
      intro j hj
      by_contra hne
      rw [translate_apply'] at hne
      have h2 := hp _ _ hne ha'
      rw [Int.even_iff] at h2
      rw [Int.odd_iff] at hj
      omega
    have hone := ((reproduces_iff_oneParity_f146 _).mp (Reproduces.reduction_f146 hqodd hq)).2
    intro i j hi hj
    have hi' : translate (-ε) p (i - ε) ≠ 0 := by
      rw [translate_apply']
      simpa using hi
    have hj' : translate (-ε) p (j - ε) ≠ 0 := by
      rw [translate_apply']
      simpa using hj
    have hie : (i - ε) % 2 = 0 := by
      by_contra hcon
      exact hi' (hqodd _ (Int.odd_iff.mpr (by omega)))
    have hje : (j - ε) % 2 = 0 := by
      by_contra hcon
      exact hj' (hqodd _ (Int.odd_iff.mpr (by omega)))
    have h3 := hone ((i - ε) / 2) ((j - ε) / 2)
      (by rwa [reduction_apply, show 2 * ((i - ε) / 2) = i - ε by omega])
      (by rwa [reduction_apply, show 2 * ((j - ε) / 2) = j - ε by omega])
    rw [Int.even_iff] at h3
    omega
  · rintro ⟨hne, hc⟩
    exact reproduces_f22_of_supportInCoset hc hne

/-- One parity is load-bearing: the pattern of the cells `-1`, `0` and `1` is reproduced at rule
`22`, is not of one parity and does not lie in one coset of `4ℤ`. -/
theorem reproduces_f22_iff_supportInCoset_of_oneParity_load_bearing :
    Reproduces (finRule f22 hq22)
        (Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
          Finsupp.single 1 (1 : ZMod 2) : FiniteConfiguration) ∧
      ¬ OneParity (Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
          Finsupp.single 1 (1 : ZMod 2) : FiniteConfiguration) ∧
      ¬ Rule22Sparse.SupportInCoset 4
        ⇑(Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
          Finsupp.single 1 (1 : ZMod 2) : FiniteConfiguration) := by
  refine ⟨reproduces_f22_threeCells, fun h => ?_, not_supportInCoset_threeCells⟩
  have := h (-1) 0 (by simp) (by simp)
  rw [Int.even_iff] at this
  omega

/-! ## A reproduced pattern with an iterate of one parity -/

/-- The diameter along an orbit grows by at most two a step. -/
private theorem diam_iterate_finRule_le (f : LocalRule) (hq : f 0 0 0 = 0) (p : FiniteConfiguration)
    (t : ℕ) : diam ((finRule f hq)^[t] p) ≤ diam p + 2 * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have := diam_finRule_le_add_two f hq ((finRule f hq)^[t] p)
    omega

/-- A copy of a pattern inside a state supported in one coset of `4ℤ` is supported in one. -/
private theorem supportInCoset_of_copies {p : FiniteConfiguration} {k G : ℕ} {c : ℕ → ℤ}
    (hG : 2 ≤ G) (hc : ∀ j, j + 1 < k → c j + diam p + G ≤ c (j + 1)) (hk : 0 < k)
    (h : Rule22Sparse.SupportInCoset 4
      ⇑((Finset.range k).sum fun j => translate (c j) p)) :
    Rule22Sparse.SupportInCoset 4 ⇑p := by
  intro a b ha hb
  have h1 := sum_translate_apply_copy hG hc hk ha
  have h2 := sum_translate_apply_copy hG hc hk hb
  have := h (a + c 0) (b + c 0) (by rw [h1]; exact ha) (by rw [h2]; exact hb)
  omega

/-- **A reproduced pattern with an iterate of one parity lies, or its image lies, in one coset of
`4ℤ`** ([RuleSpace] §5). The iterate is reproduced and of one parity, so it lies in one coset of
`4ℤ`, as does every second iterate of it; at a reproduction time after the iterate, the copies of
the pattern, or at the next time the copies of its image, are such an iterate. -/
theorem supportInCoset_of_reproduces_f22_of_iterate_oneParity {p : FiniteConfiguration}
    (h : Reproduces (finRule f22 hq22) p) {n : ℕ} (hn : OneParity ((finRule f22 hq22)^[n] p)) :
    Rule22Sparse.SupportInCoset 4 ⇑p ∨ Rule22Sparse.SupportInCoset 4 ⇑(finRule f22 hq22 p) := by
  have hq : Reproduces (finRule f22 hq22) ((finRule f22 hq22)^[n] p) :=
    Reproduces.iterate f22 hq22 h n
  have hqc := ((reproduces_f22_iff_supportInCoset_of_oneParity hn).mp hq).2
  have hevenc : ∀ m, Rule22Sparse.SupportInCoset 4 ⇑((finRule f22 hq22)^[2 * m]
      ((finRule f22 hq22)^[n] p)) := by
    intro m
    have e2 : LocalRuleColumns.step f22 = LocalRuleColumns.step Rule22Sparse.rule22 := by
      rw [f22_eq_rule22]
    rw [coe_finRule_iterate, e2]
    exact Rule22Sparse.supportInCoset_iterate_step_rule22_two_mul hqc m
  obtain ⟨t, k, hk, c, hc, hS⟩ := h.2 (diam p + 2 * n + 1) 4
  have hpne := h.1
  have ht : n ≤ t := by
    by_contra htn
    have h1 := copies_diam_le hpne ⟨c, hc, hS⟩ (by omega)
    have h2 := diam_iterate_finRule_le f22 hq22 p t
    have h3 := one_le_diam_of_ne_zero hpne
    have h4 : k ≤ k * p.diam := Nat.le_mul_of_pos_right k h3
    omega
  have hk0 : 0 < k := by omega
  rcases Nat.even_or_odd' (t - n) with ⟨m, hm | hm⟩
  · left
    have e : (finRule f22 hq22)^[t] p = (finRule f22 hq22)^[2 * m] ((finRule f22 hq22)^[n] p) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [e] at hS
    exact supportInCoset_of_copies (by omega) hc hk0 (hS ▸ hevenc m)
  · right
    have e : (finRule f22 hq22)^[t + 1] p =
        (finRule f22 hq22)^[2 * (m + 1)] ((finRule f22 hq22)^[n] p) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [Function.iterate_succ_apply', hS,
      finRule_sum_translate f22 hq22 (by omega : 2 ≤ 4) hc] at e
    have hc' : ∀ j, j + 1 < k → c j + diam (finRule f22 hq22 p) + 2 ≤ c (j + 1) := by
      intro j hj
      have := hc j hj
      have := diam_finRule_le_add_two f22 hq22 p
      omega
    exact supportInCoset_of_copies (G := 2) (by omega) hc' hk0 (e ▸ hevenc (m + 1))

/-- The orbit statement has a fixed instance: the pattern of the cells `-1`, `0` and `1` is
reproduced at rule `22`, its image, the cells `-2` and `2`, is of one parity, the pattern does not
lie in one coset of `4ℤ` and its image does. -/
theorem supportInCoset_of_reproduces_f22_of_iterate_oneParity_nonvacuous :
    Reproduces (finRule f22 hq22)
        (Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
          Finsupp.single 1 (1 : ZMod 2) : FiniteConfiguration) ∧
      (finRule f22 hq22)^[1] (Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
          Finsupp.single 1 (1 : ZMod 2) : FiniteConfiguration) =
        Finsupp.single (-2) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2) ∧
      OneParity ((finRule f22 hq22)^[1] (Finsupp.single (-1) (1 : ZMod 2) +
          Finsupp.single 0 (1 : ZMod 2) + Finsupp.single 1 (1 : ZMod 2) : FiniteConfiguration)) ∧
      ¬ Rule22Sparse.SupportInCoset 4
        ⇑(Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
          Finsupp.single 1 (1 : ZMod 2) : FiniteConfiguration) ∧
      Rule22Sparse.SupportInCoset 4
        ⇑(finRule f22 hq22 (Finsupp.single (-1) (1 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) +
          Finsupp.single 1 (1 : ZMod 2) : FiniteConfiguration)) := by
  have himg : (finRule f22 hq22)^[1] threeCells =
      Finsupp.single (-2) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2) := by
    ext i
    rw [Function.iterate_one, finRule_apply, threeCells_apply, threeCells_apply, threeCells_apply]
    simp only [f22, wolframRule, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> first | decide | (exfalso; omega)
  have hpar : OneParity (Finsupp.single (-2) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) := by
    intro i j hi hj
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
    rw [even_iff_two_dvd]
    split_ifs at hi hj <;> first | omega | simp_all
  have hcoset : Rule22Sparse.SupportInCoset 4
      ⇑(Finsupp.single (-2) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2) :
        FiniteConfiguration) := by
    intro i j hi hj
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
    split_ifs at hi hj <;> first | omega | simp_all
  refine ⟨reproduces_f22_threeCells, himg, himg ▸ hpar, not_supportInCoset_threeCells, ?_⟩
  change Rule22Sparse.SupportInCoset 4 ⇑(finRule f22 hq22 threeCells)
  have himg' : finRule f22 hq22 threeCells =
      Finsupp.single (-2) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2) := himg
  rw [himg']
  exact hcoset

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.reduction_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.reduction_apply

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_f22_iterate_two_mul_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f22_iterate_two_mul_reduction

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.reduction_f146' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.reduction_f146

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.reduction_f146_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.reduction_f146_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_f22_iff_supportInCoset_of_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_f22_iff_supportInCoset_of_oneParity

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_f22_iff_supportInCoset_of_oneParity_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_f22_iff_supportInCoset_of_oneParity_load_bearing

set_option linter.style.longLine false in
/-- info: 'ECA.supportInCoset_of_reproduces_f22_of_iterate_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.supportInCoset_of_reproduces_f22_of_iterate_oneParity

set_option linter.style.longLine false in
/-- info: 'ECA.supportInCoset_of_reproduces_f22_of_iterate_oneParity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.supportInCoset_of_reproduces_f22_of_iterate_oneParity_nonvacuous
