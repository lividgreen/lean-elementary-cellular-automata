module

public import ECA.NeverCreated
public import Mathlib.Data.Fin.VecNotation
import all ECA.DefectCounts
import all ECA.NeverCreated

/-!
# A local count with a potential never increases, and the patterns it keeps a rule from reproducing
([RuleSpace] §5)

[RuleSpace] §5 Proposition 5.27 excludes the reproduction of a pattern by a count that one step
never increases and that copies carry, and Proposition 5.46 gives such a count for a word that a
rule never creates in place. This module gives a count of a different kind, whose monotonicity
rests on a weight on the windows of the image and on no single word: an additive local count with
a potential.

* `FiniteConfiguration.window`, `FiniteConfiguration.windowSites` and
  `FiniteConfiguration.localCount` — the `W` cells from a cell, the cells whose window meets the
  support, and the additive local count `C(s) = Σ_i φ (s (i), …, s (i + W − 1))` of a weight `φ`
  on windows of `W` cells that weighs the clear window `0`; `FiniteConfiguration.localCount_eq_sum`
  — the sum may be taken over any set of cells holding the sites.
* `LocalRule.PotentialCert` — a **potential certificate**: an integer weight `π` on the windows of
  `W + 1` cells such that at every window `u` of `W + 2` cells, `φ` of the image's middle `W` cells
  plus `π` of the first `W + 1` cells is at most `φ` of the middle `W` cells plus `π` of the last
  `W + 1` cells.
* `LocalRule.PotentialCert.localCount_finRule_le` — **a certificate makes the count never increase
  in one step**: summed over the cells, the potentials telescope between two clear windows.
* `localCount_copies` — `k` copies of a pattern at a gap of at least `W − 1` carry at least `k`
  times its local count; `not_reproduces_of_count_mono_gap` — the exclusion of Proposition 5.27(i)
  with the copies bound required from a gap `G₀` on.
* `LocalRule.PotentialCert.not_reproduces` — **the exclusion**: a rule with a potential certificate
  for a weight `φ` reproduces no pattern of positive local count.
* Two counts of width `9` at rule `22`, found by a linear program outside the artifact, whose
  certificates are decided over the `2048` windows of eleven cells: `phiA` with `piA`, positive at
  `p101101` (`localCount_phiA_p101101`, `not_reproduces_f22_101101`), and `phiB` with `piB`,
  positive at `p1011001` (`localCount_phiB_p1011001`, `not_reproduces_f22_1011001`). Neither
  pattern reads the word `10101` (`p101101_not_reads_10101`, `p1011001_not_reads_10101`), so
  Proposition 5.46 does not reach them, and `p101101` has the even diameter `6` (`diam_p101101`).
* `LocalRule.PotentialCert.not_reproduces_nonvacuous` — the hypotheses of the exclusion hold at
  once. `potentialCert_f22_phiA_load_bearing` shows the certificate is load-bearing: at rule `90`
  the count `phiA` rises from `p1001` to `2`, and no potential certifies it there.
  `localCount_copies_gap_load_bearing` shows the gap hypothesis of `localCount_copies` cannot be
  dropped.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## Windows and the local count -/

/-- **The window of `W` cells from a cell**: the states of the cells `i, i + 1, …, i + W - 1`, cell
`i` first. -/
def FiniteConfiguration.window (s : FiniteConfiguration) (W : ℕ) (i : ℤ) : Fin W → ZMod 2 :=
  fun k => s (i + ((k : ℕ) : ℤ))

/-- **The cells whose window of width `W` meets the support**: the cells `i` with a set cell among
`i, …, i + W - 1`. A window off these cells is clear. -/
def FiniteConfiguration.windowSites (s : FiniteConfiguration) (W : ℕ) : Finset ℤ :=
  s.support.biUnion fun j => Finset.Icc (j - ((W - 1 : ℕ) : ℤ)) j

/-- **The additive local count** of a weight `φ` on the windows of `W` cells:
`Σ_i φ (s (i), …, s (i + W - 1))` over the cells whose window meets the support. When `φ` weighs
the clear window `0` this is the sum over every cell (`FiniteConfiguration.localCount_eq_sum`). -/
def FiniteConfiguration.localCount {W : ℕ} (φ : (Fin W → ZMod 2) → ℕ)
    (s : FiniteConfiguration) : ℕ :=
  ∑ i ∈ s.windowSites W, φ (s.window W i)

private theorem mem_windowSites {s : FiniteConfiguration} {W : ℕ} {i : ℤ} :
    i ∈ s.windowSites W ↔ ∃ j, s j ≠ 0 ∧ j - ((W - 1 : ℕ) : ℤ) ≤ i ∧ i ≤ j := by
  unfold FiniteConfiguration.windowSites
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hi⟩
    exact ⟨j, Finsupp.mem_support_iff.mp hj, (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2⟩
  · rintro ⟨j, hj, h1, h2⟩
    exact ⟨j, Finsupp.mem_support_iff.mpr hj, Finset.mem_Icc.mpr ⟨h1, h2⟩⟩

/-- A state supported in `[a, b]` has its sites in `[a - (W - 1), b]`. -/
private theorem windowSites_subset {s : FiniteConfiguration} {W : ℕ} {a b : ℤ}
    (h : ∀ j, s j ≠ 0 → a ≤ j ∧ j ≤ b) :
    s.windowSites W ⊆ Finset.Icc (a - ((W - 1 : ℕ) : ℤ)) b := by
  intro i hi
  obtain ⟨j, hj, h1, h2⟩ := mem_windowSites.mp hi
  have := h j hj
  rw [Finset.mem_Icc]
  omega

/-- **The local count is the sum over any set of cells holding the sites**: a window off the sites
is clear and weighs `0`. -/
theorem FiniteConfiguration.localCount_eq_sum {W : ℕ} {φ : (Fin W → ZMod 2) → ℕ}
    (hφ : φ 0 = 0) {s : FiniteConfiguration} {T : Finset ℤ} (hT : s.windowSites W ⊆ T) :
    s.localCount φ = ∑ i ∈ T, φ (s.window W i) := by
  unfold FiniteConfiguration.localCount
  refine Finset.sum_subset hT (fun i _ hi => ?_)
  have hclear : s.window W i = 0 := by
    funext k
    by_contra hne
    apply hi
    refine mem_windowSites.mpr ⟨i + ((k : ℕ) : ℤ), hne, ?_, ?_⟩
    · have := k.isLt
      omega
    · omega
  rw [hclear]
  exact hφ

/-- The state `s` supported in `[a, b]` with cells `s x = if P x then 1 else 0`: its local count is
the sum over the cells of `[a - (W - 1), b]` of the weight of the window read off `P`. -/
private theorem localCount_of_cells {W : ℕ} {φ : (Fin W → ZMod 2) → ℕ} (hφ : φ 0 = 0)
    {s : FiniteConfiguration} {P : ℤ → Prop} [DecidablePred P]
    (hs : ∀ x, s x = if P x then 1 else 0) {a b : ℤ} (hab : ∀ x, P x → a ≤ x ∧ x ≤ b) :
    s.localCount φ = ∑ i ∈ Finset.Icc (a - ((W - 1 : ℕ) : ℤ)) b,
      φ (fun k : Fin W => if P (i + ((k : ℕ) : ℤ)) then 1 else 0) := by
  have hsupp : ∀ x, s x ≠ 0 → a ≤ x ∧ x ≤ b := by
    intro x hx
    apply hab
    by_contra hP
    apply hx
    rw [hs]
    simp [hP]
  rw [FiniteConfiguration.localCount_eq_sum hφ (windowSites_subset hsupp)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  funext k
  simp [FiniteConfiguration.window, hs]

/-! ## The potential certificate -/

/-- **The middle `W` cells** of a window of `W + 2` cells: the cells `1, …, W`. -/
def windowMiddle {W : ℕ} (u : Fin (W + 2) → ZMod 2) : Fin W → ZMod 2 :=
  fun k => u ⟨k + 1, by omega⟩

/-- **The first `W + 1` cells** of a window of `W + 2` cells: the cells `0, …, W`. -/
def windowTail {W : ℕ} (u : Fin (W + 2) → ZMod 2) : Fin (W + 1) → ZMod 2 :=
  fun k => u k.castSucc

/-- **The last `W + 1` cells** of a window of `W + 2` cells: the cells `1, …, W + 1`. -/
def windowHead {W : ℕ} (u : Fin (W + 2) → ZMod 2) : Fin (W + 1) → ZMod 2 :=
  fun k => u k.succ

/-- **The rule at the middle `W` cells** of a window of `W + 2` cells, which the window determines:
cell `k` of the result is `f` of the cells `k`, `k + 1`, `k + 2`. -/
def LocalRule.imageMiddle {W : ℕ} (f : LocalRule) (u : Fin (W + 2) → ZMod 2) :
    Fin W → ZMod 2 :=
  fun k => f (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩) (u ⟨k + 2, by omega⟩)

/-- **A potential certificate** of a weight `φ` on the windows of `W` cells for a rule `f`: an
integer weight `π` on the windows of `W + 1` cells such that at every window `u` of `W + 2` cells,
`φ` of the image's middle `W` cells plus `π` of the first `W + 1` cells is at most `φ` of the middle
`W` cells plus `π` of the last `W + 1` cells. -/
def LocalRule.PotentialCert {W : ℕ} (f : LocalRule) (φ : (Fin W → ZMod 2) → ℕ)
    (π : (Fin (W + 1) → ZMod 2) → ℤ) : Prop :=
  ∀ u : Fin (W + 2) → ZMod 2,
    (φ (f.imageMiddle u) : ℤ) + π (windowTail u) ≤ (φ (windowMiddle u) : ℤ) + π (windowHead u)

/-! ## The count never increases in one step -/

private theorem window_finRule {W : ℕ} (f : LocalRule) (hq : f 0 0 0 = 0) (s : FiniteConfiguration)
    (i : ℤ) : (finRule f hq s).window W i = f.imageMiddle (s.window (W + 2) (i - 1)) := by
  funext k
  simp only [FiniteConfiguration.window, LocalRule.imageMiddle, finRule_apply, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat]
  ring_nf

private theorem windowMiddle_window {W : ℕ} (s : FiniteConfiguration) (i : ℤ) :
    windowMiddle (s.window (W + 2) (i - 1)) = s.window W i := by
  funext k
  simp only [windowMiddle, FiniteConfiguration.window, Nat.cast_add, Nat.cast_one]
  ring_nf

private theorem windowTail_window {W : ℕ} (s : FiniteConfiguration) (i : ℤ) :
    windowTail (s.window (W + 2) (i - 1)) = s.window (W + 1) (i - 1) := by
  funext k
  simp [windowTail, FiniteConfiguration.window]

private theorem windowHead_window {W : ℕ} (s : FiniteConfiguration) (i : ℤ) :
    windowHead (s.window (W + 2) (i - 1)) = s.window (W + 1) i := by
  funext k
  simp only [windowHead, FiniteConfiguration.window, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring_nf

private theorem sum_Icc_telescope_nat (g : ℤ → ℤ) (A : ℤ) :
    ∀ n : ℕ, ∑ i ∈ Finset.Icc A (A - 1 + n), (g i - g (i - 1)) = g (A - 1 + n) - g (A - 1)
  | 0 => by simp
  | n + 1 => by
    have hins : Finset.Icc A (A - 1 + ((n + 1 : ℕ) : ℤ)) =
        insert (A - 1 + ((n + 1 : ℕ) : ℤ)) (Finset.Icc A (A - 1 + n)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [hins, Finset.sum_insert (by simp), sum_Icc_telescope_nat g A n]
    push_cast
    ring_nf

/-- A sum of consecutive differences over `[A, B]` is the difference of the ends. -/
private theorem sum_Icc_telescope (g : ℤ → ℤ) {A B : ℤ} (h : A ≤ B + 1) :
    ∑ i ∈ Finset.Icc A B, (g i - g (i - 1)) = g B - g (A - 1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, B = A - 1 + n := ⟨(B - (A - 1)).toNat, by omega⟩
  subst hn
  exact sum_Icc_telescope_nat g A n

/-- **A potential certificate makes the local count never increase in one step**: the inequality of
the certificate, summed over the cells of a set holding the sites of the state and of its image,
telescopes in the potential between two clear windows. -/
theorem LocalRule.PotentialCert.localCount_finRule_le {f : LocalRule} {W : ℕ}
    {φ : (Fin W → ZMod 2) → ℕ} {π : (Fin (W + 1) → ZMod 2) → ℤ} (hq : f 0 0 0 = 0)
    (hφ : φ 0 = 0) (h : PotentialCert f φ π) (s : FiniteConfiguration) :
    (finRule f hq s).localCount φ ≤ s.localCount φ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ x, s x ≠ 0 → -(N : ℤ) ≤ x ∧ x ≤ N := by
    refine ⟨s.support.sup Int.natAbs, fun x hx => ?_⟩
    have := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.mpr hx)
    omega
  -- the image is supported one cell further out on each side
  have himg : ∀ x, finRule f hq s x ≠ 0 → -((N : ℤ) + 1) ≤ x ∧ x ≤ (N : ℤ) + 1 := by
    intro x hx
    rw [finRule_apply] at hx
    by_contra hbad
    apply hx
    have h1 : s (x - 1) = 0 := by
      by_contra hne
      have := hN _ hne
      omega
    have h2 : s x = 0 := by
      by_contra hne
      have := hN _ hne
      omega
    have h3 : s (x + 1) = 0 := by
      by_contra hne
      have := hN _ hne
      omega
    rw [h1, h2, h3]
    exact hq
  have hT1 : s.windowSites W ⊆ Finset.Icc (-(N : ℤ) - W - 1) ((N : ℤ) + 1) := by
    refine (windowSites_subset hN).trans (Finset.Icc_subset_Icc ?_ ?_) <;> omega
  have hT2 : (finRule f hq s).windowSites W ⊆ Finset.Icc (-(N : ℤ) - W - 1) ((N : ℤ) + 1) := by
    refine (windowSites_subset himg).trans (Finset.Icc_subset_Icc ?_ ?_) <;> omega
  rw [FiniteConfiguration.localCount_eq_sum hφ hT2, FiniteConfiguration.localCount_eq_sum hφ hT1]
  have key : ∀ i : ℤ, (φ ((finRule f hq s).window W i) : ℤ) + π (s.window (W + 1) (i - 1)) ≤
      (φ (s.window W i) : ℤ) + π (s.window (W + 1) i) := by
    intro i
    have := h (s.window (W + 2) (i - 1))
    rwa [← window_finRule, windowMiddle_window, windowTail_window, windowHead_window] at this
  have hsum := Finset.sum_le_sum (s := Finset.Icc (-(N : ℤ) - W - 1) ((N : ℤ) + 1))
    (fun i _ => key i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have htel := sum_Icc_telescope (fun i => π (s.window (W + 1) i))
    (A := -(N : ℤ) - W - 1) (B := (N : ℤ) + 1) (by omega)
  rw [Finset.sum_sub_distrib] at htel
  have hB : s.window (W + 1) ((N : ℤ) + 1) = 0 := by
    funext k
    by_contra hne
    have := hN _ hne
    omega
  have hA : s.window (W + 1) (-(N : ℤ) - W - 1 - 1) = 0 := by
    funext k
    by_contra hne
    have := hN _ hne
    have hk := k.isLt
    omega
  simp only [hA, hB, sub_self] at htel
  have hle : ((∑ i ∈ Finset.Icc (-(N : ℤ) - W - 1) ((N : ℤ) + 1),
      φ ((finRule f hq s).window W i) : ℕ) : ℤ) ≤
      ((∑ i ∈ Finset.Icc (-(N : ℤ) - W - 1) ((N : ℤ) + 1), φ (s.window W i) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast hle

/-! ## Copies carry the count -/

/-- **`k` copies of a pattern at a gap of at least `W - 1` carry at least `k` times its local
count**: a window of the pattern lies in the hull of the pattern widened by `W - 1` cells on the
left, where the other copies vanish, so its translate by each copy's offset is a window of the sum,
and distinct copies give distinct cells. -/
theorem localCount_copies {W : ℕ} {φ : (Fin W → ZMod 2) → ℕ}
    {p s : FiniteConfiguration} {k G : ℕ} (h : Copies p s k G) (hG : W ≤ G + 1) :
    k * p.localCount φ ≤ s.localCount φ := by
  obtain ⟨c, hc, hs⟩ := h
  by_cases hp : p = 0
  · subst hp
    simp [FiniteConfiguration.localCount, FiniteConfiguration.windowSites]
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmM := Finset.min'_le_max' p.support hpne
  have hd : (diam p : ℤ) = p.support.max' hpne - p.support.min' hpne + 1 := by
    unfold diam
    rw [dite_eq_left hpne]
    omega
  -- the sites of the pattern lie in its hull widened to the left
  have hsite : ∀ i ∈ p.windowSites W, p.support.min' hpne - ((W - 1 : ℕ) : ℤ) ≤ i ∧
      i ≤ p.support.max' hpne := by
    intro i hi
    obtain ⟨j, hj, h1, h2⟩ := mem_windowSites.mp hi
    have := Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hj)
    have := Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hj)
    omega
  -- a window of the widened hull of copy `j` is the window of the sum
  have hwin : ∀ j < k, ∀ i : ℤ, p.support.min' hpne - ((W - 1 : ℕ) : ℤ) ≤ i →
      i ≤ p.support.max' hpne → s.window W (i + c j) = p.window W i := by
    intro j hj i h1 h2
    funext k'
    have hk' := k'.isLt
    have e := copies_apply hpne hc (g := W - 1) (by omega) hj (x := i + ((k' : ℕ) : ℤ))
      (by omega) (by omega)
    rw [← hs] at e
    simp only [FiniteConfiguration.window]
    rw [show i + c j + ((k' : ℕ) : ℤ) = i + ((k' : ℕ) : ℤ) + c j by ring, e]
  -- a set cell of the pattern stays set in the sum
  have hsupp : ∀ j < k, ∀ y : ℤ, p y ≠ 0 → s (y + c j) ≠ 0 := by
    intro j hj y hy
    have h1 := Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hy)
    have h2 := Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hy)
    have e := copies_apply hpne hc (g := 0) (Nat.zero_le _) hj (x := y) (by omega) (by omega)
    rw [← hs] at e
    rw [e]
    exact hy
  have hinj : Set.InjOn (fun x : ℕ × ℤ => x.2 + c x.1)
      ↑(Finset.range k ×ˢ p.windowSites W) := by
    intro x hx y hy he
    obtain ⟨hj, hi⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
    obtain ⟨hj2, hi2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hy)
    have hj' := Finset.mem_range.mp hj
    have hj2' := Finset.mem_range.mp hj2
    obtain ⟨hb1, hb2⟩ := hsite _ hi
    obtain ⟨hb3, hb4⟩ := hsite _ hi2
    simp only at he
    have hq1 : x.1 = y.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := copies_ord hc hlt hj2'
        omega
      · have := copies_ord hc hgt hj'
        omega
    have : x.2 = y.2 := by rw [hq1] at he; omega
    exact Prod.ext hq1 this
  have hsub : (Finset.range k ×ˢ p.windowSites W).image (fun x : ℕ × ℤ => x.2 + c x.1) ⊆
      s.windowSites W := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hj, hi⟩ := Finset.mem_product.mp hx
    have hj' := Finset.mem_range.mp hj
    obtain ⟨j', hj'ne, h1, h2⟩ := mem_windowSites.mp hi
    exact mem_windowSites.mpr ⟨j' + c x.1, hsupp _ hj' _ hj'ne, by omega, by omega⟩
  unfold FiniteConfiguration.localCount
  have hcard : k * ∑ i ∈ p.windowSites W, φ (p.window W i) =
      ∑ x ∈ Finset.range k ×ˢ p.windowSites W, φ (p.window W x.2) := by
    rw [Finset.sum_product]
    dsimp only
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hcard]
  calc ∑ x ∈ Finset.range k ×ˢ p.windowSites W, φ (p.window W x.2)
      = ∑ x ∈ Finset.range k ×ˢ p.windowSites W, φ (s.window W (x.2 + c x.1)) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        obtain ⟨hj, hi⟩ := Finset.mem_product.mp hx
        obtain ⟨hb1, hb2⟩ := hsite _ hi
        rw [hwin _ (Finset.mem_range.mp hj) _ hb1 hb2]
    _ = ∑ y ∈ (Finset.range k ×ˢ p.windowSites W).image (fun x : ℕ × ℤ => x.2 + c x.1),
          φ (s.window W y) := (Finset.sum_image (f := fun y => φ (s.window W y)) hinj).symm
    _ ≤ ∑ y ∈ s.windowSites W, φ (s.window W y) := Finset.sum_le_sum_of_subset hsub

/-! ## The exclusion -/

/-- **A count that one step never increases, and that `k` copies at a gap of at least `G₀` carry at
least `k` times, excludes reproduction of every pattern of positive count**
([RuleSpace] §5 Proposition 5.27(i) with the copies bound required from a gap `G₀` on): along the
orbit of `p` the count stays at most that of `p`, while at least `count p + 1` copies at the gap
`G₀` carry more. -/
theorem not_reproduces_of_count_mono_gap (U : FiniteConfiguration → FiniteConfiguration)
    (Φ : FiniteConfiguration → ℕ) (G₀ : ℕ) (hmono : ∀ s, Φ (U s) ≤ Φ s)
    (hcopies : ∀ p s k G, G₀ ≤ G → Copies p s k G → k * Φ p ≤ Φ s)
    {p : FiniteConfiguration} (hp : 1 ≤ Φ p) : ¬ Reproduces U p := by
  rintro ⟨_, h⟩
  obtain ⟨t, k, hk, hc⟩ := h (Φ p + 1) G₀
  have hit : ∀ t, Φ (U^[t] p) ≤ Φ p := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Function.iterate_succ_apply']; exact (hmono _).trans ih
  have h1 := hcopies p _ k G₀ le_rfl hc
  have h2 := hit t
  nlinarith

/-- **A rule with a potential certificate for a weight `φ` reproduces no pattern of positive local
count** ([RuleSpace] §5 Proposition 5.27(i) with the local count of `φ` as the count): the
certificate makes the count never increase in one step, copies at a gap of at least `W - 1` carry
it, and a pattern of positive count is not reproduced. -/
theorem LocalRule.PotentialCert.not_reproduces {f : LocalRule} {W : ℕ}
    {φ : (Fin W → ZMod 2) → ℕ} {π : (Fin (W + 1) → ZMod 2) → ℤ} (hq : f 0 0 0 = 0)
    (hφ : φ 0 = 0) (h : PotentialCert f φ π) {p : FiniteConfiguration}
    (hp : 1 ≤ p.localCount φ) : ¬ Reproduces (finRule f hq) p :=
  not_reproduces_of_count_mono_gap (finRule f hq) (fun s => s.localCount φ) (W - 1)
    (fun s => h.localCount_finRule_le hq hφ s)
    (fun _ _ _ _ hG hc => localCount_copies hc (by omega)) hp

/-! ## Helpers on states given by their set cells -/

/-- A state with cells `s x = if P x then 1 else 0` is set at `x` exactly when `P x` holds. -/
private theorem ne_zero_iff_of_cells {s : FiniteConfiguration} {P : ℤ → Prop} [DecidablePred P]
    (hs : ∀ x, s x = if P x then 1 else 0) (x : ℤ) : s x ≠ 0 ↔ P x := by
  rw [hs]
  by_cases h : P x <;> simp [h]

/-- The diameter of a state whose set cells lie between two set cells `a` and `b` is
`b - a + 1`. -/
private theorem diam_eq_of_ends {p : FiniteConfiguration} {a b : ℤ} (ha : p a ≠ 0) (hb : p b ≠ 0)
    (h : ∀ x, p x ≠ 0 → a ≤ x ∧ x ≤ b) : diam p = (b - a).toNat + 1 := by
  have hne : p.support.Nonempty := ⟨a, Finsupp.mem_support_iff.mpr ha⟩
  have hmin : p.support.min' hne = a := by
    refine le_antisymm (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr ha)) ?_
    exact (h _ (Finsupp.mem_support_iff.mp (Finset.min'_mem p.support hne))).1
  have hmax : p.support.max' hne = b := by
    refine le_antisymm ?_ (Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hb))
    exact (h _ (Finsupp.mem_support_iff.mp (Finset.max'_mem p.support hne))).2
  unfold diam
  rw [dite_eq_left hne, hmin, hmax]

/-- The translate of a single set cell is a single set cell. -/
private theorem translate_single_cell (a i : ℤ) :
    translate i (Finsupp.single a (1 : ZMod 2)) = Finsupp.single (a + i) 1 := by
  simp [FiniteConfiguration.translate, Finsupp.mapDomain_single]

/-- A single set cell has cells `if x = a then 1 else 0`. -/
private theorem single_cell_apply (a x : ℤ) :
    (Finsupp.single a (1 : ZMod 2)) x = if x = a then 1 else 0 := by
  by_cases h : x = a
  · subst h
    simp
  · simp [h]

/-! ## Two counts of width `9` at rule `22` -/

/-- **The count `phiA`**, a weight on ten windows of nine cells (cell `0` first), `0` elsewhere:
`110101000`, `101010100`, `010110100`, `010101010`, `110101010`, `001011010`, `101010001`,
`100010101`, `000101011` weigh `1` and `010101011` weighs `2`. -/
def phiA (u : Fin 9 → ZMod 2) : ℕ :=
  if u = ![1, 1, 0, 1, 0, 1, 0, 0, 0] then 1 else
  if u = ![1, 0, 1, 0, 1, 0, 1, 0, 0] then 1 else
  if u = ![0, 1, 0, 1, 1, 0, 1, 0, 0] then 1 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 0] then 1 else
  if u = ![1, 1, 0, 1, 0, 1, 0, 1, 0] then 1 else
  if u = ![0, 0, 1, 0, 1, 1, 0, 1, 0] then 1 else
  if u = ![1, 0, 1, 0, 1, 0, 0, 0, 1] then 1 else
  if u = ![1, 0, 0, 0, 1, 0, 1, 0, 1] then 1 else
  if u = ![0, 0, 0, 1, 0, 1, 0, 1, 1] then 1 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 1] then 2 else 0

/-- **The potential `piA`** of `phiA` at rule `22`, an integer weight on sixteen windows of ten
cells (cell `0` first), `0` elsewhere. -/
def piA (u : Fin 10 → ZMod 2) : ℤ :=
  if u = ![1, 1, 0, 1, 0, 1, 0, 0, 0, 0] then -1 else
  if u = ![0, 1, 0, 1, 1, 0, 1, 0, 0, 0] then -1 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 0, 0] then 1 else
  if u = ![1, 1, 0, 1, 0, 1, 0, 1, 0, 0] then 1 else
  if u = ![0, 0, 1, 0, 1, 1, 0, 1, 0, 0] then -1 else
  if u = ![1, 0, 1, 0, 1, 0, 0, 0, 1, 0] then -1 else
  if u = ![0, 1, 1, 0, 1, 0, 1, 0, 1, 0] then 1 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 1, 0] then -1 else
  if u = ![1, 1, 0, 1, 0, 1, 0, 0, 0, 1] then -1 else
  if u = ![0, 1, 0, 1, 1, 0, 1, 0, 0, 1] then -1 else
  if u = ![1, 1, 0, 0, 0, 1, 0, 1, 0, 1] then 1 else
  if u = ![0, 0, 1, 0, 1, 1, 0, 1, 0, 1] then -1 else
  if u = ![1, 0, 1, 0, 1, 0, 0, 0, 1, 1] then -1 else
  if u = ![1, 0, 0, 0, 1, 0, 1, 0, 1, 1] then 1 else
  if u = ![1, 0, 1, 0, 1, 0, 1, 0, 1, 1] then 1 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 1, 1] then -1 else 0

private theorem phiA_zero : phiA 0 = 0 := by decide

/-- **`piA` certifies `phiA` at rule `22`**, decided over the `2048` windows of eleven cells (the
two weights were found by a linear program outside the artifact). -/
theorem potentialCert_f22_phiA : PotentialCert f22 phiA piA := by
  unfold PotentialCert
  decide +kernel

/-- **The pattern `101101`**: the set cells `0`, `2`, `3` and `5`, of diameter `6`. -/
noncomputable def p101101 : FiniteConfiguration :=
  Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 5 1

private theorem p101101_apply (x : ℤ) :
    p101101 x = if x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 5 then 1 else 0 := by
  simp only [p101101, Finsupp.add_apply, single_cell_apply]
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h2 : x = 2
  · simp [h2]
  by_cases h3 : x = 3
  · simp [h3]
  by_cases h5 : x = 5
  · simp [h5]
  simp [h0, h2, h3, h5]

/-- **The count `phiA` of `101101` is `2`**: two windows weigh `1`, `001011010` from the cell `-2`
and `010110100` from the cell `-1`. -/
theorem localCount_phiA_p101101 : p101101.localCount phiA = 2 := by
  rw [localCount_of_cells phiA_zero p101101_apply (a := 0) (b := 5)
    (by intro x hx; omega)]
  decide +kernel

/-- **Rule `22` does not reproduce the pattern `101101`**: its count `phiA` is positive, and the
potential `piA` makes the count never increase. -/
theorem not_reproduces_f22_101101 : ¬ Reproduces (finRule f22 hq22) p101101 :=
  potentialCert_f22_phiA.not_reproduces hq22 phiA_zero
    (by rw [localCount_phiA_p101101]; norm_num)

/-- **The pattern `101101` reads `10101` nowhere**, so [RuleSpace] §5 Proposition 5.46 does not
reach it. -/
theorem p101101_not_reads_10101 : ∀ i, ¬ p101101.Reads [1, 0, 1, 0, 1] i := by
  intro i h
  rw [reads_five] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have e := ne_zero_iff_of_cells p101101_apply
  have a0 := (e i).mp (by rw [h0]; exact one_ne_zero)
  have a2 := (e (i + 2)).mp (by rw [h2]; exact one_ne_zero)
  have a4 := (e (i + 4)).mp (by rw [h4]; exact one_ne_zero)
  have a1 : ¬ (i + 1 = 0 ∨ i + 1 = 2 ∨ i + 1 = 3 ∨ i + 1 = 5) :=
    fun hh => (e (i + 1)).mpr hh h1
  have a3 : ¬ (i + 3 = 0 ∨ i + 3 = 2 ∨ i + 3 = 3 ∨ i + 3 = 5) :=
    fun hh => (e (i + 3)).mpr hh h3
  omega

/-- **The pattern `101101` has diameter `6`**, an even number. -/
theorem diam_p101101 : diam p101101 = 6 := by
  have e := ne_zero_iff_of_cells p101101_apply
  rw [diam_eq_of_ends (a := 0) (b := 5) ((e 0).mpr (by simp)) ((e 5).mpr (by simp))
    (fun x hx => by have := (e x).mp hx; omega)]
  rfl

/-- **The count `phiB`**, a weight on five windows of nine cells (cell `0` first), `0` elsewhere:
`101010000` and `010110010` weigh `3`, `010101010` weighs `2`, `110101010` weighs `1` and
`010101011` weighs `3`. -/
def phiB (u : Fin 9 → ZMod 2) : ℕ :=
  if u = ![1, 0, 1, 0, 1, 0, 0, 0, 0] then 3 else
  if u = ![0, 1, 0, 1, 1, 0, 0, 1, 0] then 3 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 0] then 2 else
  if u = ![1, 1, 0, 1, 0, 1, 0, 1, 0] then 1 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 1] then 3 else 0

/-- **The potential `piB`** of `phiB` at rule `22`, an integer weight on eleven windows of ten
cells (cell `0` first), `0` elsewhere. -/
def piB (u : Fin 10 → ZMod 2) : ℤ :=
  if u = ![1, 0, 1, 0, 1, 0, 0, 0, 0, 0] then -3 else
  if u = ![0, 1, 0, 1, 1, 0, 0, 1, 0, 0] then -3 else
  if u = ![1, 1, 0, 1, 0, 1, 0, 1, 0, 0] then -1 else
  if u = ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0] then -1 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 1, 0] then -3 else
  if u = ![1, 0, 1, 0, 1, 0, 0, 0, 0, 1] then -3 else
  if u = ![0, 1, 0, 1, 1, 0, 0, 1, 0, 1] then -3 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1] then -1 else
  if u = ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1] then -1 else
  if u = ![1, 0, 1, 0, 1, 0, 1, 0, 1, 1] then -1 else
  if u = ![0, 1, 0, 1, 0, 1, 0, 1, 1, 1] then -3 else 0

private theorem phiB_zero : phiB 0 = 0 := by decide

/-- **`piB` certifies `phiB` at rule `22`**, decided over the `2048` windows of eleven cells. -/
theorem potentialCert_f22_phiB : PotentialCert f22 phiB piB := by
  unfold PotentialCert
  decide +kernel

/-- **The pattern `1011001`**: the set cells `0`, `2`, `3` and `6`, of diameter `7`. -/
noncomputable def p1011001 : FiniteConfiguration :=
  Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 6 1

private theorem p1011001_apply (x : ℤ) :
    p1011001 x = if x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 6 then 1 else 0 := by
  simp only [p1011001, Finsupp.add_apply, single_cell_apply]
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h2 : x = 2
  · simp [h2]
  by_cases h3 : x = 3
  · simp [h3]
  by_cases h6 : x = 6
  · simp [h6]
  simp [h0, h2, h3, h6]

/-- **The count `phiB` of `1011001` is `3`**: one window weighs `3`, `010110010` from the cell
`-1`. -/
theorem localCount_phiB_p1011001 : p1011001.localCount phiB = 3 := by
  rw [localCount_of_cells phiB_zero p1011001_apply (a := 0) (b := 6)
    (by intro x hx; omega)]
  decide +kernel

/-- **Rule `22` does not reproduce the pattern `1011001`**: its count `phiB` is positive, and the
potential `piB` makes the count never increase. -/
theorem not_reproduces_f22_1011001 : ¬ Reproduces (finRule f22 hq22) p1011001 :=
  potentialCert_f22_phiB.not_reproduces hq22 phiB_zero
    (by rw [localCount_phiB_p1011001]; norm_num)

/-- **The pattern `1011001` reads `10101` nowhere**, so [RuleSpace] §5 Proposition 5.46 does not
reach it. -/
theorem p1011001_not_reads_10101 : ∀ i, ¬ p1011001.Reads [1, 0, 1, 0, 1] i := by
  intro i h
  rw [reads_five] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have e := ne_zero_iff_of_cells p1011001_apply
  have a0 := (e i).mp (by rw [h0]; exact one_ne_zero)
  have a2 := (e (i + 2)).mp (by rw [h2]; exact one_ne_zero)
  have a4 := (e (i + 4)).mp (by rw [h4]; exact one_ne_zero)
  have a1 : ¬ (i + 1 = 0 ∨ i + 1 = 2 ∨ i + 1 = 3 ∨ i + 1 = 6) :=
    fun hh => (e (i + 1)).mpr hh h1
  have a3 : ¬ (i + 3 = 0 ∨ i + 3 = 2 ∨ i + 3 = 3 ∨ i + 3 = 6) :=
    fun hh => (e (i + 3)).mpr hh h3
  omega

/-! ## The hypotheses are met at once, and the guards -/

/-- **The exclusion has a fixed instance meeting its hypotheses**: rule `22`, the count `phiA`
with its potential `piA`, and the pattern `101101` of positive count. -/
theorem LocalRule.PotentialCert.not_reproduces_nonvacuous :
    ∃ p : FiniteConfiguration, f22 0 0 0 = 0 ∧ phiA 0 = 0 ∧ PotentialCert f22 phiA piA ∧
      1 ≤ p.localCount phiA ∧ ¬ Reproduces (finRule f22 hq22) p :=
  ⟨p101101, hq22, phiA_zero, potentialCert_f22_phiA,
    by rw [localCount_phiA_p101101]; norm_num, not_reproduces_f22_101101⟩

/-- **The pattern `1001`**: the set cells `0` and `3`. -/
noncomputable def p1001 : FiniteConfiguration := Finsupp.single 0 1 + Finsupp.single 3 1

private theorem p1001_apply (x : ℤ) : p1001 x = if x = 0 ∨ x = 3 then 1 else 0 := by
  simp only [p1001, Finsupp.add_apply, single_cell_apply]
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h3 : x = 3
  · simp [h3]
  simp [h0, h3]

/-- One step of rule `90` on `1001` sets the cells `-1`, `1`, `2` and `4`. -/
private theorem finRule_f90_p1001_apply (x : ℤ) :
    finRule f90 hq90 p1001 x = if x = -1 ∨ x = 1 ∨ x = 2 ∨ x = 4 then 1 else 0 := by
  rw [finRule_apply, p1001_apply, p1001_apply, p1001_apply]
  simp only [f90]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **The certificate is load-bearing in the rule**: at rule `90` the pattern `1001` steps to
`101101`, so the count `phiA` rises from `0` to `2`, and no potential certifies `phiA` there. -/
theorem potentialCert_f22_phiA_load_bearing :
    (finRule f90 hq90 p1001).localCount phiA = 2 ∧ p1001.localCount phiA = 0 ∧
      ¬ ∃ π : (Fin 10 → ZMod 2) → ℤ, PotentialCert f90 phiA π := by
  have h2 : (finRule f90 hq90 p1001).localCount phiA = 2 := by
    rw [localCount_of_cells phiA_zero finRule_f90_p1001_apply (a := -1) (b := 4)
      (by intro x hx; omega)]
    decide +kernel
  have h0 : p1001.localCount phiA = 0 := by
    rw [localCount_of_cells phiA_zero p1001_apply (a := 0) (b := 3) (by intro x hx; omega)]
    decide +kernel
  refine ⟨h2, h0, ?_⟩
  rintro ⟨π, hπ⟩
  have := hπ.localCount_finRule_le hq90 phiA_zero p1001
  rw [h2, h0] at this
  omega

/-- **The count `phi2`**, a weight on the windows of two cells: `1` at the window `10`. -/
def phi2 (u : Fin 2 → ZMod 2) : ℕ := if u = ![1, 0] then 1 else 0

private theorem phi2_zero : phi2 0 = 0 := by decide

/-- **The gap hypothesis of `localCount_copies` cannot be dropped**: at width `2`, two copies of the
single set cell at gap `0` are the pair of adjacent cells, which carries one window `10` where two
are asked. -/
theorem localCount_copies_gap_load_bearing :
    Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (Finsupp.single 0 1 + Finsupp.single 1 1) 2 0 ∧
      FiniteConfiguration.localCount phi2 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = 1 ∧
      FiniteConfiguration.localCount phi2
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) = 1 := by
  refine ⟨⟨fun j => (j : ℤ), fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · have hd : diam (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = 1 := by simp [diam]
    rw [hd]
    push_cast
    omega
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, translate_single_cell]
    simp
  · rw [localCount_of_cells phi2_zero (P := fun x => x = 0) (single_cell_apply 0) (a := 0) (b := 0)
      (by intro x hx; omega)]
    decide +kernel
  · have hs : ∀ x : ℤ, (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 :
        FiniteConfiguration) x = if x = 0 ∨ x = 1 then 1 else 0 := by
      intro x
      simp only [Finsupp.add_apply, single_cell_apply]
      by_cases h0 : x = 0
      · simp [h0]
      by_cases h1 : x = 1
      · simp [h1]
      simp [h0, h1]
    rw [localCount_of_cells phi2_zero hs (a := 0) (b := 1) (by intro x hx; omega)]
    decide +kernel

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.localCount_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.localCount_eq_sum

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.PotentialCert.localCount_finRule_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.PotentialCert.localCount_finRule_le

/-- info: 'ECA.localCount_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.localCount_copies

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_of_count_mono_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_count_mono_gap

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.PotentialCert.not_reproduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.PotentialCert.not_reproduces

/-- info: 'ECA.potentialCert_f22_phiA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.potentialCert_f22_phiA

set_option linter.style.longLine false in
/-- info: 'ECA.localCount_phiA_p101101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.localCount_phiA_p101101

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_f22_101101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_f22_101101

set_option linter.style.longLine false in
/-- info: 'ECA.p101101_not_reads_10101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.p101101_not_reads_10101

/-- info: 'ECA.diam_p101101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.diam_p101101

/-- info: 'ECA.potentialCert_f22_phiB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.potentialCert_f22_phiB

set_option linter.style.longLine false in
/-- info: 'ECA.localCount_phiB_p1011001' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.localCount_phiB_p1011001

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_f22_1011001' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_f22_1011001

set_option linter.style.longLine false in
/-- info: 'ECA.p1011001_not_reads_10101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.p1011001_not_reads_10101

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.PotentialCert.not_reproduces_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.PotentialCert.not_reproduces_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.potentialCert_f22_phiA_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.potentialCert_f22_phiA_load_bearing

set_option linter.style.longLine false in
/-- info: 'ECA.localCount_copies_gap_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.localCount_copies_gap_load_bearing
