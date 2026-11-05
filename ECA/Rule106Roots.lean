module

public import ECA.Rule106Patterns
public import ECA.ReproducedPatterns
import all ECA.ReproductionBracket
import all ECA.Growth
import all ECA.EndpointClasses

/-!
# Rule `106` reproduces a state exactly when a state with no predecessor above it does
([RuleSpace] §5)

Rule `106` is one-to-one on finitely supported states ([RuleSpace] §3 Proposition 3.3), and
reproduction pulls back along an injective step (`Reproduces.of_finRule`). A state is never
wider than its image at rule `106` (`FiniteConfiguration.diam_le_diam_finRule_wolfram106`), since
the image's leftmost set cell sits one cell left of the state's and its rightmost at most one
cell left of the state's. So the backward chain of a nonzero state either stops at a state with
no predecessor or, being confined to the finitely many patterns of bounded width up to
translation, returns to a translate of itself, and a state periodic up to translation is never
reproduced (`Reproduces.not_of_iterate_eq_translate`).

## Main results

* `FiniteConfiguration.diam_le_diam_finRule_wolfram106` — a state is never wider than its image at
  rule `106`; with `finRule_wolfram106_leftEndpoint` and `finRule_wolfram106_rightEndpoint`, the
  two endpoint facts it rests on.
* `exists_notMem_range_or_iterate_eq_translate_wolfram106` — every nonzero state descends from a
  state with no predecessor, or is periodic up to translation.
* `reproduces_wolfram106_iff_root` — **the reduction**: a nonzero state is reproduced exactly when
  a state with no predecessor it descends from is.
* `Reproduces.of_finRule_nonvacuous` and `reproduces_wolfram106_iff_root_nonvacuous` — the
  statements at the pair `11`, which has no predecessor and is reproduced.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The rule at a cell, and its bridge to `f106` -/

private theorem wolframRule_106_eq : wolframRule 106 = f106 := by
  funext a b c
  revert a b c
  decide

private theorem finRule_wolfram106_eq (hq : wolframRule 106 0 0 0 = 0) (s : FiniteConfiguration) :
    finRule (wolframRule 106) hq s = finRule f106 hq106 s := by
  ext i
  rw [finRule_apply, finRule_apply, wolframRule_106_eq]

private theorem finRule_wolfram106_apply (hq : wolframRule 106 0 0 0 = 0) (s : FiniteConfiguration)
    (i : ℤ) : finRule (wolframRule 106) hq s i = s (i + 1) + s (i - 1) * s i := by
  rw [finRule_wolfram106_eq, finRule_apply]
  rfl

/-- **Rule `106` is one-to-one on finitely supported states**, in the form `Reproduces` is stated
at ([RuleSpace] §3 Proposition 3.3). -/
theorem finRule_wolfram106_injective (hq : wolframRule 106 0 0 0 = 0) :
    Function.Injective (finRule (wolframRule 106) hq) := by
  intro x y hxy
  apply finRule_f106_injective
  rwa [← finRule_wolfram106_eq hq, ← finRule_wolfram106_eq hq]

private theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-! ## A preimage is never wider -/

/-- **The left endpoint at rule `106`**: if the leftmost set cell of a state is `l`, the image is
clear left of `l - 1` and set at `l - 1` ([RuleSpace] §5). -/
theorem finRule_wolfram106_leftEndpoint (hq : wolframRule 106 0 0 0 = 0) {s : FiniteConfiguration}
    (hne : s.support.Nonempty) :
    finRule (wolframRule 106) hq s (s.support.min' hne - 1) ≠ 0 ∧
      ∀ y < s.support.min' hne - 1, finRule (wolframRule 106) hq s y = 0 := by
  refine ⟨?_, fun y hy => ?_⟩
  · rw [finRule_wolfram106_apply, below_min'_eq_zero hne (by omega : s.support.min' hne - 1 - 1 <
      s.support.min' hne), zero_mul, add_zero, sub_add_cancel]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem _ hne)
  · rw [finRule_wolfram106_apply, below_min'_eq_zero hne (by omega : y + 1 < s.support.min' hne),
      below_min'_eq_zero hne (by omega : y - 1 < s.support.min' hne), zero_mul, add_zero]

/-- **The right endpoint at rule `106`**: if the rightmost set cell of a state is `r`, the image is
set at `r - 1` or at `r`, so its rightmost set cell is at least `r - 1` ([RuleSpace] §5). -/
theorem finRule_wolfram106_rightEndpoint (hq : wolframRule 106 0 0 0 = 0)
    {s : FiniteConfiguration} (hne : s.support.Nonempty) :
    ∃ b, s.support.max' hne - 1 ≤ b ∧ finRule (wolframRule 106) hq s b ≠ 0 := by
  have hr : s (s.support.max' hne) ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hne)
  by_cases h1 : s (s.support.max' hne - 1) = 0
  · refine ⟨s.support.max' hne - 1, le_rfl, ?_⟩
    rw [finRule_wolfram106_apply, h1, mul_zero, add_zero, sub_add_cancel]
    exact hr
  · refine ⟨s.support.max' hne, by omega, ?_⟩
    rw [finRule_wolfram106_apply, above_max'_eq_zero hne (by omega : s.support.max' hne <
      s.support.max' hne + 1), zero_add]
    have e1 := zmod2_eq_one_of_ne_zero' _ h1
    have e2 := zmod2_eq_one_of_ne_zero' _ hr
    rw [e1, e2]
    decide

/-- **A state is never wider than its image at rule `106`**: the image's leftmost set cell is one
cell left of the state's and its rightmost at most one cell left of the state's
([RuleSpace] §5). -/
theorem FiniteConfiguration.diam_le_diam_finRule_wolfram106 (hq : wolframRule 106 0 0 0 = 0)
    (s : FiniteConfiguration) : diam s ≤ diam (finRule (wolframRule 106) hq s) := by
  by_cases hs : s = 0
  · subst hs
    rw [finRule_zero' _ hq]
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  obtain ⟨hA, -⟩ := finRule_wolfram106_leftEndpoint hq hne
  obtain ⟨b, hb1, hb⟩ := finRule_wolfram106_rightEndpoint hq hne
  have h := le_diam_of_cells hA hb
  rw [diam_eq' hne]
  have hlr := Finset.min'_le_max' s.support hne
  omega

/-! ## Every nonzero state descends from a root or is periodic -/

private theorem eq_of_support_eq {a b : FiniteConfiguration} (h : a.support = b.support) :
    a = b := by
  ext x
  by_cases hx : a x = 0
  · have : x ∉ b.support := by rw [← h]; simpa using hx
    have hb : b x = 0 := by
      by_contra hb
      exact this (Finsupp.mem_support_iff.mpr hb)
    rw [hx, hb]
  · have hb : b x ≠ 0 := by
      rw [← Finsupp.mem_support_iff, ← h]
      simpa using hx
    rw [zmod2_eq_one_of_ne_zero' _ hx, zmod2_eq_one_of_ne_zero' _ hb]

private theorem exists_root_or_periodic {U : FiniteConfiguration → FiniteConfiguration}
    (hcomm : ∀ (d : ℤ) (s : FiniteConfiguration),
      U (FiniteConfiguration.translate d s) = FiniteConfiguration.translate d (U s))
    (h0 : U 0 = 0) (hw : ∀ s, diam s ≤ diam (U s)) {p : FiniteConfiguration} (hp : p ≠ 0) :
    (∃ ρ n, ρ ∉ Set.range U ∧ U^[n] ρ = p) ∨
      ∃ m c, 0 < m ∧ U^[m] p = FiniteConfiguration.translate c p := by
  classical
  have hex : ∀ q : FiniteConfiguration, ∃ r, q ∈ Set.range U → U r = q := fun q => by
    by_cases h : q ∈ Set.range U
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨q, fun h' => absurd h' h⟩
  choose pre hpre using hex
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → FiniteConfiguration, g 0 = p ∧ ∀ n, g (n + 1) = pre (g n) :=
    ⟨fun n => pre^[n] p, rfl, fun n => Function.iterate_succ_apply' _ _ _⟩
  by_cases hroot : ∃ n, g n ∉ Set.range U
  · left
    have hn : g (Nat.find hroot) ∉ Set.range U := Nat.find_spec hroot
    have hmin : ∀ k < Nat.find hroot, g k ∈ Set.range U := fun k hk => by
      by_contra h
      exact Nat.find_min hroot hk h
    refine ⟨g (Nat.find hroot), Nat.find hroot, hn, ?_⟩
    have key : ∀ k, k ≤ Nat.find hroot → U^[k] (g k) = p := by
      intro k
      induction k with
      | zero => intro _; rw [Function.iterate_zero, id, hg0]
      | succ k ih =>
        intro hk
        rw [Function.iterate_succ_apply, hgs, hpre _ (hmin k (by omega))]
        exact ih (by omega)
    exact key _ le_rfl
  · right
    push Not at hroot
    have hstep : ∀ n, U (g (n + 1)) = g n := fun n => by
      rw [hgs]
      exact hpre _ (hroot n)
    have hiter : ∀ n, U^[n] (g n) = p := by
      intro n
      induction n with
      | zero => rw [Function.iterate_zero, id, hg0]
      | succ n ih => rw [Function.iterate_succ_apply, hstep]; exact ih
    have hiter2 : ∀ d k, U^[d] (g (k + d)) = g k := by
      intro d
      induction d with
      | zero => intro k; rfl
      | succ d ih =>
        intro k
        change U^[d + 1] (g ((k + d) + 1)) = g k
        rw [Function.iterate_succ_apply, hstep]
        exact ih k
    have hg_ne : ∀ n, g n ≠ 0 := by
      intro n h
      have := hiter n
      rw [h, Function.iterate_fixed h0] at this
      exact hp this.symm
    have hdiam : ∀ n, diam (g n) ≤ diam p := by
      intro n
      induction n with
      | zero => rw [hg0]
      | succ n ih =>
        have := hw (g (n + 1))
        rw [hstep] at this
        omega
    have hne : ∀ n, (g n).support.Nonempty := fun n =>
      Finsupp.support_nonempty_iff.mpr (hg_ne n)
    obtain ⟨lo, hlo⟩ : ∃ lo : ℕ → ℤ, ∀ n, lo n = (g n).support.min' (hne n) :=
      ⟨fun n => (g n).support.min' (hne n), fun _ => rfl⟩
    have hmem : ∀ n, (FiniteConfiguration.translate (-lo n) (g n)).support ∈
        (Finset.Icc (0 : ℤ) (diam p : ℤ)).powerset := by
      intro n
      rw [Finset.mem_powerset]
      intro x hx
      rw [FiniteConfiguration.translate_support, Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have h1 := Finset.min'_le _ y hy
      have h2 := Finset.le_max' _ y hy
      have h3 := diam_eq' (hne n)
      have h4 := hdiam n
      rw [Finset.mem_Icc]
      rw [hlo n]
      omega
    obtain ⟨i, j, hij, hsup⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨_, hmem n⟩ : ↥((Finset.Icc (0 : ℤ) (diam p : ℤ)).powerset)))
    have hsup' : (FiniteConfiguration.translate (-lo i) (g i)).support =
        (FiniteConfiguration.translate (-lo j) (g j)).support := congrArg Subtype.val hsup
    have key : ∀ i j : ℕ, i < j → (FiniteConfiguration.translate (-lo i) (g i)).support =
        (FiniteConfiguration.translate (-lo j) (g j)).support →
        ∃ m c, 0 < m ∧ U^[m] p = FiniteConfiguration.translate c p := by
      intro i j hij hs
      have heq := eq_of_support_eq hs
      have hgi : g i = FiniteConfiguration.translate (-lo j + lo i) (g j) := by
        have := congrArg (FiniteConfiguration.translate (lo i)) heq
        rw [FiniteConfiguration.translate_translate', FiniteConfiguration.translate_translate',
          neg_add_cancel, FiniteConfiguration.translate_zero'] at this
        exact this
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
      refine ⟨d + 1, -lo (i + d + 1) + lo i, Nat.succ_pos d, ?_⟩
      have h1 : U^[d + 1] (g (i + d + 1)) = g i := hiter2 (d + 1) i
      calc U^[d + 1] p = U^[d + 1] (U^[i + d + 1] (g (i + d + 1))) := by rw [hiter]
        _ = U^[i + d + 1] (U^[d + 1] (g (i + d + 1))) := by
          rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply]
        _ = U^[i + d + 1] (g i) := by rw [h1]
        _ = FiniteConfiguration.translate (-lo (i + d + 1) + lo i) p := by
          rw [hgi, iterate_translate' hcomm, hiter]
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h hsup'
    · exact key j i h hsup'.symm

/-- **Every nonzero state descends from a state with no predecessor, or is periodic up to
translation**: the backward chain of a nonzero state never widens, so it either stops at a state
with no predecessor or, among the finitely many patterns of bounded width up to translation,
returns to a translate of itself ([RuleSpace] §5). -/
theorem exists_notMem_range_or_iterate_eq_translate_wolfram106 (hq : wolframRule 106 0 0 0 = 0)
    {p : FiniteConfiguration} (hp : p ≠ 0) :
    (∃ ρ n, ρ ∉ Set.range (finRule (wolframRule 106) hq) ∧
        (finRule (wolframRule 106) hq)^[n] ρ = p) ∨
      ∃ m c, 0 < m ∧
        (finRule (wolframRule 106) hq)^[m] p = FiniteConfiguration.translate c p :=
  exists_root_or_periodic (U := finRule (wolframRule 106) hq)
    (fun d s => finRule_translate (wolframRule 106) hq d s) (finRule_zero' _ hq)
    (FiniteConfiguration.diam_le_diam_finRule_wolfram106 hq) hp

/-! ## The reduction -/

/-- **A nonzero state is reproduced at rule `106` exactly when a state with no predecessor it
descends from is**: a periodic state is never reproduced, and along the iterates of a root
reproduction passes both ways at the injective rule ([RuleSpace] §5). -/
theorem reproduces_wolfram106_iff_root (hq : wolframRule 106 0 0 0 = 0) {p : FiniteConfiguration}
    (hp : p ≠ 0) :
    Reproduces (finRule (wolframRule 106) hq) p ↔
      ∃ ρ n, ρ ∉ Set.range (finRule (wolframRule 106) hq) ∧
        (finRule (wolframRule 106) hq)^[n] ρ = p ∧ Reproduces (finRule (wolframRule 106) hq) ρ := by
  constructor
  · intro h
    rcases exists_notMem_range_or_iterate_eq_translate_wolfram106 hq hp with
      ⟨ρ, n, hρ, hn⟩ | ⟨m, c, hm, hmc⟩
    · refine ⟨ρ, n, hρ, hn, ?_⟩
      rw [← hn] at h
      exact (Reproduces.iterate_iff (wolframRule 106) hq (finRule_wolfram106_injective hq) n).mp h
    · exact absurd h (Reproduces.not_of_iterate_eq_translate (wolframRule 106) hq hm hmc)
  · rintro ⟨ρ, n, -, hn, hρ⟩
    rw [← hn]
    exact Reproduces.iterate (wolframRule 106) hq hρ n

/-! ## The statements are not vacuous -/

/-- The pullback statement has a fixed instance: rule `106` is one-to-one, the image of the pair
`11` is reproduced, and so is the pair. -/
theorem Reproduces.of_finRule_nonvacuous (hq : wolframRule 106 0 0 0 = 0) :
    Function.Injective (finRule (wolframRule 106) hq) ∧
      Reproduces (finRule (wolframRule 106) hq)
        (finRule (wolframRule 106) hq (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1)) ∧
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) := by
  have hinj := finRule_wolfram106_injective hq
  have himg := reproduces_wolfram106_orbit hq 1
  rw [Function.iterate_one] at himg
  exact ⟨hinj, himg, Reproduces.of_finRule (wolframRule 106) hq hinj himg⟩

/-- The reduction has a fixed instance: the pair `11` has no predecessor and is reproduced, so the
right side holds at its second iterate with the root the pair and the number of steps `2`, and so
does the left. -/
theorem reproduces_wolfram106_iff_root_nonvacuous (hq : wolframRule 106 0 0 0 = 0) :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∉
        Set.range (finRule (wolframRule 106) hq) ∧
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∧
      (finRule (wolframRule 106) hq)^[2]
          (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ≠ 0 ∧
      Reproduces (finRule (wolframRule 106) hq)
        ((finRule (wolframRule 106) hq)^[2]
          (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1)) ∧
      (∃ ρ n, ρ = (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∧ n = 2 ∧
        ρ ∉ Set.range (finRule (wolframRule 106) hq) ∧
        (finRule (wolframRule 106) hq)^[n] ρ =
          (finRule (wolframRule 106) hq)^[2]
            (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∧
        Reproduces (finRule (wolframRule 106) hq) ρ) := by
  have hroot : (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) ∉
      Set.range (finRule (wolframRule 106) hq) := by
    rintro ⟨x, hx⟩
    refine seedOneOne_notMem_range_f106 ⟨x, ?_⟩
    rw [← finRule_wolfram106_eq hq]
    exact hx
  have hrep := (Reproduces.of_finRule_nonvacuous hq).2.2
  have hrep2 := reproduces_wolfram106_orbit hq 2
  have hne := hrep2.1
  refine ⟨hroot, hrep, hne, hrep2, ⟨_, 2, rfl, rfl, hroot, rfl, hrep⟩⟩

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_wolfram106_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_wolfram106_injective

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_wolfram106_leftEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_wolfram106_leftEndpoint

set_option linter.style.longLine false in
/-- info: 'ECA.finRule_wolfram106_rightEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_wolfram106_rightEndpoint

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.diam_le_diam_finRule_wolfram106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.diam_le_diam_finRule_wolfram106

set_option linter.style.longLine false in
/-- info: 'ECA.exists_notMem_range_or_iterate_eq_translate_wolfram106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_notMem_range_or_iterate_eq_translate_wolfram106

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram106_iff_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram106_iff_root

set_option linter.style.longLine false in
/-- info: 'ECA.Reproduces.of_finRule_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.Reproduces.of_finRule_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram106_iff_root_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram106_iff_root_nonvacuous
