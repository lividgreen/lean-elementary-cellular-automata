module

public import ECA.Doubling
public import ECA.LightConeWidth
public import ECA.EndpointClasses
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card

/-!
# The three-cell dilation: rule `254` after rule `222`
([RuleSpace] §2 for the setting and the growing part, Proposition 2.13)

The dilation of a finite configuration, one step of rule `254`, reads a cell as `1` when it or a
neighbour is `1`. Rule `222` is the same union of three cells except that the pattern `101` gives
`0`. Five facts about the pair, all at radius one:

* the dilation after a step of rule `222` is the dilation after the dilation
  (`finRule_f254_finRule_f222`), a check over the `32` windows of five cells;
* the dilation is not injective (`not_injective_finRule_f254`), `101` and `111` having one dilation;
* the growing part of rule `222` under the support diameter is the nonzero states
  (`growingPart_f222_eq_ne_zero`), the pattern `001` and its mirror `100` giving `1`, so the
  endpoints move out one cell at each side;
* `n` steps of rule `254` take the light cone of the `n`-cell window to at most `(n + 1) ^ 2`
  states (`encard_image_iterate_f254_lightCone_le`), the solid block over the support's ends
  widened by `n`, and the zero state;
* the solid blocks of the window with holes at isolated even interior cells are at least
  `2 ^ ((n - 3) / 2)` states of the cone that no number of steps of rule `222` identifies
  (`exists_finset_injOn_iterate_f222`): `101` keeps its middle `0` while every other window of the
  block gives `1`, so the holes persist at every step as the ends move out.

## Main results

* `f222`, `f254` with `hq222`, `hq254` — the two rules, by Wolfram's bit convention
  (`wolframRule`), quiescent.
* `finRule_f254_finRule_f222` — the dilation after a step of rule `222` is the dilation after the
  dilation.
* `not_injective_finRule_f254` — the dilation is not injective.
* `growingPart_f222_eq_ne_zero` — at rule `222` with the support diameter, the growing part is the
  nonzero states.
* `encard_image_iterate_f254_lightCone_le` — the image of the `n`-cell window's cone under `n`
  steps of rule `254` has at most `(n + 1) ^ 2` states.
* `exists_finset_injOn_iterate_f222` — at least `2 ^ ((n - 3) / 2)` states of the `n`-cell window
  that every iterate of rule `222` is injective on.

## Scope

The pointwise characterization of the iterates of rule `254`
(`finRule_iterate_f254_apply_ne_zero_iff`) is private: a cell of the `k`-th iterate is nonzero
exactly when the state has a nonzero cell within `k` of it.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- Rule `222`: `a ∨ b ∨ c`, except that `101` gives `0`. -/
def f222 : LocalRule := wolframRule 222

/-- Rule `254`: `a ∨ b ∨ c`, the dilation of one step. -/
def f254 : LocalRule := wolframRule 254

/-- Rule `222` is quiescent. -/
theorem hq222 : f222 0 0 0 = 0 := by decide

/-- Rule `254` is quiescent. -/
theorem hq254 : f254 0 0 0 = 0 := by decide

/-- The indicator of a finite set of cells, as a finite configuration. -/
private noncomputable def ofFinset (S : Finset ℤ) : FiniteConfiguration :=
  Finsupp.indicator S fun _ _ => (1 : ZMod 2)

private theorem ofFinset_apply (S : Finset ℤ) (i : ℤ) :
    ofFinset S i = if i ∈ S then 1 else 0 := by
  unfold ofFinset
  rw [Finsupp.indicator_apply]
  simp

private theorem ofFinset_injective : Function.Injective ofFinset := by
  intro S T h
  ext i
  have := congrArg (fun x : FiniteConfiguration => x i) h
  simp only [ofFinset_apply] at this
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

private theorem ofFinset_eq_one {S : Finset ℤ} {i : ℤ} (h : i ∈ S) : ofFinset S i = 1 := by
  simp [ofFinset_apply, h]

private theorem ofFinset_eq_zero {S : Finset ℤ} {i : ℤ} (h : i ∉ S) : ofFinset S i = 0 := by
  simp [ofFinset_apply, h]

private theorem ofFinset_ne_zero_iff (S : Finset ℤ) (i : ℤ) : ofFinset S i ≠ 0 ↔ i ∈ S := by
  by_cases h : i ∈ S
  · simp [ofFinset_eq_one h, h]
  · simp [ofFinset_eq_zero h, h]

/-- Membership in a solid block with holes. -/
private theorem mem_blockHoles {a b i : ℤ} {H : Finset ℤ} :
    i ∈ Finset.Icc a b \ H ↔ a ≤ i ∧ i ≤ b ∧ i ∉ H := by
  rw [Finset.mem_sdiff, Finset.mem_Icc, and_assoc]

/-- A two-element field element is equal to another exactly when the two are zero together. -/
private theorem zmod_two_eq_iff : ∀ a b : ZMod 2, a = b ↔ (a ≠ 0 ↔ b ≠ 0) := by decide

/-! ## The dilation and its iterates -/

/-- **The dilation, cell by cell**: a cell is `1` when it or a neighbour is nonzero. -/
private theorem finRule_f254_apply (s : FiniteConfiguration) (i : ℤ) :
    LocalRule.finRule f254 hq254 s i =
      if s (i - 1) ≠ 0 ∨ s i ≠ 0 ∨ s (i + 1) ≠ 0 then 1 else 0 := by
  rw [finRule_apply]
  generalize s (i - 1) = a
  generalize s i = b
  generalize s (i + 1) = c
  revert a b c
  decide

private theorem finRule_f254_ne_zero_iff (s : FiniteConfiguration) (i : ℤ) :
    LocalRule.finRule f254 hq254 s i ≠ 0 ↔ s (i - 1) ≠ 0 ∨ s i ≠ 0 ∨ s (i + 1) ≠ 0 := by
  rw [finRule_f254_apply]
  split_ifs with h <;> simp [h]

/-- **`k` dilations**: a cell of the `k`-th iterate of rule `254` is nonzero exactly when the state
has a nonzero cell within `k` of it. -/
private theorem finRule_iterate_f254_apply_ne_zero_iff (k : ℕ) (s : FiniteConfiguration) (i : ℤ) :
    ((LocalRule.finRule f254 hq254)^[k] s) i ≠ 0 ↔
      ∃ j : ℤ, i - k ≤ j ∧ j ≤ i + k ∧ s j ≠ 0 := by
  induction k generalizing i with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero, add_zero]
      constructor
      · intro h
        exact ⟨i, le_rfl, le_rfl, h⟩
      · rintro ⟨j, h1, h2, h3⟩
        obtain rfl : j = i := by omega
        exact h3
  | succ k ih =>
      rw [Function.iterate_succ_apply', finRule_f254_ne_zero_iff, ih, ih, ih]
      push_cast
      constructor
      · rintro (⟨j, h1, h2, h3⟩ | ⟨j, h1, h2, h3⟩ | ⟨j, h1, h2, h3⟩)
        · exact ⟨j, by omega, by omega, h3⟩
        · exact ⟨j, by omega, by omega, h3⟩
        · exact ⟨j, by omega, by omega, h3⟩
      · rintro ⟨j, h1, h2, h3⟩
        rcases (by omega : (i - 1 - k ≤ j ∧ j ≤ i - 1 + k) ∨ (i - k ≤ j ∧ j ≤ i + k) ∨
            (i + 1 - k ≤ j ∧ j ≤ i + 1 + k)) with h | h | h
        · exact Or.inl ⟨j, h.1, h.2, h3⟩
        · exact Or.inr (Or.inl ⟨j, h.1, h.2, h3⟩)
        · exact Or.inr (Or.inr ⟨j, h.1, h.2, h3⟩)

/-! ## The dilation after a step of rule 222 -/

/-- **The dilation after a step of rule `222` is the dilation after the dilation** ([RuleSpace] §2):
both sides at a cell read the five cells around it, and the identity of the two values is a check
over the `32` windows. -/
theorem finRule_f254_finRule_f222 (s : FiniteConfiguration) :
    LocalRule.finRule f254 hq254 (LocalRule.finRule f222 hq222 s) =
      LocalRule.finRule f254 hq254 (LocalRule.finRule f254 hq254 s) := by
  have key : ∀ a b c d e : ZMod 2,
      f254 (f222 a b c) (f222 b c d) (f222 c d e) =
        f254 (f254 a b c) (f254 b c d) (f254 c d e) := by decide
  ext i
  simp only [finRule_apply, sub_add_cancel, add_sub_cancel_right]
  exact key _ _ _ _ _

/-- **The dilation is not injective** ([RuleSpace] §2): the states `101` and `111` have one
dilation. -/
theorem not_injective_finRule_f254 : ¬ Function.Injective (LocalRule.finRule f254 hq254) := by
  intro h
  have hne : ofFinset {0, 2} ≠ ofFinset {0, 1, 2} := by
    intro heq
    have := ofFinset_injective heq
    have h1 : (1 : ℤ) ∈ ({0, 1, 2} : Finset ℤ) := by decide
    rw [← this] at h1
    revert h1
    decide
  apply hne
  apply h
  ext i
  rw [zmod_two_eq_iff, finRule_f254_ne_zero_iff, finRule_f254_ne_zero_iff]
  simp only [ofFinset_ne_zero_iff, Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ## The growing part of rule 222 -/

/-- **The growing part of rule `222` under the support diameter is the nonzero states**
([RuleSpace] §2 Proposition 2.13(i) at rule `222`, whose endpoint moves are exact, one cell at each
side: `001` and `100` both give `1`). -/
theorem growingPart_f222_eq_ne_zero :
    Nonautonomous.GrowingPart (LocalRule.finRule f222 hq222) FiniteConfiguration.diam =
      {s | s ≠ 0} := by
  have h1 : f222 0 0 1 = 1 := by decide
  have h2 : f222 1 0 0 = 1 := by decide
  refine growingPart_eq_ne_zero (U := LocalRule.finRule f222 hq222)
    (fun {s} => ⟨fun h => ?_, fun h => ?_⟩)
    (fun {s} hne hne' => LocalRule.finRule_min'_of_leftTap (f := f222) (hq := hq222)
      h1 hne hne')
    (fun {s} hne hne' => LocalRule.finRule_max'_of_rightTap (f := f222) (hq := hq222)
      h2 hne hne')
  · by_contra hs
    exact LocalRule.finRule_ne_zero_of_leftTap (f := f222) (hq := hq222) h1 hs h
  · subst h
    ext i
    rw [LocalRule.finRule_apply]
    simpa using hq222

/-! ## The image of the light cone under the dilation -/

/-- **After `n` dilations the cone of the `n`-cell window has at most `(n + 1) ^ 2` states**
([RuleSpace] §2 Definition 2.4's light cone): a nonzero state of the window, with its support's
ends at `m ≤ M`, goes to the solid block from `m - n` to `M + n`, so the image has at most one state
per pair of ends and the zero state. -/
theorem encard_image_iterate_f254_lightCone_le (n : ℕ) :
    ((LocalRule.finRule f254 hq254)^[n] '' lightCone n 0).encard ≤ (n + 1) ^ 2 := by
  let g : ℕ × ℕ → FiniteConfiguration := fun p =>
    ofFinset (Finset.Icc ((p.1 : ℤ) - n) ((p.2 : ℤ) + n))
  have hsub : ((LocalRule.finRule f254 hq254)^[n] '' lightCone n 0) ⊆
      insert 0 (g '' ↑(Finset.range n ×ˢ Finset.range n)) := by
    rintro _ ⟨s, hs, rfl⟩
    by_cases h0 : s = 0
    · left
      subst h0
      ext i
      rw [zmod_two_eq_iff, finRule_iterate_f254_apply_ne_zero_iff]
      simp
    · right
      have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr h0
      have hm := hs _ (Finset.min'_mem _ hne)
      have hM := hs _ (Finset.max'_mem _ hne)
      have hmM : s.support.min' hne ≤ s.support.max' hne := Finset.min'_le_max' _ hne
      refine ⟨((s.support.min' hne).toNat, (s.support.max' hne).toNat), ?_, ?_⟩
      · simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
        push_cast at hm hM
        omega
      · symm
        ext i
        simp only [g]
        rw [zmod_two_eq_iff, finRule_iterate_f254_apply_ne_zero_iff, ofFinset_ne_zero_iff]
        push_cast at hm hM ⊢
        rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
        simp only [Finset.mem_Icc]
        constructor
        · rintro ⟨j, h1, h2, h3⟩
          have hj1 := Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr h3)
          have hj2 := Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr h3)
          omega
        · intro h
          by_cases hc : i ≤ s.support.min' hne + n
          · exact ⟨s.support.min' hne, by omega, by omega,
              Finsupp.mem_support_iff.mp (Finset.min'_mem _ hne)⟩
          · exact ⟨s.support.max' hne, by omega, by omega,
              Finsupp.mem_support_iff.mp (Finset.max'_mem _ hne)⟩
  calc ((LocalRule.finRule f254 hq254)^[n] '' lightCone n 0).encard
      ≤ (insert 0 (g '' ↑(Finset.range n ×ˢ Finset.range n))).encard := Set.encard_le_encard hsub
    _ ≤ (g '' ↑(Finset.range n ×ˢ Finset.range n)).encard + 1 := Set.encard_insert_le _ _
    _ ≤ ((Finset.range n ×ˢ Finset.range n : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).encard + 1 := by
        gcongr
        exact Set.encard_image_le _ _
    _ = ((n * n : ℕ) : ℕ∞) + 1 := by
        rw [Set.encard_coe_eq_coe_finsetCard]
        simp
    _ ≤ (n + 1) ^ 2 := by
        have : n * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
        exact_mod_cast this

/-! ## Holes that persist under rule 222 -/

/-- **One step of rule `222` on a solid block with isolated holes**: the block widens by one cell at
each side and the holes stay, since `101` gives `0` and every other window of a block gives `1`. -/
private theorem finRule_f222_blockHoles (lo hi : ℤ) (H : Finset ℤ) (hlh : lo ≤ hi)
    (hH : ∀ p ∈ H, lo < p ∧ p < hi ∧ p - 1 ∉ H ∧ p + 1 ∉ H) :
    LocalRule.finRule f222 hq222 (ofFinset (Finset.Icc lo hi \ H)) =
      ofFinset (Finset.Icc (lo - 1) (hi + 1) \ H) := by
  have hlo : lo ∉ H := fun h => by have := (hH lo h).1; omega
  have hhi : hi ∉ H := fun h => by have := (hH hi h).2.1; omega
  ext i
  rw [finRule_apply]
  by_cases hi0 : i ∈ H
  · obtain ⟨h1, h2, h3, h4⟩ := hH i hi0
    rw [ofFinset_eq_one (mem_blockHoles.mpr ⟨by omega, by omega, h3⟩),
      ofFinset_eq_zero (fun h => (mem_blockHoles.mp h).2.2 hi0),
      ofFinset_eq_one (mem_blockHoles.mpr ⟨by omega, by omega, h4⟩),
      ofFinset_eq_zero (fun h => (mem_blockHoles.mp h).2.2 hi0)]
    decide
  · by_cases hin : lo ≤ i ∧ i ≤ hi
    · rw [ofFinset_eq_one (mem_blockHoles.mpr ⟨hin.1, hin.2, hi0⟩),
        ofFinset_eq_one (mem_blockHoles.mpr ⟨by omega, by omega, hi0⟩)]
      have : ∀ a c : ZMod 2, f222 a 1 c = 1 := by decide
      exact this _ _
    · have hz : ofFinset (Finset.Icc lo hi \ H) i = 0 :=
        ofFinset_eq_zero (fun h => hin ⟨(mem_blockHoles.mp h).1, (mem_blockHoles.mp h).2.1⟩)
      rw [hz]
      by_cases hl : i = lo - 1
      · subst hl
        rw [ofFinset_eq_zero (fun h => by have := (mem_blockHoles.mp h).1; omega),
          ofFinset_eq_one (mem_blockHoles.mpr ⟨by omega, by omega, by simpa using hlo⟩),
          ofFinset_eq_one (mem_blockHoles.mpr ⟨by omega, by omega, hi0⟩)]
        decide
      · by_cases hr : i = hi + 1
        · subst hr
          rw [ofFinset_eq_one (mem_blockHoles.mpr ⟨by omega, by omega, by simpa using hhi⟩),
            ofFinset_eq_zero (fun h => by have := (mem_blockHoles.mp h).2.1; omega),
            ofFinset_eq_one (mem_blockHoles.mpr ⟨by omega, by omega, hi0⟩)]
          decide
        · rw [ofFinset_eq_zero (fun h => by
              have := (mem_blockHoles.mp h).1
              have := (mem_blockHoles.mp h).2.1
              omega),
            ofFinset_eq_zero (fun h => by
              have := (mem_blockHoles.mp h).1
              have := (mem_blockHoles.mp h).2.1
              omega),
            ofFinset_eq_zero (fun h => by
              have := (mem_blockHoles.mp h).1
              have := (mem_blockHoles.mp h).2.1
              omega)]
          decide

/-- **`k` steps of rule `222` on a solid block with isolated holes** widen the block by `k` cells at
each side and keep the holes. -/
private theorem finRule_iterate_f222_blockHoles (lo hi : ℤ) (H : Finset ℤ) (hlh : lo ≤ hi)
    (hH : ∀ p ∈ H, lo < p ∧ p < hi ∧ p - 1 ∉ H ∧ p + 1 ∉ H) (k : ℕ) :
    (LocalRule.finRule f222 hq222)^[k] (ofFinset (Finset.Icc lo hi \ H)) =
      ofFinset (Finset.Icc (lo - k) (hi + k) \ H) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih,
        finRule_f222_blockHoles (lo - k) (hi + k) H (by omega)
          (fun p hp => by
            obtain ⟨h1, h2, h3, h4⟩ := hH p hp
            exact ⟨by omega, by omega, h3, h4⟩)]
      push_cast
      rw [show lo - ((k : ℤ) + 1) = lo - k - 1 by ring,
        show hi + ((k : ℤ) + 1) = hi + k + 1 by ring]

/-- **At least `2 ^ ((n - 3) / 2)` states of the `n`-cell window that no iterate of rule `222`
identifies** ([RuleSpace] §2): the solid blocks of the window with holes at chosen even interior
cells. `101` keeps its middle `0` and the windows `110`, `011` and `111` give `1`, so the holes
persist at every step while the ends move out, and two blocks with different holes never meet. -/
theorem exists_finset_injOn_iterate_f222 (n : ℕ) :
    ∃ S : Finset FiniteConfiguration, (∀ s ∈ S, s ∈ lightCone n 0) ∧
      2 ^ ((n - 3) / 2) ≤ S.card ∧
        ∀ k, Set.InjOn ((LocalRule.finRule f222 hq222)^[k]) S := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨{0}, ?_, by simp, fun k => ?_⟩
    · intro s hs i hi
      rw [Finset.mem_singleton] at hs
      subst hs
      simp at hi
    · simp
  set j := (n - 3) / 2 with hj
  let Q : Finset ℤ := (Finset.Icc 1 j).image (fun q : ℕ => 2 * (q : ℤ))
  have hQ : ∀ p ∈ Q, ∃ q : ℕ, 1 ≤ q ∧ q ≤ j ∧ p = 2 * (q : ℤ) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_Icc] at hq
    exact ⟨q, hq.1, hq.2, rfl⟩
  have hQrange : ∀ p ∈ Q, 2 ≤ p ∧ p + 3 ≤ n := by
    intro p hp
    obtain ⟨q, h1, h2, rfl⟩ := hQ p hp
    omega
  have hQcard : Q.card = j := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    simp
  have hHyp : ∀ H ∈ Q.powerset, ∀ p ∈ H, (0 : ℤ) < p ∧ p < (n : ℤ) - 1 ∧ p - 1 ∉ H ∧ p + 1 ∉ H := by
    intro H hH p hp
    have hpQ := hQ p (Finset.mem_powerset.mp hH hp)
    obtain ⟨q, h1, h2, rfl⟩ := hpQ
    refine ⟨by omega, by omega, fun h => ?_, fun h => ?_⟩
    · obtain ⟨q', -, -, h'⟩ := hQ _ (Finset.mem_powerset.mp hH h)
      omega
    · obtain ⟨q', -, -, h'⟩ := hQ _ (Finset.mem_powerset.mp hH h)
      omega
  let cfg : Finset ℤ → FiniteConfiguration := fun H =>
    ofFinset (Finset.Icc (0 : ℤ) ((n : ℤ) - 1) \ H)
  have hinj : ∀ k : ℕ, ∀ H ∈ Q.powerset, ∀ H' ∈ Q.powerset,
      (LocalRule.finRule f222 hq222)^[k] (cfg H) = (LocalRule.finRule f222 hq222)^[k] (cfg H') →
        H = H' := by
    intro k H hH H' hH' h
    have e1 := finRule_iterate_f222_blockHoles 0 ((n : ℤ) - 1) H (by omega) (hHyp H hH) k
    have e2 := finRule_iterate_f222_blockHoles 0 ((n : ℤ) - 1) H' (by omega) (hHyp H' hH') k
    change _ = ofFinset _ at e1 e2
    have h' : ofFinset (Finset.Icc (0 - (k : ℤ)) ((n : ℤ) - 1 + k) \ H) =
        ofFinset (Finset.Icc (0 - (k : ℤ)) ((n : ℤ) - 1 + k) \ H') := by
      rw [← e1, ← e2]
      exact h
    have h'' := ofFinset_injective h'
    ext p
    constructor
    · intro hp
      by_contra hp'
      have hpQ := Finset.mem_powerset.mp hH hp
      have := hQrange p hpQ
      have hmem : p ∈ Finset.Icc (0 - (k : ℤ)) ((n : ℤ) - 1 + k) \ H' := by
        rw [Finset.mem_sdiff, Finset.mem_Icc]
        exact ⟨⟨by omega, by omega⟩, hp'⟩
      rw [← h''] at hmem
      exact (Finset.mem_sdiff.mp hmem).2 hp
    · intro hp
      by_contra hp'
      have hpQ := Finset.mem_powerset.mp hH' hp
      have := hQrange p hpQ
      have hmem : p ∈ Finset.Icc (0 - (k : ℤ)) ((n : ℤ) - 1 + k) \ H := by
        rw [Finset.mem_sdiff, Finset.mem_Icc]
        exact ⟨⟨by omega, by omega⟩, hp'⟩
      rw [h''] at hmem
      exact (Finset.mem_sdiff.mp hmem).2 hp
  refine ⟨Q.powerset.image cfg, ?_, ?_, ?_⟩
  · intro s hs i hi
    obtain ⟨H, -, rfl⟩ := Finset.mem_image.mp hs
    rw [Finsupp.mem_support_iff] at hi
    change ofFinset _ i ≠ 0 at hi
    rw [ofFinset_apply] at hi
    split_ifs at hi with h
    · rw [Finset.mem_sdiff, Finset.mem_Icc] at h
      constructor <;> omega
    · exact absurd rfl hi
  · rw [Finset.card_image_of_injOn (f := cfg) (fun H hH H' hH' h => hinj 0 H hH H' hH' h),
      Finset.card_powerset, hQcard]
  · intro k s hs s' hs' h
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hs)
    obtain ⟨H', hH', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hs')
    rw [hinj k H hH H' hH' h]

end ECA

/-! ## Axiom audit

Every theorem above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

/-- info: 'ECA.hq222' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.hq222

/-- info: 'ECA.hq254' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.hq254

/-- info: 'ECA.finRule_f254_finRule_f222' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f254_finRule_f222

/-- info: 'ECA.not_injective_finRule_f254' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_injective_finRule_f254

/-- info: 'ECA.growingPart_f222_eq_ne_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.growingPart_f222_eq_ne_zero

/-- info: 'ECA.encard_image_iterate_f254_lightCone_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.encard_image_iterate_f254_lightCone_le

/-- info: 'ECA.exists_finset_injOn_iterate_f222' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_finset_injOn_iterate_f222
