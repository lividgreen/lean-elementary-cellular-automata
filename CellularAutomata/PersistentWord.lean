/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.LocalMargin
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Int.Interval

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Two states erasing within `2` at every scale

It generalizes `LocalMargin.lineRule_eq_of_erasesWithin_two` from scale one
to every scale, at a class of radius-one tables. Registered as [RuleSpace] §6 Proposition 6.1,
row RS-10.

Three conditions are minted here and named for use in every docstring. A function of a state
**forces** a value at a cell from a finite set of cells (`Forces`): every state agreeing with a
given partial state on that set has that value there. A table **has a persistent word** when a
chain of non-empty partial states, the first on at most two cells, is carried each into the next by
one step of the table (`HasPersistentWord`, through `StepsInto`). A table is **permutive at the
left (right) end** when its output at every middle and right (left) input changes with the left
(right) input (`LeftPermutive`, `RightPermutive`). The words "erases within" are not used for any
of them: that condition is `LocalMargin.ErasesWithin`, and is the hypothesis of the parent.

## Main results

* `eq_const_of_erasesWithin_two_of_forces` — a translation-commuting update that forces a cell from
  at most two cells is constant, at every state erasing within `2`.
* `eq_of_erasesWithin_two_of_forces` — two states each erasing within `2` have the same successor.
* `eq_of_erasesWithin_two_of_forces_nonvacuous` — a fixed instance meeting every hypothesis at two
  different states.
* `eq_of_erasesWithin_two_of_forces_guard` — the guard: the two cells are load-bearing, at the
  majority of five cells forcing from three.
* `forces_iterate_of_hasPersistentWord` — a table with a persistent word forces a cell from at most
  two cells at every scale.
* `hasPersistentWord_majTable` and `hasPersistentWord_lonelyOne` — two tables with a persistent
  word, the majority and the table sending only `(0,0,1)` to `1`.
* `not_erasesWithin_one_of_leftPermutive` and `not_erasesWithin_one_of_rightPermutive` — a table
  permutive at an end erases within `1` at no state, at any scale.
* `leftPermutive_rule30` — Wolfram's rule 30 is permutive at the left end.
* `lineRule_iterate_eq_of_erasesWithin_two_of_forcing` — at every scale, two states each erasing
  within `2` have the same successor, at every table that has a persistent word or is permutive at
  an end.
* `lineRule_iterate_eq_of_erasesWithin_two_of_forcing_nonvacuous` — a fixed instance: the product
  table at scale `2`, at two different states.

## Scope

The parent is a sufficient condition on the table; which tables outside the class give the same
conclusion at some scale is not stated here. The witnesses name the table, the scale and the states
and are not existential in them. A persistent word is a chain of partial states, not of translates
of one word: each may sit anywhere, and none need repeat.
-/

@[expose] public section

namespace ForcingWord

open LocalMargin

/-! ## Definitions -/

/-- **Forces**: every state agreeing with `v` on `D` has `U`-value `c` at cell `i`. -/
def Forces (U : (ℤ → ZMod 2) → (ℤ → ZMod 2)) (D : Finset ℤ) (v : ℤ → ZMod 2) (i : ℤ)
    (c : ZMod 2) : Prop :=
  ∀ x : ℤ → ZMod 2, (∀ j ∈ D, x j = v j) → U x i = c

/-- **Steps into**: one step of the table carries every state agreeing with `v` on `D`
to a state agreeing with `v'` on `D'`. -/
def StepsInto (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (D : Finset ℤ) (v : ℤ → ZMod 2)
    (D' : Finset ℤ) (v' : ℤ → ZMod 2) : Prop :=
  ∀ x : ℤ → ZMod 2, (∀ j ∈ D, x j = v j) → ∀ j ∈ D', lineRule f x j = v' j

/-- **Has a persistent word**: a chain of partial states, the first on at most two cells, each
carried into the next by one step, none empty. -/
def HasPersistentWord (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  ∃ W : ℕ → Finset ℤ × (ℤ → ZMod 2), (W 0).1.card ≤ 2 ∧
    (∀ t, StepsInto f (W t).1 (W t).2 (W (t + 1)).1 (W (t + 1)).2) ∧ ∀ t, (W t).1.Nonempty

/-- **Permutive at the left end**: the output changes with the left input, at every middle and
right input. -/
def LeftPermutive (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop := ∀ b c, f 0 b c ≠ f 1 b c

/-- **Permutive at the right end**: the output changes with the right input, at every left and
middle input. -/
def RightPermutive (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop := ∀ a b, f a b 0 ≠ f a b 1

/-! ## Piece 1: the certificate lemma -/

/-- **A forced cell makes the update constant at a state erasing within `2`.** For a cell `m`,
change the state to agree with the translate of the forcing partial state around `m`, on the
translated set of at most two cells; the new state differs from the old at no more than two cells,
so the update does not move, and the forcing, carried across by translation, fixes the value at
`m`. -/
theorem eq_const_of_erasesWithin_two_of_forces (U : (ℤ → ZMod 2) → (ℤ → ZMod 2))
    (hU : ∀ (x : ℤ → ZMod 2) (k : ℤ), U (fun j => x (j + k)) = fun j => U x (j + k))
    (D : Finset ℤ) (v : ℤ → ZMod 2) (i : ℤ) (c : ZMod 2) (hD : D.card ≤ 2) (hF : Forces U D v i c)
    (x : ℤ → ZMod 2) (hx : ErasesWithin U x 2) : U x = fun _ => c := by
  classical
  funext m
  obtain ⟨x', hx'⟩ : ∃ x' : ℤ → ZMod 2,
      x' = fun j => if j - (m - i) ∈ D then v (j - (m - i)) else x j := ⟨_, rfl⟩
  have hD' : ∃ D' : Finset ℤ, D'.card ≤ 2 ∧ ∀ j, j ∉ D' → x' j = x j := by
    refine ⟨D.image (· + (m - i)), Finset.card_image_le.trans hD, fun j hj => ?_⟩
    have : j - (m - i) ∉ D := fun h =>
      hj (Finset.mem_image.mpr ⟨j - (m - i), h, by ring⟩)
    simp [hx', this]
  have h1 : U x' = U x := hx x' hD'
  have h2 := hF (fun j => x' (j + (m - i))) (fun j hj => by simp [hx', hj])
  rw [hU x' (m - i)] at h2
  have h3 : U x' m = c := by simpa using h2
  rw [← h1]
  exact h3

/-- **Two states erasing within `2` have the same successor**, for an update that forces a cell from
at most two cells and commutes with translation. -/
theorem eq_of_erasesWithin_two_of_forces (U : (ℤ → ZMod 2) → (ℤ → ZMod 2))
    (hU : ∀ (x : ℤ → ZMod 2) (k : ℤ), U (fun j => x (j + k)) = fun j => U x (j + k))
    (D : Finset ℤ) (v : ℤ → ZMod 2) (i : ℤ) (c : ZMod 2) (hD : D.card ≤ 2) (hF : Forces U D v i c)
    (x y : ℤ → ZMod 2) (hx : ErasesWithin U x 2) (hy : ErasesWithin U y 2) : U x = U y :=
  (eq_const_of_erasesWithin_two_of_forces U hU D v i c hD hF x hx).trans
    (eq_const_of_erasesWithin_two_of_forces U hU D v i c hD hF y hy).symm

/-- The iterate of the radius-one rule commutes with every translation. -/
theorem lineRule_iterate_shift (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (τ : ℕ)
    (x : ℤ → ZMod 2) (k : ℤ) :
    (lineRule f)^[τ] (fun j => x (j + k)) = fun j => (lineRule f)^[τ] x (j + k) := by
  induction τ with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext i
    change f _ _ _ = f _ _ _
    beta_reduce
    rw [show i - 1 + k = i + k - 1 by omega, show i + 1 + k = i + k + 1 by omega]

private theorem iter_two (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (x : ℤ → ZMod 2) :
    (lineRule f)^[2] x = lineRule f (lineRule f x) := rfl

private theorem prodTable_lineRule_eq_zero (x : ℤ → ZMod 2) (S : Finset ℤ) (hS : S.card ≤ 3)
    (hx : ∀ j, j ∉ S → x j = 0) :
    ∃ m : ℤ, ∀ j, j ≠ m → lineRule (fun a b c : ZMod 2 => a * b * c) x j = 0 := by
  by_cases hall : ∀ j, lineRule (fun a b c : ZMod 2 => a * b * c) x j = 0
  · exact ⟨0, fun j _ => hall j⟩
  push Not at hall
  obtain ⟨j, hj⟩ := hall
  have hmem : ∀ l, x l ≠ 0 → l ∈ S := fun l hl => by
    by_contra h; exact hl (hx l h)
  have h1 : ∀ a b c : ZMod 2, a * b * c ≠ 0 → a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by decide
  have hnz : ∀ l, lineRule (fun a b c : ZMod 2 => a * b * c) x l ≠ 0 →
      l - 1 ∈ S ∧ l ∈ S ∧ l + 1 ∈ S := fun l hl => by
    obtain ⟨ha, hb, hc⟩ := h1 _ _ _ hl
    exact ⟨hmem _ ha, hmem _ hb, hmem _ hc⟩
  obtain ⟨a1, a2, a3⟩ := hnz j hj
  have hsub : ({j - 1, j, j + 1} : Finset ℤ) ⊆ S := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> assumption
  have h3 : ({j - 1, j, j + 1} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  have hSeq : ({j - 1, j, j + 1} : Finset ℤ) = S :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨j, fun l hl => ?_⟩
  by_contra hne
  obtain ⟨b1, b2, b3⟩ := hnz l hne
  rw [← hSeq] at b1 b2 b3
  simp only [Finset.mem_insert, Finset.mem_singleton] at b1 b2 b3
  omega

private theorem prodTable_lineRule_eq_zero' (y : ℤ → ZMod 2) (m : ℤ)
    (hy : ∀ j, j ≠ m → y j = 0) :
    lineRule (fun a b c : ZMod 2 => a * b * c) y = fun _ => 0 := by
  funext l
  change y (l - 1) * y l * y (l + 1) = 0
  by_cases h : l = m
  · rw [hy (l - 1) (by omega)]; simp
  · rw [hy l h]; simp

private theorem prodTable_iterate_two_eq_zero (x : ℤ → ZMod 2) (S : Finset ℤ) (hS : S.card ≤ 3)
    (hx : ∀ j, j ∉ S → x j = 0) :
    (lineRule fun a b c : ZMod 2 => a * b * c)^[2] x = fun _ => 0 := by
  obtain ⟨m, hm⟩ := prodTable_lineRule_eq_zero x S hS hx
  have h1 := prodTable_lineRule_eq_zero' _ m hm
  rw [iter_two, h1]

private theorem erasesWithin_prod_two (c : ℤ → ZMod 2) (S₀ : Finset ℤ) (hS₀ : S₀.card ≤ 1)
    (hc : ∀ j, j ∉ S₀ → c j = 0) :
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2]) c 2 := by
  classical
  rintro x ⟨D, hD, hx⟩
  have hsub : ∀ j, j ∉ D ∪ S₀ → x j = 0 := fun j hj => by
    rw [Finset.mem_union, not_or] at hj
    rw [hx j hj.1, hc j hj.2]
  rw [prodTable_iterate_two_eq_zero x (D ∪ S₀) ((Finset.card_union_le _ _).trans (by omega)) hsub,
    prodTable_iterate_two_eq_zero c S₀ (by omega) hc]

/-- A fixed instance meeting every hypothesis of `eq_of_erasesWithin_two_of_forces` at two different
states: the product of three cells at scale `2`, the forcing set `{0}` with the zero partial state,
cell `0` and value `0`, the zero state and the state with cell `0` set. -/
theorem eq_of_erasesWithin_two_of_forces_nonvacuous :
    (∀ (x : ℤ → ZMod 2) (k : ℤ),
      (lineRule fun a b c : ZMod 2 => a * b * c)^[2] (fun j => x (j + k)) =
        fun j => (lineRule fun a b c : ZMod 2 => a * b * c)^[2] x (j + k)) ∧
    ({0} : Finset ℤ).card ≤ 2 ∧
    Forces ((lineRule fun a b c : ZMod 2 => a * b * c)^[2]) {0} (fun _ => 0) 0 0 ∧
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2]) (fun _ : ℤ => 0) 2 ∧
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2])
      (fun j : ℤ => if j = 0 then 1 else 0) 2 ∧
    (fun _ : ℤ => (0 : ZMod 2)) ≠ (fun j : ℤ => if j = 0 then 1 else 0) := by
  refine ⟨fun x k => lineRule_iterate_shift _ 2 x k, by simp, ?_,
    erasesWithin_prod_two _ ∅ (by simp) (fun _ _ => rfl),
    erasesWithin_prod_two _ {0} (by simp) (fun j hj => by simpa using hj), fun h => ?_⟩
  · intro x hx
    have h0 : x 0 = 0 := hx 0 (by simp)
    rw [iter_two]
    change (x (-1 - 1) * x (-1) * x (-1 + 1)) * (x (0 - 1) * x 0 * x (0 + 1)) *
      (x (1 - 1) * x 1 * x (1 + 1)) = 0
    rw [show (-1 : ℤ) + 1 = 0 by omega, show (1 : ℤ) - 1 = 0 by omega, h0]
    simp
  · have := congrFun h 0
    simp at this

/-- The five-cell majority of a state: at a cell, `1` when at least three of the five cells within
distance two are `1`, else `0`. It commutes with translation, and is the update of the guard. -/
def maj5Rule (x : ℤ → ZMod 2) : ℤ → ZMod 2 := fun i =>
  if 3 ≤ ((Finset.Icc (-2 : ℤ) 2).filter fun d => x (i + d) = 1).card then 1 else 0

private theorem card_icc_neg_two_two : (Finset.Icc (-2 : ℤ) 2).card = 5 := by decide

/-- **Guard: the two cells are load-bearing.** The majority of five cells commutes with
translation, forces a value at cell `0` from the three cells `{-1, 0, 1}` (the zero partial state,
value `0`), and both constant states erase within `2`, yet their successors differ. The forcing set
has three cells, so `eq_of_erasesWithin_two_of_forces` does not apply, and its conclusion fails. -/
theorem eq_of_erasesWithin_two_of_forces_guard :
    (∀ (x : ℤ → ZMod 2) (k : ℤ), maj5Rule (fun j => x (j + k)) = fun j => maj5Rule x (j + k)) ∧
    ({-1, 0, 1} : Finset ℤ).card = 3 ∧
    Forces maj5Rule {-1, 0, 1} (fun _ => 0) 0 0 ∧
    ErasesWithin maj5Rule (fun _ : ℤ => 0) 2 ∧ ErasesWithin maj5Rule (fun _ : ℤ => 1) 2 ∧
    maj5Rule (fun _ : ℤ => 0) ≠ maj5Rule (fun _ : ℤ => 1) := by
  classical
  refine ⟨fun x k => ?_, by decide, ?_, ?_, ?_, fun h => ?_⟩
  · funext i
    simp only [maj5Rule, add_right_comm]
  · intro x hx
    simp only [maj5Rule]
    refine ite_eq_right_iff.mpr fun hcon => ?_
    have hsub : ((Finset.Icc (-2 : ℤ) 2).filter fun d => x (0 + d) = 1) ⊆ {-2, 2} := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hne
      have hd' : d ∈ ({-1, 0, 1} : Finset ℤ) := by simp; omega
      have := hx d hd'
      have h01 : (0 : ZMod 2) = 1 := by
        have h2 := hd.2
        rw [zero_add, this] at h2
        exact h2
      exact absurd h01 (by decide)
    have := Finset.card_le_card hsub
    have h2 : ({-2, 2} : Finset ℤ).card ≤ 2 := Finset.card_le_two
    exact absurd hcon (by omega)
  · rintro x ⟨D, hD, hx⟩
    funext i
    simp only [maj5Rule]
    have hsub : ((Finset.Icc (-2 : ℤ) 2).filter fun d => x (i + d) = 1).card ≤ 2 := by
      refine (Finset.card_le_card_of_injOn (fun d => i + d) ?_ ?_).trans hD
      · intro d hd
        simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hd
        by_contra hne
        have h2 := hd.2
        rw [hx _ (by simpa using hne)] at h2
        have h3 : (0 : ZMod 2) = 1 := h2
        exact absurd h3 (by decide)
      · intro a _ b _ h; simpa using h
    have hc1 : ¬ 3 ≤ ((Finset.Icc (-2 : ℤ) 2).filter fun d => x (i + d) = 1).card := by omega
    have hc2 : ¬ 3 ≤ ((Finset.Icc (-2 : ℤ) 2).filter
        fun d => (fun _ : ℤ => (0 : ZMod 2)) (i + d) = 1).card := by
      simp
    simp only [hc1, hc2, ↓reduceIte]
  · rintro x ⟨D, hD, hx⟩
    funext i
    simp only [maj5Rule]
    have hsub : ((Finset.Icc (-2 : ℤ) 2).filter fun d => ¬ x (i + d) = 1).card ≤ 2 := by
      refine (Finset.card_le_card_of_injOn (fun d => i + d) ?_ ?_).trans hD
      · intro d hd
        simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hd
        by_contra hne
        have h2 := hd.2
        rw [hx _ (by simpa using hne)] at h2
        exact h2 rfl
      · intro a _ b _ h; simpa using h
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.Icc (-2 : ℤ) 2)
      (fun d => x (i + d) = 1)
    rw [card_icc_neg_two_two] at hsum
    have hc1 : 3 ≤ ((Finset.Icc (-2 : ℤ) 2).filter fun d => x (i + d) = 1).card := by omega
    simp only [hc1, ↓reduceIte]
    simp
  · have := congrFun h 0
    simp [maj5Rule] at this

/-! ## Piece 2: a persistent word forces a cell at every scale -/

private theorem iterate_agrees_of_hasPersistentWord (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (W : ℕ → Finset ℤ × (ℤ → ZMod 2))
    (hW : ∀ t, StepsInto f (W t).1 (W t).2 (W (t + 1)).1 (W (t + 1)).2) (τ : ℕ)
    (x : ℤ → ZMod 2) (hx : ∀ j ∈ (W 0).1, x j = (W 0).2 j) :
    ∀ j ∈ (W τ).1, (lineRule f)^[τ] x j = (W τ).2 j := by
  induction τ with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hW n _ ih

/-- **A persistent word forces a cell at every scale.** The first partial state of the word is on at
most two cells, and every state agreeing with it there agrees, after `τ` steps, with the `τ`-th
partial state, which is non-empty. -/
theorem forces_iterate_of_hasPersistentWord (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hf : HasPersistentWord f) (τ : ℕ) :
    ∃ (D : Finset ℤ) (v : ℤ → ZMod 2) (i : ℤ) (c : ZMod 2), D.card ≤ 2 ∧
      Forces ((lineRule f)^[τ]) D v i c := by
  obtain ⟨W, h0, hW, hne⟩ := hf
  obtain ⟨i, hi⟩ := hne τ
  exact ⟨(W 0).1, (W 0).2, i, (W τ).2 i, h0, fun x hx =>
    iterate_agrees_of_hasPersistentWord f W hW τ x hx i hi⟩

/-- The majority table has a persistent word: two adjacent zeros stay zero, at every step. -/
theorem hasPersistentWord_majTable : HasPersistentWord majTable := by
  refine ⟨fun _ => ({0, 1}, fun _ => 0), by decide, fun t x hx j hj => ?_, fun _ => ⟨0, by simp⟩⟩
  have h0 : x 0 = 0 := hx 0 (by simp)
  have h1 : x 1 = 0 := hx 1 (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · change majTable (x (0 - 1)) (x 0) (x (0 + 1)) = 0
    rw [zero_add, h0, h1]; simp [majTable]
  · change majTable (x (1 - 1)) (x 1) (x (1 + 1)) = 0
    rw [sub_self, h0, h1]; simp [majTable]

/-- The table sending only `(0,0,1)` to `1` has a persistent word: a single zero drifting left one
cell a step. -/
theorem hasPersistentWord_lonelyOne :
    HasPersistentWord (fun a b c : ZMod 2 => (1 - a) * (1 - b) * c) := by
  refine ⟨fun t => ({-(t : ℤ)}, fun _ => 0), by simp, fun t x hx j hj => ?_,
    fun t => ⟨-(t : ℤ), by simp⟩⟩
  simp only [Finset.mem_singleton] at hj
  have h0 : x (-(t : ℤ)) = 0 := hx _ (by simp)
  simp only [Finset.mem_singleton] at hx
  change (1 - x (j - 1)) * (1 - x j) * x (j + 1) = 0
  rw [hj, show -((t + 1 : ℕ) : ℤ) + 1 = -(t : ℤ) by push_cast; omega, h0]
  simp

/-! ## Piece 3: permutive at an end -/

private theorem iterate_congr (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (τ : ℕ) (i : ℤ)
    (x x' : ℤ → ZMod 2) (h : ∀ j : ℤ, i - (τ : ℤ) ≤ j → j ≤ i + (τ : ℤ) → x j = x' j) :
    (lineRule f)^[τ] x i = (lineRule f)^[τ] x' i := by
  induction τ generalizing i with
  | zero => simpa using h i (by simp) (by simp)
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change f _ _ _ = f _ _ _
    rw [ih (i - 1) (fun j hj1 hj2 => h j (by omega) (by omega)),
      ih i (fun j hj1 hj2 => h j (by omega) (by omega)),
      ih (i + 1) (fun j hj1 hj2 => h j (by omega) (by omega))]

private theorem zmod2_ne_cases : ∀ a a' : ZMod 2, a ≠ a' → (a = 0 ∧ a' = 1) ∨ (a = 1 ∧ a' = 0) := by
  decide

private theorem left_edge_ne (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hf : LeftPermutive f)
    (τ : ℕ) : ∀ (i : ℤ) (x x' : ℤ → ZMod 2),
    (∀ j, j ≠ i - (τ : ℤ) → i - (τ : ℤ) ≤ j → j ≤ i + (τ : ℤ) → x j = x' j) →
    x (i - (τ : ℤ)) ≠ x' (i - (τ : ℤ)) →
    (lineRule f)^[τ] x i ≠ (lineRule f)^[τ] x' i := by
  induction τ with
  | zero => intro i x x' _ h; simpa using h
  | succ k ih =>
    intro i x x' hag hne
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change f _ _ _ ≠ f _ _ _
    have e1 := ih (i - 1) x x' (fun j hj1 hj2 hj3 => hag j (by omega) (by omega) (by omega))
      (by rw [show i - 1 - (k : ℤ) = i - ((k + 1 : ℕ) : ℤ) by omega]; exact hne)
    have e2 : (lineRule f)^[k] x i = (lineRule f)^[k] x' i :=
      iterate_congr f k i x x' (fun j hj1 hj2 => hag j (by omega) (by omega) (by omega))
    have e3 : (lineRule f)^[k] x (i + 1) = (lineRule f)^[k] x' (i + 1) :=
      iterate_congr f k (i + 1) x x' (fun j hj1 hj2 => hag j (by omega) (by omega) (by omega))
    rw [e2, e3]
    intro h
    rcases zmod2_ne_cases _ _ e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at h; exact hf _ _ h
    · rw [h1, h2] at h; exact hf _ _ h.symm

private theorem right_edge_ne (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hf : RightPermutive f)
    (τ : ℕ) : ∀ (i : ℤ) (x x' : ℤ → ZMod 2),
    (∀ j, j ≠ i + (τ : ℤ) → i - (τ : ℤ) ≤ j → j ≤ i + (τ : ℤ) → x j = x' j) →
    x (i + (τ : ℤ)) ≠ x' (i + (τ : ℤ)) →
    (lineRule f)^[τ] x i ≠ (lineRule f)^[τ] x' i := by
  induction τ with
  | zero => intro i x x' _ h; simpa using h
  | succ k ih =>
    intro i x x' hag hne
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change f _ _ _ ≠ f _ _ _
    have e1 := ih (i + 1) x x' (fun j hj1 hj2 hj3 => hag j (by omega) (by omega) (by omega))
      (by rw [show i + 1 + (k : ℤ) = i + ((k + 1 : ℕ) : ℤ) by omega]; exact hne)
    have e2 : (lineRule f)^[k] x i = (lineRule f)^[k] x' i :=
      iterate_congr f k i x x' (fun j hj1 hj2 => hag j (by omega) (by omega) (by omega))
    have e3 : (lineRule f)^[k] x (i - 1) = (lineRule f)^[k] x' (i - 1) :=
      iterate_congr f k (i - 1) x x' (fun j hj1 hj2 => hag j (by omega) (by omega) (by omega))
    rw [e2, e3]
    intro h
    rcases zmod2_ne_cases _ _ e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at h; exact hf _ _ h
    · rw [h1, h2] at h; exact hf _ _ h.symm

private theorem zmod2_add_one_ne : ∀ a : ZMod 2, a + 1 ≠ a := by decide

/-- **A table permutive at the left end erases within `1` at no state, at any scale.** Changing the
cell `τ` places to the left of a cell changes its `τ`-step value, by induction on the left edge of
the light cone; at scale `0` the iterate is the identity. -/
theorem not_erasesWithin_one_of_leftPermutive (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hf : LeftPermutive f) (τ : ℕ) (x : ℤ → ZMod 2) :
    ¬ ErasesWithin ((lineRule f)^[τ]) x 1 := by
  intro hx
  have hD : ∃ D : Finset ℤ, D.card ≤ 1 ∧ ∀ j, j ∉ D →
      (fun j => if j = 0 - (τ : ℤ) then x j + 1 else x j) j = x j :=
    ⟨{0 - (τ : ℤ)}, by simp, fun j hj => by
      have : j ≠ 0 - (τ : ℤ) := by simpa using hj
      exact ite_eq_right_iff.mpr fun h => absurd h this⟩
  have heq := congrFun (hx _ hD) 0
  refine left_edge_ne f hf τ 0 x (fun j => if j = 0 - (τ : ℤ) then x j + 1 else x j)
    (fun j hj _ _ => (ite_eq_right_iff.mpr fun h => absurd h hj).symm) ?_ heq.symm
  simp only [ite_true]
  exact (zmod2_add_one_ne _).symm

/-- **A table permutive at the right end erases within `1` at no state, at any scale**, the mirror
image of `not_erasesWithin_one_of_leftPermutive`, through the right edge of the light cone. -/
theorem not_erasesWithin_one_of_rightPermutive (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hf : RightPermutive f) (τ : ℕ) (x : ℤ → ZMod 2) :
    ¬ ErasesWithin ((lineRule f)^[τ]) x 1 := by
  intro hx
  have hD : ∃ D : Finset ℤ, D.card ≤ 1 ∧ ∀ j, j ∉ D →
      (fun j => if j = 0 + (τ : ℤ) then x j + 1 else x j) j = x j :=
    ⟨{0 + (τ : ℤ)}, by simp, fun j hj => by
      have : j ≠ 0 + (τ : ℤ) := by simpa using hj
      exact ite_eq_right_iff.mpr fun h => absurd h this⟩
  have heq := congrFun (hx _ hD) 0
  refine right_edge_ne f hf τ 0 x (fun j => if j = 0 + (τ : ℤ) then x j + 1 else x j)
    (fun j hj _ _ => (ite_eq_right_iff.mpr fun h => absurd h hj).symm) ?_ heq.symm
  simp only [ite_true]
  exact (zmod2_add_one_ne _).symm

/-- Wolfram's rule 30, `a + b + c + b * c`, is permutive at the left end. -/
theorem leftPermutive_rule30 : LeftPermutive (fun a b c : ZMod 2 => a + b + c + b * c) := by
  intro b c
  revert b c
  decide

/-! ## The parent -/

/-- **At every scale, two states each erasing within `2` have the same successor**, at every table
that has a persistent word or is permutive at an end. With a persistent word, the iterate forces a
cell from at most two cells (`forces_iterate_of_hasPersistentWord`) and commutes with translation
(`lineRule_iterate_shift`), so `eq_of_erasesWithin_two_of_forces` applies; permutive at an end,
erasing within `2` implies erasing within `1`, which `not_erasesWithin_one_of_leftPermutive` and its
mirror refute. -/
theorem lineRule_iterate_eq_of_erasesWithin_two_of_forcing
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hf : HasPersistentWord f ∨ LeftPermutive f ∨ RightPermutive f) (τ : ℕ) (x y : ℤ → ZMod 2)
    (hx : ErasesWithin ((lineRule f)^[τ]) x 2) (hy : ErasesWithin ((lineRule f)^[τ]) y 2) :
    (lineRule f)^[τ] x = (lineRule f)^[τ] y := by
  have down : ErasesWithin ((lineRule f)^[τ]) x 1 := fun x' hx' =>
    hx x' (hx'.imp fun D hD => ⟨by omega, hD.2⟩)
  rcases hf with hW | hL | hR
  · obtain ⟨D, v, i, c, hD, hF⟩ := forces_iterate_of_hasPersistentWord f hW τ
    exact eq_of_erasesWithin_two_of_forces _ (fun x k => lineRule_iterate_shift f τ x k)
      D v i c hD hF x y hx hy
  · exact absurd down (not_erasesWithin_one_of_leftPermutive f hL τ x)
  · exact absurd down (not_erasesWithin_one_of_rightPermutive f hR τ x)

/-- A fixed instance meeting every hypothesis of the parent at two different states: the product
table has a persistent word, and at scale `2` the zero state and the state with cell `0` set both
erase within `2`. -/
theorem lineRule_iterate_eq_of_erasesWithin_two_of_forcing_nonvacuous :
    HasPersistentWord (fun a b c : ZMod 2 => a * b * c) ∧
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2]) (fun _ : ℤ => 0) 2 ∧
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2])
      (fun j : ℤ => if j = 0 then 1 else 0) 2 ∧
    (fun _ : ℤ => (0 : ZMod 2)) ≠ (fun j : ℤ => if j = 0 then 1 else 0) := by
  obtain ⟨-, -, -, h0, h1, hne⟩ := eq_of_erasesWithin_two_of_forces_nonvacuous
  refine ⟨?_, h0, h1, hne⟩
  refine ⟨fun _ => ({0}, fun _ => 0), by simp, fun t x hx j hj => ?_, fun _ => ⟨0, by simp⟩⟩
  simp only [Finset.mem_singleton] at hj hx
  subst hj
  have h0 : x 0 = 0 := hx 0 rfl
  change x (0 - 1) * x 0 * x (0 + 1) = 0
  rw [h0]; simp

end ForcingWord

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'ForcingWord.eq_const_of_erasesWithin_two_of_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.eq_const_of_erasesWithin_two_of_forces

/-- info: 'ForcingWord.eq_of_erasesWithin_two_of_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.eq_of_erasesWithin_two_of_forces

/-- info: 'ForcingWord.lineRule_iterate_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.lineRule_iterate_shift

/-- info: 'ForcingWord.eq_of_erasesWithin_two_of_forces_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.eq_of_erasesWithin_two_of_forces_nonvacuous

/-- info: 'ForcingWord.eq_of_erasesWithin_two_of_forces_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.eq_of_erasesWithin_two_of_forces_guard

/-- info: 'ForcingWord.forces_iterate_of_hasPersistentWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.forces_iterate_of_hasPersistentWord

/-- info: 'ForcingWord.hasPersistentWord_majTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.hasPersistentWord_majTable

/-- info: 'ForcingWord.hasPersistentWord_lonelyOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.hasPersistentWord_lonelyOne

/-- info: 'ForcingWord.not_erasesWithin_one_of_leftPermutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.not_erasesWithin_one_of_leftPermutive

/-- info: 'ForcingWord.not_erasesWithin_one_of_rightPermutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.not_erasesWithin_one_of_rightPermutive

/-- info: 'ForcingWord.leftPermutive_rule30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.leftPermutive_rule30

/-- info: 'ForcingWord.lineRule_iterate_eq_of_erasesWithin_two_of_forcing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.lineRule_iterate_eq_of_erasesWithin_two_of_forcing

/-- info: 'ForcingWord.lineRule_iterate_eq_of_erasesWithin_two_of_forcing_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingWord.lineRule_iterate_eq_of_erasesWithin_two_of_forcing_nonvacuous

