/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.PersistentWord
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The forcing class counted

Extends [RuleSpace] §6, Proposition 6.1 (row RS-10), whose class of tables — those that have a
persistent word or are permutive at an end — is a sufficient condition on the table that the
proposition does not enumerate. This module enumerates a decidable sub-class of the first half.

A **partial state** is a pair `(D, v)`: a finite set of known cells and the values there (the
values elsewhere are irrelevant). `stepWord f` is the three-valued step: a cell near the known set
is known after one step exactly when the table `f` is constant over every completion of the
unknown cells among its three neighbours. It is sound (`stepsInto_stepWord`), monotone in the known
set (`stepWord_mono`) and commutes with translation (`stepWord_translate`, an equality of partial
states). A word **returns** when some iterate of the step contains a translate of an earlier
iterate while no iterate up to it is empty; a return makes the iterate chain a persistent word
(`hasPersistentWord_of_return`). `ReturnsWithinTwo` is the bounded form of a return, decided over
the six words of `sixWords` at the first and second iterate and the shifts of at most two cells.

## Main results

* `stepsInto_stepWord`, `stepWord_mono`, `stepWord_translate` — soundness, monotonicity and
  translation-commutation of the step.
* `hasPersistentWord_of_return` — a return of the step implies a persistent word.
* `hasPersistentWord_of_return_nonvacuous` — a fixed instance meeting every hypothesis at once.
* `ReturnsWithinTwo`, `hasPersistentWord_of_returnsWithinTwo` — the decidable certificate and its
  soundness.
* `card_returnsWithinTwo`, `card_permutiveEnd`, `card_returnsWithinTwo_and_permutiveEnd`,
  `card_forcingClass` — over the `256` radius-one tables on two states, the certificate holds at
  `128`, permutivity at an end at `28`, both at `4`, and either at `152`.
* `lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass` — the parent's conclusion over the
  class of the certificate or permutivity at an end, with its `_nonvacuous` witness.

## Scope

The certificate is sufficient for a persistent word and not shown necessary: a table outside it may
have a persistent word that no one of the six words returns on within two steps. The three-valued
step is sound and not complete, so a table may force a cell that `stepWord` does not see. Nothing
here states which of the `104` tables outside the class give the parent's conclusion at some scale.
-/

@[expose] public section

namespace ForcingCount

open ForcingWord LocalMargin

/-! ## Definitions -/

/-- The known value of a partial state `(D, v)` at a cell, and `0` off the known set. -/
def fillAt (D : Finset ℤ) (v : ℤ → ZMod 2) (p : ℤ) : ZMod 2 := if p ∈ D then v p else 0

/-- **Forced**: the one-step value of the table `f` at cell `p` is the same at every triple of
neighbours agreeing with the partial state `(D, v)` on those of `p - 1`, `p`, `p + 1` that lie in
`D`; the common value is `f` at the triple filled with `0` off `D`. -/
def Forced (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (D : Finset ℤ) (v : ℤ → ZMod 2) (p : ℤ) :
    Prop :=
  ∀ a b c : ZMod 2, (p - 1 ∈ D → a = v (p - 1)) → (p ∈ D → b = v p) →
    (p + 1 ∈ D → c = v (p + 1)) →
    f a b c = f (fillAt D v (p - 1)) (fillAt D v p) (fillAt D v (p + 1))

instance (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (D : Finset ℤ) (v : ℤ → ZMod 2) (p : ℤ) :
    Decidable (Forced f D v p) := by unfold Forced; infer_instance

/-- **The three-valued step** on partial states: the cells of the known set and its two neighbours
at which the step is forced, with the forced value there and `0` elsewhere. -/
def stepWord (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (W : Finset ℤ × (ℤ → ZMod 2)) :
    Finset ℤ × (ℤ → ZMod 2) :=
  ((W.1 ∪ W.1.image (· + 1) ∪ W.1.image (· - 1)).filter (fun p => Forced f W.1 W.2 p),
   fun p => if Forced f W.1 W.2 p then
     f (fillAt W.1 W.2 (p - 1)) (fillAt W.1 W.2 p) (fillAt W.1 W.2 (p + 1)) else 0)

/-- The iterates of the three-valued step. -/
def iter (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (W : Finset ℤ × (ℤ → ZMod 2)) (t : ℕ) :
    Finset ℤ × (ℤ → ZMod 2) := (stepWord f)^[t] W

/-- **Contains**: `W'` extends the partial state `W`, with a larger known set and the same values
on the smaller one. -/
def Contains (W' W : Finset ℤ × (ℤ → ZMod 2)) : Prop :=
  W.1 ⊆ W'.1 ∧ ∀ j ∈ W.1, W'.2 j = W.2 j

instance (W' W : Finset ℤ × (ℤ → ZMod 2)) : Decidable (Contains W' W) := by
  unfold Contains; infer_instance

/-- Translation of a partial state by `s` cells. -/
def translateWord (s : ℤ) (W : Finset ℤ × (ℤ → ZMod 2)) : Finset ℤ × (ℤ → ZMod 2) :=
  (W.1.image (· + s), fun j => W.2 (j - s))

/-- **The six words** searched for a return: one known cell with either value, and two adjacent
known cells with each of the four assignments, the values elsewhere `0`. -/
def sixWords : List (Finset ℤ × (ℤ → ZMod 2)) :=
  [({0}, fun _ => 0), ({0}, fun j => if j = 0 then 1 else 0),
   ({0, 1}, fun _ => 0), ({0, 1}, fun j => if j = 1 then 1 else 0),
   ({0, 1}, fun j => if j = 0 then 1 else 0), ({0, 1}, fun j => if j = 0 ∨ j = 1 then 1 else 0)]

/-- **Returns within two**: some word of `sixWords` has non-empty iterates up to the first or
second one, and that iterate contains a translate of the word itself by at most two cells. -/
def ReturnsWithinTwo (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  ∃ W ∈ sixWords, ∃ t ∈ ({1, 2} : Finset ℕ), ∃ s ∈ Finset.Icc (-2 : ℤ) 2,
    (∀ t' ≤ t, (iter f W t').1.Nonempty) ∧ Contains (iter f W t) (translateWord s W)

instance (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Decidable (ReturnsWithinTwo f) :=
  inferInstanceAs (Decidable (∃ W ∈ sixWords, ∃ t ∈ ({1, 2} : Finset ℕ),
    ∃ s ∈ Finset.Icc (-2 : ℤ) 2,
    (∀ t' ≤ t, (iter f W t').1.Nonempty) ∧ Contains (iter f W t) (translateWord s W)))

instance : DecidablePred LeftPermutive := fun f =>
  inferInstanceAs (Decidable (∀ b c, f 0 b c ≠ f 1 b c))

instance : DecidablePred RightPermutive := fun f =>
  inferInstanceAs (Decidable (∀ a b, f a b 0 ≠ f a b 1))

/-! ## The three-valued step -/

/-- A cell lies in the image of a set under a shift exactly when its preimage lies in the set. -/
theorem mem_image_add_iff (D : Finset ℤ) (s q : ℤ) : q ∈ D.image (· + s) ↔ q - s ∈ D := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨q - s, h, by ring⟩

/-- A cell lies in the image of a set under the shift by `-1` exactly when its successor lies in the
set. -/
theorem mem_image_sub_one_iff (D : Finset ℤ) (q : ℤ) : q ∈ D.image (· - 1) ↔ q + 1 ∈ D := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨q + 1, h, by ring⟩

/-- On the known set the filled value is the stored value. -/
theorem fillAt_of_mem {D : Finset ℤ} {v : ℤ → ZMod 2} {p : ℤ} (h : p ∈ D) : fillAt D v p = v p := by
  simp [fillAt, h]

/-- Membership in the known set of the step: a cell near the known set at which the step is
forced. -/
theorem stepWord_fst_mem (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (W : Finset ℤ × (ℤ → ZMod 2))
    (p : ℤ) : p ∈ (stepWord f W).1 ↔
      (p ∈ W.1 ∨ p - 1 ∈ W.1 ∨ p + 1 ∈ W.1) ∧ Forced f W.1 W.2 p := by
  simp only [stepWord, Finset.mem_filter, Finset.mem_union, mem_image_add_iff,
    mem_image_sub_one_iff]
  tauto

/-- The value function of the step. -/
theorem stepWord_snd (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (W : Finset ℤ × (ℤ → ZMod 2))
    (p : ℤ) : (stepWord f W).2 p = if Forced f W.1 W.2 p then
     f (fillAt W.1 W.2 (p - 1)) (fillAt W.1 W.2 p) (fillAt W.1 W.2 (p + 1)) else 0 := rfl

/-- **Soundness**: one step of the table carries every state agreeing with a partial state to a
state agreeing with its three-valued step. -/
theorem stepsInto_stepWord (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (D : Finset ℤ)
    (v : ℤ → ZMod 2) :
    StepsInto f D v (stepWord f (D, v)).1 (stepWord f (D, v)).2 := by
  intro x hx j hj
  rw [stepWord_fst_mem] at hj
  rw [stepWord_snd]
  simp only [hj.2, ↓reduceIte]
  exact hj.2 (x (j - 1)) (x j) (x (j + 1)) (fun h => hx _ h) (fun h => hx _ h)
    (fun h => hx _ h)

/-- A forced value is the value at the filled triple of any larger partial state. -/
theorem forced_value_eq {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {W W' : Finset ℤ × (ℤ → ZMod 2)}
    (hC : Contains W' W) {p : ℤ} (hF : Forced f W.1 W.2 p) :
    f (fillAt W'.1 W'.2 (p - 1)) (fillAt W'.1 W'.2 p) (fillAt W'.1 W'.2 (p + 1)) =
      f (fillAt W.1 W.2 (p - 1)) (fillAt W.1 W.2 p) (fillAt W.1 W.2 (p + 1)) := by
  obtain ⟨hD, hv⟩ := hC
  have key : ∀ q, q ∈ W.1 → fillAt W'.1 W'.2 q = W.2 q := fun q hq => by
    rw [fillAt_of_mem (hD hq), hv q hq]
  exact hF _ _ _ (fun h => key _ h) (fun h => key _ h) (fun h => key _ h)

/-- Forcing persists under extension of the partial state. -/
theorem forced_mono {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {W W' : Finset ℤ × (ℤ → ZMod 2)}
    (hC : Contains W' W) {p : ℤ} (hF : Forced f W.1 W.2 p) : Forced f W'.1 W'.2 p := by
  have hE := forced_value_eq hC hF
  obtain ⟨hD, hv⟩ := hC
  intro a b c ha hb hc
  rw [hE]
  exact hF a b c (fun h => by rw [ha (hD h), hv _ h]) (fun h => by rw [hb (hD h), hv _ h])
    (fun h => by rw [hc (hD h), hv _ h])

/-- **Monotonicity**: the three-valued step of a larger partial state contains the step of the
smaller one. -/
theorem stepWord_mono (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) {W W' : Finset ℤ × (ℤ → ZMod 2)}
    (hC : Contains W' W) : Contains (stepWord f W') (stepWord f W) := by
  refine ⟨fun p hp => ?_, fun j hj => ?_⟩
  · rw [stepWord_fst_mem] at hp ⊢
    exact ⟨by rcases hp.1 with h | h | h
              exacts [Or.inl (hC.1 h), Or.inr (Or.inl (hC.1 h)), Or.inr (Or.inr (hC.1 h))],
      forced_mono hC hp.2⟩
  · rw [stepWord_fst_mem] at hj
    rw [stepWord_snd, stepWord_snd]
    simp only [hj.2, forced_mono hC hj.2, ↓reduceIte, forced_value_eq hC hj.2]

/-- Filling commutes with translation. -/
theorem fillAt_translate (D : Finset ℤ) (v : ℤ → ZMod 2) (s q : ℤ) :
    fillAt (D.image (· + s)) (fun j => v (j - s)) q = fillAt D v (q - s) := by
  simp only [fillAt, mem_image_add_iff]

/-- Forcing commutes with translation. -/
theorem forced_translate (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (D : Finset ℤ)
    (v : ℤ → ZMod 2) (s p : ℤ) :
    Forced f (D.image (· + s)) (fun j => v (j - s)) p ↔ Forced f D v (p - s) := by
  have e1 : p - 1 - s = p - s - 1 := by ring
  have e2 : p + 1 - s = p - s + 1 := by ring
  simp only [Forced, fillAt_translate, mem_image_add_iff, e1, e2]

/-- **Translation-commutation**: the step of a translate is the translate of the step, as partial
states (equal known sets and equal value functions). -/
theorem stepWord_translate (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (s : ℤ)
    (W : Finset ℤ × (ℤ → ZMod 2)) :
    stepWord f (translateWord s W) = translateWord s (stepWord f W) := by
  have e1 : ∀ p : ℤ, p - 1 - s = p - s - 1 := fun p => by ring
  have e2 : ∀ p : ℤ, p + 1 - s = p - s + 1 := fun p => by ring
  refine Prod.ext (Finset.ext fun p => ?_) (funext fun p => ?_)
  · simp only [translateWord, stepWord_fst_mem, mem_image_add_iff, forced_translate, e1, e2]
  · simp only [translateWord, stepWord_snd, forced_translate, fillAt_translate, e1, e2]

/-! ## The return lemma -/

/-- The iterate chain advances by one step. -/
theorem iter_succ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (W : Finset ℤ × (ℤ → ZMod 2)) (t : ℕ) :
    iter f W (t + 1) = stepWord f (iter f W t) :=
  Function.iterate_succ_apply' (stepWord f) t W

/-- A return propagates: the containment of a translate persists at every later pair of iterates. -/
theorem contains_translate_iter (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (W : Finset ℤ × (ℤ → ZMod 2)) (t₁ t₂ : ℕ) (s : ℤ)
    (hret : Contains (iter f W t₂) (translateWord s (iter f W t₁))) (k : ℕ) :
    Contains (iter f W (t₂ + k)) (translateWord s (iter f W (t₁ + k))) := by
  induction k with
  | zero => exact hret
  | succ k ih =>
    rw [← Nat.add_assoc, ← Nat.add_assoc, iter_succ, iter_succ, ← stepWord_translate]
    exact stepWord_mono f ih

/-- **A return of the three-valued step gives a persistent word.** If the iterates of a word on at
most two cells are non-empty up to a later one, and that later one contains a translate of an
earlier one, then the table has a persistent word. -/
theorem hasPersistentWord_of_return (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (W : Finset ℤ × (ℤ → ZMod 2)) (hW : W.1.card ≤ 2) (t₁ t₂ : ℕ) (hlt : t₁ < t₂)
    (hne : ∀ t ≤ t₂, (iter f W t).1.Nonempty) (s : ℤ)
    (hret : Contains (iter f W t₂) (translateWord s (iter f W t₁))) : HasPersistentWord f := by
  have hn : ∀ t, (iter f W t).1.Nonempty := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases h : t ≤ t₂
      · exact hne t h
      · obtain ⟨k, rfl⟩ : ∃ k, t = t₂ + k := ⟨t - t₂, by omega⟩
        obtain ⟨x, hx⟩ := ih (t₁ + k) (by omega)
        exact ⟨x + s, (contains_translate_iter f W t₁ t₂ s hret k).1
          (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
  refine ⟨fun t => iter f W t, hW, fun t => ?_, hn⟩
  beta_reduce
  rw [iter_succ]
  exact stepsInto_stepWord f (iter f W t).1 (iter f W t).2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- the decided iterates of the step at a concrete table need more than the default heartbeats.
/-- **The return lemma's hypotheses are jointly satisfiable**: at the majority table, the word on
the two cells `0` and `1` valued `0`, at `t₁ = 0`, `t₂ = 1`, `s = 0`, every hypothesis holds and
the table has a persistent word. -/
theorem hasPersistentWord_of_return_nonvacuous :
    (({0, 1} : Finset ℤ), fun _ : ℤ => (0 : ZMod 2)).1.card ≤ 2 ∧ (0 : ℕ) < 1 ∧
    (∀ t ≤ 1, (iter majTable (({0, 1} : Finset ℤ), fun _ : ℤ => (0 : ZMod 2)) t).1.Nonempty) ∧
    Contains (iter majTable (({0, 1} : Finset ℤ), fun _ : ℤ => (0 : ZMod 2)) 1)
      (translateWord 0 (iter majTable (({0, 1} : Finset ℤ), fun _ : ℤ => (0 : ZMod 2)) 0)) ∧
    HasPersistentWord majTable := by
  have h1 : (({0, 1} : Finset ℤ), fun _ : ℤ => (0 : ZMod 2)).1.card ≤ 2 := by decide
  have h3 : ∀ t ≤ 1,
      (iter majTable (({0, 1} : Finset ℤ), fun _ : ℤ => (0 : ZMod 2)) t).1.Nonempty := by decide
  have h4 : Contains (iter majTable (({0, 1} : Finset ℤ), fun _ : ℤ => (0 : ZMod 2)) 1)
      (translateWord 0 (iter majTable (({0, 1} : Finset ℤ), fun _ : ℤ => (0 : ZMod 2)) 0)) := by
    decide
  exact ⟨h1, by decide, h3, h4, hasPersistentWord_of_return majTable _ h1 0 1 (by decide) h3 0 h4⟩

/-! ## The bounded certificate -/

/-- Every word of `sixWords` is on at most two cells. -/
theorem card_le_two_of_mem_sixWords : ∀ W ∈ sixWords, W.1.card ≤ 2 := by decide

/-- **The certificate is sound**: a table that returns within two has a persistent word. -/
theorem hasPersistentWord_of_returnsWithinTwo (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (h : ReturnsWithinTwo f) : HasPersistentWord f := by
  obtain ⟨W, hW, t, ht, s, -, hne, hc⟩ := h
  have ht' : 0 < t := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    omega
  exact hasPersistentWord_of_return f W (card_le_two_of_mem_sixWords W hW) 0 t ht' hne s hc

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see the return lemma's witness.
/-- The certificate holds at the majority table. -/
theorem returnsWithinTwo_majTable : ReturnsWithinTwo majTable := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see the return lemma's witness.
/-- The certificate fails at the table `a + c`, which is permutive at both ends. -/
theorem not_returnsWithinTwo_add_ends :
    ¬ ReturnsWithinTwo (fun a _ c : ZMod 2 => a + c) := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- the ambient type has 256 members; kernel reduction of the nested Pi-Fintype instance and of the
-- bounded search needs more than the defaults of both limits.
/-- **The certificate holds at `128` of the `256` tables.** -/
theorem card_returnsWithinTwo :
    Fintype.card {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 // ReturnsWithinTwo f} = 128 := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see card_returnsWithinTwo.
/-- **Permutivity at an end holds at `28` tables.** -/
theorem card_permutiveEnd :
    Fintype.card {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 //
      LeftPermutive f ∨ RightPermutive f} = 28 := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see card_returnsWithinTwo.
/-- **Both hold at `4` tables**: the two shifts and their complements. -/
theorem card_returnsWithinTwo_and_permutiveEnd :
    Fintype.card {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 //
      ReturnsWithinTwo f ∧ (LeftPermutive f ∨ RightPermutive f)} = 4 := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see card_returnsWithinTwo.
/-- **Either holds at `152` tables**: the class of the corollary below. -/
theorem card_forcingClass :
    Fintype.card {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 //
      ReturnsWithinTwo f ∨ LeftPermutive f ∨ RightPermutive f} = 152 := by
  decide

/-! ## The class corollary -/

/-- **The parent's conclusion over the counted class**: at every scale, two states each erasing
within `2` have the same successor, at every table that returns within two or is permutive at an
end. -/
theorem lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hf : ReturnsWithinTwo f ∨ LeftPermutive f ∨ RightPermutive f) (τ : ℕ) (x y : ℤ → ZMod 2)
    (hx : ErasesWithin ((lineRule f)^[τ]) x 2) (hy : ErasesWithin ((lineRule f)^[τ]) y 2) :
    (lineRule f)^[τ] x = (lineRule f)^[τ] y := by
  refine lineRule_iterate_eq_of_erasesWithin_two_of_forcing f ?_ τ x y hx hy
  rcases hf with h | h | h
  · exact Or.inl (hasPersistentWord_of_returnsWithinTwo f h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see the return lemma's witness.
/-- **The corollary's hypotheses are jointly satisfiable**: at the product table the certificate
holds, and the two states `0` and the single `1` at the origin each erase within `2` at scale `2`
and differ. -/
theorem lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_nonvacuous :
    ReturnsWithinTwo (fun a b c : ZMod 2 => a * b * c) ∧
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2]) (fun _ : ℤ => 0) 2 ∧
    ErasesWithin ((lineRule fun a b c : ZMod 2 => a * b * c)^[2])
      (fun j : ℤ => if j = 0 then 1 else 0) 2 ∧
    (fun _ : ℤ => (0 : ZMod 2)) ≠ (fun j : ℤ => if j = 0 then 1 else 0) := by
  obtain ⟨-, h0, h1, hne⟩ := lineRule_iterate_eq_of_erasesWithin_two_of_forcing_nonvacuous
  exact ⟨by decide, h0, h1, hne⟩

end ForcingCount

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean, and the guards below make that
build-enforced. -/

set_option linter.style.longLine false

/-- info: 'ForcingCount.stepsInto_stepWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.stepsInto_stepWord

/-- info: 'ForcingCount.stepWord_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.stepWord_mono

/-- info: 'ForcingCount.stepWord_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.stepWord_translate

/-- info: 'ForcingCount.hasPersistentWord_of_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.hasPersistentWord_of_return

/-- info: 'ForcingCount.hasPersistentWord_of_return_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.hasPersistentWord_of_return_nonvacuous

/-- info: 'ForcingCount.hasPersistentWord_of_returnsWithinTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.hasPersistentWord_of_returnsWithinTwo

/-- info: 'ForcingCount.card_returnsWithinTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.card_returnsWithinTwo

/-- info: 'ForcingCount.card_permutiveEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.card_permutiveEnd

/-- info: 'ForcingCount.card_returnsWithinTwo_and_permutiveEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.card_returnsWithinTwo_and_permutiveEnd

/-- info: 'ForcingCount.card_forcingClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.card_forcingClass

/-- info: 'ForcingCount.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass

/-- info: 'ForcingCount.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_nonvacuous

/-- info: 'ForcingCount.returnsWithinTwo_majTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.returnsWithinTwo_majTable

/-- info: 'ForcingCount.not_returnsWithinTwo_add_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ForcingCount.not_returnsWithinTwo_add_ends

