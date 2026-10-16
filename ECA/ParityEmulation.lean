module

public import ECA.RationalRayRule90

/-!
# Parity emulation of rule 90, and rule 18's erasure of gap-filling hits
([RuleSpace] §5)

A radius-one rule on finitely supported states is read through `LocalRule.finRule`. This file states
three things about rule `90` (`f90`, the sum of the two outer cells).

* **A class that steps as `90` does on one-parity states.** `LocalRule.AgreesOffAdjacent f` asks
  that `f` agree with `f90` on the five neighbourhoods with no two adjacent set cells; eight rules
  meet it (`card_agreesOffAdjacent`). A state is `FiniteConfiguration.OneParity` when all its set
  cells have the same parity. On such states every rule of the class steps as `90` does
  (`FiniteConfiguration.OneParity.finRule_eq_f90`), one parity is preserved by `90`
  (`oneParity_finRule_f90`), so the whole orbit agrees
  (`FiniteConfiguration.OneParity.iterate_eq_f90`), and the doubling identity of `90` carries over
  to the class (`FiniteConfiguration.OneParity.iterate_two_pow_add`). The two translated copies in
  that identity do not overlap once `2 ^ (M + 1)` exceeds the width of the support
  (`two_pow_copies_disjoint`).
* **Rule 18 erases gap-filling hits.** `f18` is Wolfram's rule 18. At every finitely supported
  state, setting any set of cells that each sit between two set cells leaves the next state
  unchanged (`finRule_f18_add_gapFill`).
* **Guards.** Off the parity class the emulation fails (`f18_ne_f90_off_parity`), the gap
  hypothesis is needed for the erasure (`gapFill_erasure_needs_gap`), and rule `90` erases no
  such hit (`f90_does_not_erase_gapFill`).

## Main results

* `FiniteConfiguration.OneParity.finRule_eq_f90` — one step, over the class and the parity states.
* `FiniteConfiguration.OneParity.iterate_eq_f90` — the orbit, with `oneParity_iterate_finRule_f90`.
* `FiniteConfiguration.OneParity.iterate_two_pow_add` — the doubling identity over the class.
* `finRule_f18_add_gapFill` — the erasure, over every finitely supported state.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- Agreement with `f90` on the five neighbourhoods with no two adjacent set cells; the first
conjunct is the quiescence `LocalRule.finRule` takes. -/
def LocalRule.AgreesOffAdjacent (f : LocalRule) : Prop :=
  f 0 0 0 = 0 ∧ f 0 0 1 = 1 ∧ f 1 0 0 = 1 ∧ f 0 1 0 = 0 ∧ f 1 0 1 = 0

/-- A finitely supported state is of one parity when all its set cells differ by even amounts. -/
def FiniteConfiguration.OneParity (s : FiniteConfiguration) : Prop :=
  ∀ i j, s i ≠ 0 → s j ≠ 0 → Even (i - j)

/-- Wolfram's rule 18, with `a` the left neighbour: `(a + c) * (1 + b)`. -/
def f18 : LocalRule := fun a b c => (a + c) * (1 + b)

/-- Quiescence of `f18`. -/
theorem hq18 : f18 0 0 0 = 0 := by decide

/-- Rule `90` meets the agreement. -/
theorem agreesOffAdjacent_f90 : AgreesOffAdjacent f90 := by
  unfold AgreesOffAdjacent f90; decide

/-- Rule 18 meets the agreement. -/
theorem agreesOffAdjacent_f18 : AgreesOffAdjacent f18 := by
  unfold AgreesOffAdjacent f18; decide

/-- The agreement is decidable, so the class is a finite type. -/
instance LocalRule.decidableAgreesOffAdjacent : DecidablePred AgreesOffAdjacent := fun f => by
  unfold AgreesOffAdjacent; infer_instance

/-- Exactly eight rules meet the agreement: the three remaining neighbourhoods are free. -/
theorem card_agreesOffAdjacent :
    Fintype.card {f : LocalRule // AgreesOffAdjacent f} = 8 := by
  decide

private theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

private theorem not_adjacent (s : FiniteConfiguration) (hs : OneParity s) (i : ℤ)
    (h : s i ≠ 0) (h' : s (i + 1) ≠ 0) : False := by
  have := hs i (i + 1) h h'
  rw [even_iff_two_dvd] at this
  omega

/-- One step: over the class, a one-parity state steps as `90` does. -/
theorem FiniteConfiguration.OneParity.finRule_eq_f90 (f : LocalRule)
    (h : AgreesOffAdjacent f) (s : FiniteConfiguration) (hs : OneParity s) :
    finRule f h.1 s = finRule f90 hq90 s := by
  ext i
  rw [finRule_apply, finRule_apply]
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  have hab : s (i - 1) ≠ 0 → s i ≠ 0 → False := by
    intro ha hb
    have := not_adjacent s hs (i - 1) ha (by simpa using hb)
    exact this
  have hbc : s i ≠ 0 → s (i + 1) ≠ 0 → False := fun hb hc => not_adjacent s hs i hb hc
  rcases zmod2_cases (s (i - 1)) with ha | ha <;> rcases zmod2_cases (s i) with hb | hb <;>
    rcases zmod2_cases (s (i + 1)) with hc | hc <;> simp only [ha, hb, hc] at hab hbc ⊢ <;>
    first
    | (exfalso; apply hab <;> decide)
    | (exfalso; apply hbc <;> decide)
    | (simp only [f90]; assumption)

private theorem oneParity_finRule_f90_aux (s : FiniteConfiguration) (i : ℤ)
    (hi : finRule f90 hq90 s i ≠ 0) : ∃ k : ℤ, (k = -1 ∨ k = 1) ∧ s (i + k) ≠ 0 := by
  rw [finRule_apply] at hi
  by_cases ha : s (i - 1) = 0
  · by_cases hc : s (i + 1) = 0
    · exfalso; apply hi; simp [f90, ha, hc]
    · exact ⟨1, Or.inr rfl, hc⟩
  · exact ⟨-1, Or.inl rfl, by simpa [sub_eq_add_neg] using ha⟩

/-- Closure: one parity is preserved by rule `90`. -/
theorem oneParity_finRule_f90 (s : FiniteConfiguration) (hs : OneParity s) :
    OneParity (finRule f90 hq90 s) := by
  intro i j hi hj
  obtain ⟨k, hk, hki⟩ := oneParity_finRule_f90_aux s i hi
  obtain ⟨l, hl, hlj⟩ := oneParity_finRule_f90_aux s j hj
  have := hs _ _ hki hlj
  rw [even_iff_two_dvd] at this ⊢
  rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;> omega

/-- The parity class is preserved along the whole orbit of rule `90`. -/
theorem oneParity_iterate_finRule_f90 (s : FiniteConfiguration) (hs : OneParity s) (t : ℕ) :
    OneParity ((finRule f90 hq90)^[t] s) := by
  induction t with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact oneParity_finRule_f90 _ ih

/-- The orbit: over the class, a one-parity state follows the orbit of rule `90`. -/
theorem FiniteConfiguration.OneParity.iterate_eq_f90 (f : LocalRule)
    (h : AgreesOffAdjacent f) (s : FiniteConfiguration) (hs : OneParity s) (t : ℕ) :
    (finRule f h.1)^[t] s = (finRule f90 hq90)^[t] s := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact FiniteConfiguration.OneParity.finRule_eq_f90 f h _ (oneParity_iterate_finRule_f90 s hs n)

/-- The doubling identity of rule `90` over the class. -/
theorem FiniteConfiguration.OneParity.iterate_two_pow_add (f : LocalRule)
    (h : AgreesOffAdjacent f) (s : FiniteConfiguration) (hs : OneParity s) (M t : ℕ) (i : ℤ) :
    ((finRule f h.1)^[2 ^ M + t] s) i =
      ((finRule f h.1)^[t] s) (i - 2 ^ M) + ((finRule f h.1)^[t] s) (i + 2 ^ M) := by
  rw [FiniteConfiguration.OneParity.iterate_eq_f90 f h s hs,
    FiniteConfiguration.OneParity.iterate_eq_f90 f h s hs,
    f90_iterate_two_pow_add]

/-- The two translated copies in the doubling identity do not overlap once `2 ^ (M + 1)` exceeds
the width of the support. -/
theorem two_pow_copies_disjoint (s : FiniteConfiguration) (a b : ℤ) (M : ℕ)
    (hsupp : ∀ i, s i ≠ 0 → a ≤ i ∧ i ≤ b) (hM : b - a < 2 ^ (M + 1)) (i : ℤ) :
    ¬ (s (i - 2 ^ M) ≠ 0 ∧ s (i + 2 ^ M) ≠ 0) := by
  rintro ⟨h1, h2⟩
  have := hsupp _ h1
  have := hsupp _ h2
  rw [pow_succ] at hM
  omega

/-- The hypotheses of the one-step emulation hold together, at rule 18 and two cells of one
parity. -/
theorem FiniteConfiguration.OneParity.finRule_eq_f90_nonvacuous :
    ∃ (f : LocalRule) (h : AgreesOffAdjacent f)
      (s : FiniteConfiguration), OneParity s ∧ finRule f h.1 s = finRule f90 hq90 s := by
  have hs : OneParity (Finsupp.single 0 1 + Finsupp.single 2 1) := by
    intro i j hi hj
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
    rw [even_iff_two_dvd]
    split_ifs at hi hj <;> first | omega | simp_all
  exact ⟨f18, agreesOffAdjacent_f18, _, hs,
    FiniteConfiguration.OneParity.finRule_eq_f90 f18 agreesOffAdjacent_f18 _ hs⟩

/-- **Erasure at rule 18, at every finitely supported state**: setting cells of `H`, each of
which is clear with both neighbours set, leaves the next state unchanged. The cells of `H` are
set by adding `Finsupp.indicator H (fun _ _ => 1)`. -/
theorem finRule_f18_add_gapFill (s : FiniteConfiguration) (H : Finset ℤ)
    (hH : ∀ h ∈ H, s h = 0 ∧ s (h - 1) = 1 ∧ s (h + 1) = 1) :
    finRule f18 hq18 (s + Finsupp.indicator H (fun _ _ => 1)) = finRule f18 hq18 s := by
  have hev : ∀ j, ((s + Finsupp.indicator H (fun _ _ => (1 : ZMod 2)) : FiniteConfiguration)) j
      = s j + (if j ∈ H then 1 else 0) := by
    intro j
    simp [Finsupp.indicator_apply]
  ext i
  rw [finRule_apply, finRule_apply, hev, hev, hev]
  have two : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases hi : i ∈ H
  · obtain ⟨h0, h1, h2⟩ := hH i hi
    have hl : i - 1 ∉ H := fun hm => by
      have := (hH _ hm).1; rw [h1] at this; exact absurd this (by decide)
    have hr : i + 1 ∉ H := fun hm => by
      have := (hH _ hm).1; rw [h2] at this; exact absurd this (by decide)
    simp [hi, hl, hr, h0, h1, h2, f18, two]
  · by_cases hl : i - 1 ∈ H
    · have := (hH _ hl).2.2
      rw [sub_add_cancel] at this
      simp [hi, hl, this, two, f18]
    · by_cases hr : i + 1 ∈ H
      · have := (hH _ hr).2.1
        rw [add_sub_cancel_right] at this
        simp [hi, hl, hr, this, two, f18]
      · simp [hi, hl, hr]

/-- The hypothesis of the erasure holds with `H = {1}` at two cells with a gap between them. -/
theorem finRule_f18_add_gapFill_nonvacuous :
    ∃ (s : FiniteConfiguration) (H : Finset ℤ), (∀ h ∈ H, s h = 0 ∧ s (h - 1) = 1 ∧ s (h + 1) = 1) ∧
      finRule f18 hq18 (s + Finsupp.indicator H (fun _ _ => 1)) = finRule f18 hq18 s := by
  have hH : ∀ h ∈ ({1} : Finset ℤ),
      (Finsupp.single 0 1 + Finsupp.single 2 1 : FiniteConfiguration) h = 0 ∧
      (Finsupp.single 0 1 + Finsupp.single 2 1 : FiniteConfiguration) (h - 1) = 1 ∧
      (Finsupp.single 0 1 + Finsupp.single 2 1 : FiniteConfiguration) (h + 1) = 1 := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst hh
    simp
  exact ⟨_, {1}, hH, finRule_f18_add_gapFill _ _ hH⟩

/-- Guard: off the parity class the emulation fails, two adjacent set cells at rule 18. -/
theorem f18_ne_f90_off_parity :
    finRule f18 hq18 (Finsupp.single 0 1 + Finsupp.single 1 1)
      ≠ finRule f90 hq90 (Finsupp.single 0 1 + Finsupp.single 1 1) := by
  intro h
  have := congrArg (fun t => t 0) h
  simp [finRule_apply, f18, f90] at this

/-- Guard: the gap hypothesis is needed, a hit beside a single set cell is not erased. -/
theorem gapFill_erasure_needs_gap :
    finRule f18 hq18 (Finsupp.single 0 1 + Finsupp.single 1 1)
      ≠ finRule f18 hq18 (Finsupp.single (0 : ℤ) (1 : ZMod 2)) := by
  intro h
  have := congrArg (fun t => t 1) h
  simp [finRule_apply, f18] at this

/-- Guard: rule `90` erases no such hit, filling the gap changes the next state. -/
theorem f90_does_not_erase_gapFill :
    finRule f90 hq90 (Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 1 1)
      ≠ finRule f90 hq90 (Finsupp.single 0 1 + Finsupp.single 2 1) := by
  intro h
  have := congrArg (fun t => t 0) h
  simp [finRule_apply, f90] at this

end ECA

/-- info: 'ECA.hq18' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.hq18

/-- info: 'ECA.agreesOffAdjacent_f90' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.agreesOffAdjacent_f90

/-- info: 'ECA.agreesOffAdjacent_f18' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.agreesOffAdjacent_f18

/-- info: 'ECA.card_agreesOffAdjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_agreesOffAdjacent

/-- info: 'ECA.FiniteConfiguration.OneParity.finRule_eq_f90' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.OneParity.finRule_eq_f90

/-- info: 'ECA.oneParity_finRule_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.oneParity_finRule_f90

/-- info: 'ECA.oneParity_iterate_finRule_f90' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.oneParity_iterate_finRule_f90

/-- info: 'ECA.FiniteConfiguration.OneParity.iterate_eq_f90' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.OneParity.iterate_eq_f90

/-- info: 'ECA.FiniteConfiguration.OneParity.iterate_two_pow_add' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.OneParity.iterate_two_pow_add

/-- info: 'ECA.two_pow_copies_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ECA.two_pow_copies_disjoint

/-- info: 'ECA.FiniteConfiguration.OneParity.finRule_eq_f90_nonvacuous' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.OneParity.finRule_eq_f90_nonvacuous

/-- info: 'ECA.finRule_f18_add_gapFill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f18_add_gapFill

/-- info: 'ECA.finRule_f18_add_gapFill_nonvacuous' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f18_add_gapFill_nonvacuous

/-- info: 'ECA.f18_ne_f90_off_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f18_ne_f90_off_parity

/-- info: 'ECA.gapFill_erasure_needs_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ECA.gapFill_erasure_needs_gap

/-- info: 'ECA.f90_does_not_erase_gapFill' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.f90_does_not_erase_gapFill
