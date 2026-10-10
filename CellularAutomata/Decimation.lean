/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.ObservedRays
public import CellularAutomata.MergeQuotient
-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Decimation: table 90 hosts itself
([RuleSpace] §5 Proposition 5.7, row RS-27; the setting is [RuleSpace] §2 Definition 2.1)

Reading one residue every `2 ^ M` cells of a state of the line (`decim M r`) is a reading of
the table `f90` run for `2 ^ M` steps: the `2 ^ M`-fold iterate, read through the
decimation, is one step of `f90` on the decimated state (`decim_iterate_f90`, the identity
`DrivenColumns.iterate_two_pow_f90` supplies). On the light-cone family of an `n`-cell window with
the stages dilated by `2 ^ M`, this is a staged square whose reading's stages are the light-cone
family of the `n'`-cell window when `n = 2 ^ M * n'` (`guestStage_decim_f90`): table 90 on a window
hosts itself on a window `2 ^ M` times smaller, at time scale `2 ^ M`. Decimations compose
(`decim_decim`), so the hosting is a tower. Table 30 has no such reading at scale two
(`not_exists_decim_law_f30`).

## Main results

* `decim` — the state `i ↦ s (r + 2 ^ M * i)`.
* `decim_iterate_f90` — `2 ^ M` steps of `f90`, decimated, are one step of `f90` on the
  decimation.
* `decim_surjective` — every state is a decimation.
* `advances_lightCone_iterate_f90` / `stagedSquare_decim_f90` / `guestStage_decim_f90` — the
  light-cone family advances under the `2 ^ M`-fold iterate, the staged square closes, and the
  reading's stage is the light-cone family of the smaller window.
  `guestStage_decim_f90_nonvacuous` shows the reading's stage at `M = 1`, `n' = 1`, `t = 0` holds a
  nonzero state.
* `decim_decim` — composing two decimations is one decimation: the tower.
* `not_exists_decim_law_f30` — **the guard**: no map on states carries the second iterate of
  table 30, read at the even cells, to a law on the even cells.
-/

@[expose] public section

namespace Decimation

open ExtremeTapWidth EndpointClasses LightConeWidth GrowingWorld
open ObservedColumn (hq90)

/-- The sampling map `i ↦ r + 2 ^ M * i` is injective, which is what makes `decim` a reading. -/
theorem decim_injective (M : ℕ) (r : ℤ) :
    Function.Injective (fun i : ℤ => r + 2 ^ M * i) := by
  intro a b h
  have h2 : (2 : ℤ) ^ M * a = 2 ^ M * b := by simpa using h
  exact mul_left_cancel₀ (pow_ne_zero M (by norm_num)) h2

/-- **Decimation**: the state `i ↦ s (r + 2 ^ M * i)`, reading one residue every `2 ^ M` cells
([RuleSpace] §2 Definition 2.1's reading, at the line). -/
noncomputable def decim (M : ℕ) (r : ℤ) (s : ℤ →₀ ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.comapDomain (fun i : ℤ => r + 2 ^ M * i) s (decim_injective M r).injOn

/-- The value of a decimation at a cell. -/
theorem decim_apply (M : ℕ) (r : ℤ) (s : ℤ →₀ ZMod 2) (i : ℤ) :
    decim M r s i = s (r + 2 ^ M * i) := by
  simp [decim, Finsupp.comapDomain_apply]

/-- **`2 ^ M` steps of table 90, read through the decimation, are one step of table 90**. -/
theorem decim_iterate_f90 (M : ℕ) (r : ℤ) (s : ℤ →₀ ZMod 2) :
    decim M r ((tableRule f90 hq90)^[2 ^ M] s) = tableRule f90 hq90 (decim M r s) := by
  ext i
  rw [decim_apply, DrivenColumns.iterate_two_pow_f90, tableRule_apply, decim_apply, decim_apply,
    decim_apply, f90]
  have e1 : r + 2 ^ M * i - 2 ^ M = r + 2 ^ M * (i - 1) := by ring
  have e2 : r + 2 ^ M * i + 2 ^ M = r + 2 ^ M * (i + 1) := by ring
  rw [e1, e2]

/-- **Every state is a decimation**: each `decim M r` is onto (a reading onto the
whole carrier). -/
theorem decim_surjective (M : ℕ) (r : ℤ) : Function.Surjective (decim M r) := by
  intro u
  refine ⟨Finsupp.mapDomain (fun i : ℤ => r + 2 ^ M * i) u, ?_⟩
  ext i
  rw [decim_apply]
  exact Finsupp.mapDomain_apply_of_injective (decim_injective M r) u i

private theorem iterate_mem_lightCone (n : ℕ) (k t : ℕ) (s : ℤ →₀ ZMod 2)
    (hs : s ∈ lightCone n t) :
    (tableRule f90 hq90)^[k] s ∈ lightCone n (t + k) := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact advances_lightCone_tableRule f90 hq90 n (t + k) _ ih

/-- **The light-cone family, dilated by `2 ^ M`, advances under the `2 ^ M`-fold iterate of
table 90** ([RuleSpace] §2 Definition 2.1's advancing condition). -/
theorem advances_lightCone_iterate_f90 (n M : ℕ) :
    Advances ((tableRule f90 hq90)^[2 ^ M]) (fun t => lightCone n (2 ^ M * t)) := by
  intro t s hs
  have := iterate_mem_lightCone n (2 ^ M) (2 ^ M * t) s hs
  change _ ∈ lightCone n (2 ^ M * (t + 1))
  rw [show 2 ^ M * (t + 1) = 2 ^ M * t + 2 ^ M by ring]
  exact this

/-- **The staged square** ([RuleSpace] §2 Definition 2.1): the `2 ^ M`-fold iterate of table 90 on
the dilated light cone, read through the decimation, closes over one step of table 90. -/
theorem stagedSquare_decim_f90 (n M : ℕ) (r : ℤ) :
    StagedSquare ((tableRule f90 hq90)^[2 ^ M]) (tableRule f90 hq90) (fun _ => decim M r)
      (fun t => lightCone n (2 ^ M * t)) :=
  fun _ s _ => decim_iterate_f90 M r s

/-- **Table 90 on a `2 ^ M * n'`-cell window hosts itself on an `n'`-cell window**
([RuleSpace] §2 Proposition 2.5's setting): the reading's stage at time `t` is the light-cone family
of the smaller window. -/
theorem guestStage_decim_f90 (n' M t : ℕ) :
    guestStage (fun _ => decim M 0) (fun t => lightCone (2 ^ M * n') (2 ^ M * t)) t
      = lightCone n' t := by
  ext u
  constructor
  · rintro ⟨s, hs, rfl⟩ i hi
    have hi' : s (0 + 2 ^ M * i) ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hi
      rwa [decim_apply] at this
    obtain ⟨h1, h2⟩ := hs _ (Finsupp.mem_support_iff.mpr hi')
    have hp : (0 : ℤ) < 2 ^ M := by positivity
    push_cast at h1 h2
    constructor
    · by_contra h
      replace h := not_le.mp h
      nlinarith
    · by_contra h
      replace h := not_lt.mp h
      nlinarith
  · intro hu
    refine ⟨Finsupp.mapDomain (fun i : ℤ => 0 + 2 ^ M * i) u, ?_, ?_⟩
    · intro j hj
      have := Finsupp.mapDomain_support hj
      rw [Finset.mem_image] at this
      obtain ⟨i, hi, rfl⟩ := this
      obtain ⟨h1, h2⟩ := hu i hi
      have hp : (0 : ℤ) < 2 ^ M := by positivity
      push_cast
      constructor <;> nlinarith
    · ext i
      rw [decim_apply]
      exact Finsupp.mapDomain_apply_of_injective (decim_injective M 0) u i

/-- The reading's stage of `guestStage_decim_f90` is not trivial: at `M = 1`, `n' = 1`, `t = 0` it
contains the single-cell state at `0`. -/
theorem guestStage_decim_f90_nonvacuous :
    ∃ u ∈ guestStage (fun _ => decim 1 0)
      (fun t => lightCone (2 ^ 1 * 1) (2 ^ 1 * t)) 0, u ≠ 0 := by
  refine ⟨Finsupp.single 0 1, ?_, ?_⟩
  · rw [guestStage_decim_f90]
    intro i hi
    have : i = 0 := by
      by_contra h
      apply Finsupp.mem_support_iff.mp hi
      simp [Ne.symm h]
    subst this
    simp
  · intro h
    have := congrArg (fun s : ℤ →₀ ZMod 2 => s 0) h
    simp at this

/-- **The tower**: composing two decimations is one decimation, the scales multiplying
(`2 ^ M * 2 ^ M' = 2 ^ (M + M')`). -/
theorem decim_decim (M M' : ℕ) (r r' : ℤ) (s : ℤ →₀ ZMod 2) :
    decim M' r' (decim M r s) = decim (M + M') (r + 2 ^ M * r') s := by
  ext i
  rw [decim_apply, decim_apply, decim_apply]
  congr 1
  rw [pow_add]
  ring

/-- **The guard: table 30 admits no law at scale two.** The two states `0` and the single cell at
`1` agree at every even cell, and their second iterates under table 30 differ at cell `0`, so no
map on the decimated states carries one decimated step to the second iterate. -/
theorem not_exists_decim_law_f30 :
    ¬ ∃ F : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2),
      ∀ s, decim 1 0 ((tableRule f30 hq30)^[2] s) = F (decim 1 0 s) := by
  rintro ⟨F, hF⟩
  have hdec : decim 1 0 (Finsupp.single (1 : ℤ) (1 : ZMod 2)) = decim 1 0 0 := by
    ext i
    rw [decim_apply, decim_apply]
    simp only [Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply]
    have : ¬ (1 : ℤ) = 0 + 2 ^ 1 * i := by omega
    simp only [this, ite_false]
  have h1 := hF (Finsupp.single (1 : ℤ) (1 : ZMod 2))
  have h0 := hF 0
  rw [hdec, ← h0] at h1
  have h2 := congrArg (fun s : ℤ →₀ ZMod 2 => s 0) h1
  simp only [decim_apply] at h2
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    tableRule_apply, f30, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
  revert h2
  decide +revert

end Decimation

/-- info: 'Decimation.decim_iterate_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decimation.decim_iterate_f90

/-- info: 'Decimation.decim_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decimation.decim_surjective

/-- info: 'Decimation.advances_lightCone_iterate_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decimation.advances_lightCone_iterate_f90

/-- info: 'Decimation.stagedSquare_decim_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decimation.stagedSquare_decim_f90

/-- info: 'Decimation.guestStage_decim_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decimation.guestStage_decim_f90

/-- info: 'Decimation.guestStage_decim_f90_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decimation.guestStage_decim_f90_nonvacuous

/-- info: 'Decimation.decim_decim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decimation.decim_decim

/-- info: 'Decimation.not_exists_decim_law_f30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decimation.not_exists_decim_law_f30
