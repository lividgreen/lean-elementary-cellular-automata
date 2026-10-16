module

public import ECA.ObservedRays
public import Nonautonomous.MergeQuotient

/-!
# Decimation: rule 90 simulates itself
([RuleSpace] §5 Proposition 5.7, row RS-27; the setting is [RuleSpace] §2 Definition 2.1)

Sampling one residue every `2 ^ M` cells of a state of the line (`decim M r`) is a blocking
transformation in Wolfram's (1986) sense, and a factor map of the rule `f90` run for `2 ^ M`
steps: the `2 ^ M`-fold iterate, composed with the decimation, is one step of `f90` on the
decimated state (`decim_iterate_f90`, the identity `iterate_two_pow_f90` supplies).
On the light-cone family of an `n`-cell window with the time dilated by `2 ^ M`, this is a
semiconjugacy from the nonautonomous system to rule `90`, its map depending on time, whose factor
map's fibers are the light-cone family of the `n'`-cell window when `n = 2 ^ M * n'`
(`imageFiber_decim_f90`): rule 90 on a window simulates itself on a window `2 ^ M` times smaller,
at time scale `2 ^ M`. Decimations compose (`decim_decim`), so the simulation is a tower. Rule 30
has no such factor map at scale two (`not_exists_decim_law_f30`).

## Main results

* `decim` — the state `i ↦ s (r + 2 ^ M * i)`.
* `decim_iterate_f90` — `2 ^ M` steps of `f90`, decimated, are one step of `f90` on the
  decimation.
* `decim_surjective` — every state is a decimation.
* `positivelyInvariant_lightCone_iterate_f90` / `nonautonomousSemiconj_decim_f90` /
  `imageFiber_decim_f90` — the light-cone family is positively invariant under the `2 ^ M`-fold
  iterate, the semiconjugacy holds, and the factor map's fiber is the light-cone family of the
  smaller window. `imageFiber_decim_f90_nonvacuous` shows the factor map's fiber at `M = 1`,
  `n' = 1`, `t = 0` holds a nonzero state.
* `decim_decim` — composing two decimations is one decimation: the tower.
* `not_exists_decim_law_f30` — **the guard**: no map on states carries the second iterate of
  rule 30, read at the even cells, to a law on the even cells.
-/

@[expose] public section

namespace ECA

open LocalRule

open Nonautonomous

/-- The sampling map `i ↦ r + 2 ^ M * i` is injective, which is what makes `decim` a factor map. -/
theorem decim_injective (M : ℕ) (r : ℤ) :
    Function.Injective (fun i : ℤ => r + 2 ^ M * i) := by
  intro a b h
  have h2 : (2 : ℤ) ^ M * a = 2 ^ M * b := by simpa using h
  exact mul_left_cancel₀ (pow_ne_zero M (by norm_num)) h2

/-- **Decimation**: the state `i ↦ s (r + 2 ^ M * i)`, sampling one residue every `2 ^ M` cells
(the factor map of [RuleSpace] §2 Definition 2.1, at the line). -/
noncomputable def decim (M : ℕ) (r : ℤ) (s : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.comapDomain (fun i : ℤ => r + 2 ^ M * i) s (decim_injective M r).injOn

/-- The value of a decimation at a cell. -/
theorem decim_apply (M : ℕ) (r : ℤ) (s : FiniteConfiguration) (i : ℤ) :
    decim M r s i = s (r + 2 ^ M * i) := by
  simp [decim, Finsupp.comapDomain_apply]

/-- **`2 ^ M` steps of rule 90, read through the decimation, are one step of rule 90**. -/
theorem decim_iterate_f90 (M : ℕ) (r : ℤ) (s : FiniteConfiguration) :
    decim M r ((finRule f90 hq90)^[2 ^ M] s) = finRule f90 hq90 (decim M r s) := by
  ext i
  rw [decim_apply, iterate_two_pow_f90, finRule_apply, decim_apply, decim_apply,
    decim_apply, f90]
  have e1 : r + 2 ^ M * i - 2 ^ M = r + 2 ^ M * (i - 1) := by ring
  have e2 : r + 2 ^ M * i + 2 ^ M = r + 2 ^ M * (i + 1) := by ring
  rw [e1, e2]

/-- **Every state is a decimation**: each `decim M r` is onto (a factor map onto the
whole carrier). -/
theorem decim_surjective (M : ℕ) (r : ℤ) : Function.Surjective (decim M r) := by
  intro u
  refine ⟨Finsupp.mapDomain (fun i : ℤ => r + 2 ^ M * i) u, ?_⟩
  ext i
  rw [decim_apply]
  exact Finsupp.mapDomain_apply_of_injective (decim_injective M r) u i

private theorem iterate_mem_lightCone (n : ℕ) (k t : ℕ) (s : FiniteConfiguration)
    (hs : s ∈ lightCone n t) :
    (finRule f90 hq90)^[k] s ∈ lightCone n (t + k) := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact positivelyInvariant_lightCone_finRule f90 hq90 n (t + k) _ ih

/-- **The light-cone family, dilated by `2 ^ M`, is positively invariant under the `2 ^ M`-fold
iterate of rule 90** ([RuleSpace] §2 Definition 2.1's invariance condition). -/
theorem positivelyInvariant_lightCone_iterate_f90 (n M : ℕ) :
    PositivelyInvariant ((finRule f90 hq90)^[2 ^ M]) (fun t => lightCone n (2 ^ M * t)) := by
  intro t s hs
  have := iterate_mem_lightCone n (2 ^ M) (2 ^ M * t) s hs
  change _ ∈ lightCone n (2 ^ M * (t + 1))
  rw [show 2 ^ M * (t + 1) = 2 ^ M * t + 2 ^ M by ring]
  exact this

/-- **The semiconjugacy** ([RuleSpace] §2 Definition 2.1): the `2 ^ M`-fold iterate of rule 90 on
the dilated light cone, composed with the decimation, closes over one step of rule 90. -/
theorem nonautonomousSemiconj_decim_f90 (n M : ℕ) (r : ℤ) :
    Semiconj ((finRule f90 hq90)^[2 ^ M]) (finRule f90 hq90) (fun _ => decim M r)
      (fun t => lightCone n (2 ^ M * t)) :=
  fun _ s _ => decim_iterate_f90 M r s

/-- **Rule 90 on a `2 ^ M * n'`-cell window simulates itself on an `n'`-cell window**
([RuleSpace] §2 Proposition 2.5's setting): the factor map's fiber at time `t` is the light-cone
family of the smaller window. -/
theorem imageFiber_decim_f90 (n' M t : ℕ) :
    imageFiber (fun _ => decim M 0) (fun t => lightCone (2 ^ M * n') (2 ^ M * t)) t
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

/-- The factor map's fiber of `imageFiber_decim_f90` is not trivial: at `M = 1`, `n' = 1`, `t = 0`
it contains the single-cell state at `0`. -/
theorem imageFiber_decim_f90_nonvacuous :
    ∃ u ∈ imageFiber (fun _ => decim 1 0)
      (fun t => lightCone (2 ^ 1 * 1) (2 ^ 1 * t)) 0, u ≠ 0 := by
  refine ⟨Finsupp.single 0 1, ?_, ?_⟩
  · rw [imageFiber_decim_f90]
    intro i hi
    have : i = 0 := by
      by_contra h
      apply Finsupp.mem_support_iff.mp hi
      simp [Ne.symm h]
    subst this
    simp
  · intro h
    have := congrArg (fun s : FiniteConfiguration => s 0) h
    simp at this

/-- **The tower**: composing two decimations is one decimation, the scales multiplying
(`2 ^ M * 2 ^ M' = 2 ^ (M + M')`). -/
theorem decim_decim (M M' : ℕ) (r r' : ℤ) (s : FiniteConfiguration) :
    decim M' r' (decim M r s) = decim (M + M') (r + 2 ^ M * r') s := by
  ext i
  rw [decim_apply, decim_apply, decim_apply]
  congr 1
  rw [pow_add]
  ring

/-- **The guard: rule 30 admits no law at scale two.** The two states `0` and the single cell at
`1` agree at every even cell, and their second iterates under rule 30 differ at cell `0`, so no
map on the decimated states carries one decimated step to the second iterate. -/
theorem not_exists_decim_law_f30 :
    ¬ ∃ F : FiniteConfiguration → FiniteConfiguration,
      ∀ s, decim 1 0 ((finRule f30 hq30)^[2] s) = F (decim 1 0 s) := by
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
  have h2 := congrArg (fun s : FiniteConfiguration => s 0) h1
  simp only [decim_apply] at h2
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    finRule_apply, f30, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
  revert h2
  decide +revert

end ECA

/-- info: 'ECA.decim_iterate_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_iterate_f90

/-- info: 'ECA.decim_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_surjective

/-- info: 'ECA.positivelyInvariant_lightCone_iterate_f90' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.positivelyInvariant_lightCone_iterate_f90

/-- info: 'ECA.nonautonomousSemiconj_decim_f90' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.nonautonomousSemiconj_decim_f90

/-- info: 'ECA.imageFiber_decim_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.imageFiber_decim_f90

/-- info: 'ECA.imageFiber_decim_f90_nonvacuous' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.imageFiber_decim_f90_nonvacuous

/-- info: 'ECA.decim_decim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_decim

/-- info: 'ECA.not_exists_decim_law_f30' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_exists_decim_law_f30
