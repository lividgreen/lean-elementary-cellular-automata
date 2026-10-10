/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.Iterate

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing-world kernel: staged squares, factor closure and the merge quotient
([RuleSpace] §2 Definition 2.1, Definition 2.2, Proposition 2.5 and Proposition 2.6)

The generic part of the growing-world development, over arbitrary carrier types and nothing but
Mathlib: a stage family `Ω : ℕ → Set X` **advances** under an update `U` (`GrowingWorld.Advances`),
a **staged square** closes a reading's law against the world's step (`GrowingWorld.StagedSquare`),
the reading's stage-`t` image is the image of the world's (`GrowingWorld.guestStage`), and a
reading of a growing world is itself a growing world (`GrowingWorld.advances_guestStage`).

Beside it, the **merge quotient** of an update `U`: two states eventually merge when some finite
iterate identifies them (`GrowingCore.Merges`), the quotient by that relation carries an induced
law that is automatically injective, and every injective-law staged-square reading factors through
it (`GrowingCore.merges_invariant_of_stagedSquare`).

## Main results

* `GrowingWorld.Advances` / `GrowingWorld.StagedSquare` / `GrowingWorld.guestStage` — the staged
  hypotheses and the reading's stage.
* `GrowingWorld.advances_guestStage` — **factor closure**: a reading of a growing world is itself a
  growing world.
* `GrowingCore.Merges` / `GrowingCore.mergesSetoid` / `GrowingCore.MergeQuot` — **the
  manufacture**: eventual merging is an equivalence, and its quotient is the canonical carrier.
* `GrowingCore.mergeLaw` / `GrowingCore.mergeLaw_injective` / `GrowingCore.stagedSquare_merge` —
  the induced law is well-defined, injective with no hypothesis, and closes the staged square
  identically at every stage family.
* `GrowingCore.mergeMk_injective_of_injective` — at an injective `U`, `mergeMk U` is itself
  injective.
* `GrowingCore.merges_invariant_of_stagedSquare` / `GrowingCore.exists_mergeMk_injective` —
  **universality**: any injective-law staged-square reading is merge-invariant per stage.
* `GrowingCore.mergeStage` / `GrowingCore.advances_mergeStage` / `GrowingCore.mergeStage_injOn` —
  **the retained profile**: the quotient's own reading stage, advancing under `Advances` and
  injected stage-to-stage by `mergeLaw`.

Each declaration keeps the namespace of the module it was stated in (`GrowingWorld`,
`GrowingCore`); the files `GrowingWorld.lean` and `GrowingCore.lean` carry the tape instance, the
fixed-carrier coherence and the finite bridge built on this kernel.
-/


@[expose] public section

namespace GrowingWorld

variable {X M : Type*}

/-! ## The staged hypotheses, at an arbitrary carrier -/

/-- One update advances the stage: a state admitted at stage `t` is carried into stage `t + 1`.
Stated at an arbitrary carrier. -/
def Advances (U : X → X) (Ω : ℕ → Set X) : Prop :=
  ∀ t, ∀ s ∈ Ω t, U s ∈ Ω (t + 1)

/-- **The staged square** ([RuleSpace] §2 Definition 2.1): one
world step, read one stage later, is one step of the reading's own law `F` applied to the current
reading, restricted at each `t` to the stage
`Ω t` the world admits there — `stagedSquare_const_iff` below makes that restriction precise at the
constant family. -/
def StagedSquare (U : X → X) (F : M → M) (ℓ : ℕ → X → M) (Ω : ℕ → Set X) : Prop :=
  ∀ t, ∀ s ∈ Ω t, ℓ (t + 1) (U s) = F (ℓ t s)

/-- The reading's stage `t`: the image of the world's stage `t` under the reading. Staged
surjectivity onto this set is definitional, not a further clause. -/
def guestStage (ℓ : ℕ → X → M) (Ω : ℕ → Set X) (t : ℕ) : Set M := ℓ t '' Ω t

/-! ## Factor closure -/

/-- **Factor closure**, the module's reason to exist: a reading of a growing world is itself a
growing world ([RuleSpace] §2 Proposition 2.5), its own stages — the images of the world's —
advancing under the reading's law `F`. One
line from the square: a point of the image steps, via `F`, to the image of the host's stepped
point. -/
theorem advances_guestStage {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hadv : Advances U Ω) (hsq : StagedSquare U F ℓ Ω) :
    Advances F (guestStage ℓ Ω) := by
  rintro t _ ⟨s, hs, rfl⟩
  exact ⟨U s, hadv t s hs, hsq t s hs⟩

end GrowingWorld

namespace GrowingCore

variable {X M : Type*}

/-! ## The manufacture: eventual merging and its quotient -/

/-- **Eventual merging**: two states whose orbits are eventually identified by some common number of
steps. An equivalence relation (`merges_refl` / `merges_symm` / `merges_trans`), and the object the
whole file is built on: it needs nothing beyond `U` itself, no reading and no law. -/
def Merges (U : X → X) (s s' : X) : Prop := ∃ k, U^[k] s = U^[k] s'

/-- If two iterates agree at some exponent, they agree at every larger exponent — the monotonicity
that makes `Merges` transitive and that peels an injective law's iterate back to its base case. -/
private theorem merges_of_iterate_eq_ge {U : X → X} {s s' : X} {k m : ℕ}
    (h : U^[k] s = U^[k] s') (hm : k ≤ m) : U^[m] s = U^[m] s' := by
  have e : m - k + k = m := Nat.sub_add_cancel hm
  calc U^[m] s = U^[m - k] (U^[k] s) := by rw [← Function.iterate_add_apply, e]
    _ = U^[m - k] (U^[k] s') := by rw [h]
    _ = U^[m] s' := by rw [← Function.iterate_add_apply, e]

theorem merges_refl (U : X → X) (s : X) : Merges U s s := ⟨0, rfl⟩

theorem merges_symm {U : X → X} {s s' : X} (h : Merges U s s') : Merges U s' s :=
  ⟨h.choose, h.choose_spec.symm⟩

theorem merges_trans {U : X → X} {s s' s'' : X} (h1 : Merges U s s') (h2 : Merges U s' s'') :
    Merges U s s'' := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  exact ⟨max k k', by
    rw [merges_of_iterate_eq_ge hk (le_max_left k k'),
      merges_of_iterate_eq_ge hk' (le_max_right k k')]⟩

/-- The setoid of eventual merging, over an arbitrary update `U`. -/
def mergesSetoid (U : X → X) : Setoid X where
  r := Merges U
  iseqv := ⟨merges_refl U, merges_symm, merges_trans⟩

/-- The quotient by eventual merging — the canonical carrier every reading with an injective law
factors through (`exists_mergeMk_injective`). Reducible: kept transparent so tactics see through it
to the underlying `Quotient` the way they see through any other type synonym in this development. -/
abbrev MergeQuot (U : X → X) : Type _ := Quotient (mergesSetoid U)

/-- The quotient map, spelled out so call sites need not spell the setoid. Reducible, for the same
reason as `MergeQuot`. -/
abbrev mergeMk (U : X → X) (s : X) : MergeQuot U := Quotient.mk (mergesSetoid U) s

/-- `U` respects eventual merging: stepping both sides by `U` preserves any common iterate one step
later. What makes `mergeLaw` well-defined. -/
theorem mergeRespects (U : X → X) :
    ∀ ⦃s s' : X⦄, Merges U s s' → Merges U (U s) (U s') := by
  rintro s s' ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc U^[k] (U s) = U^[k + 1] s := (Function.iterate_succ_apply U k s).symm
    _ = U (U^[k] s) := Function.iterate_succ_apply' U k s
    _ = U (U^[k] s') := congrArg U hk
    _ = U^[k + 1] s' := (Function.iterate_succ_apply' U k s').symm
    _ = U^[k] (U s') := Function.iterate_succ_apply U k s'

/-- The converse step: if the `U`-images merge, so did the states themselves — one more step of
iterate bookkeeping. What makes `mergeLaw` injective. -/
private theorem merges_of_merges_apply {U : X → X} {s s' : X} (h : Merges U (U s) (U s')) :
    Merges U s s' := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  calc U^[k + 1] s = U^[k] (U s) := Function.iterate_succ_apply U k s
    _ = U^[k] (U s') := hk
    _ = U^[k + 1] s' := (Function.iterate_succ_apply U k s').symm

/-- **The induced law, well-defined with no hypothesis**: `mergeLaw U ⟦s⟧ = ⟦U s⟧`. -/
def mergeLaw (U : X → X) : MergeQuot U → MergeQuot U := Quotient.map U (mergeRespects U)

@[simp] theorem mergeLaw_mergeMk (U : X → X) (s : X) : mergeLaw U (mergeMk U s) = mergeMk U (U s) :=
  Quotient.map_mk U (mergeRespects U) s

/-- **The induced law is injective, with no hypothesis at all**: this is the whole reason eventual
merging manufactures a reading with an injective law rather than merely a reading. -/
theorem mergeLaw_injective (U : X → X) : Function.Injective (mergeLaw U) := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ s => induction y using Quotient.inductionOn with
    | _ s' =>
      intro hxy
      rw [mergeLaw_mergeMk, mergeLaw_mergeMk] at hxy
      exact Quotient.sound (merges_of_merges_apply (Quotient.exact hxy))

/-- **`mergeMk` itself is injective when `U` is**: `Merges U s s'` unwinds to `∃ k, U^[k] s = U^[k]
s'`, and an injective `U` has injective iterates, so the witnessing equation collapses to `s = s'`
directly — no merging happens at all. -/
theorem mergeMk_injective_of_injective {U : X → X} (hU : Function.Injective U) :
    Function.Injective (mergeMk U) := by
  intro s s' hss'
  obtain ⟨k, hk⟩ := Quotient.exact hss'
  exact hU.iterate k hk

/-- **The staged square, at every stage family, with no hypothesis**: the quotient map is a
time-independent reading that closes the square against `mergeLaw` identically — this is the
manufacture, [RuleSpace] §2 Proposition 2.6(i). -/
theorem stagedSquare_merge (U : X → X) (Ω : ℕ → Set X) :
    GrowingWorld.StagedSquare U (mergeLaw U) (fun _ s => mergeMk U s) Ω := by
  intro _t s _
  exact (mergeLaw_mergeMk U s).symm

/-! ## Universality: every reading with an injective law factors through the quotient -/

/-- The host's forward orbit stays in its stages: `k` steps from a stage-`t` state lands in stage
`t + k`. Repeated `Advances`. -/
private theorem mem_stage_of_advances {U : X → X} {Ω : ℕ → Set X} (hadv : GrowingWorld.Advances U Ω)
    {t : ℕ} {s : X} (hs : s ∈ Ω t) : ∀ k, U^[k] s ∈ Ω (t + k) := by
  intro k
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have h := hadv (t + k) (U^[k] s) ih
    rw [Function.iterate_succ_apply']
    exact h

/-- The iterated square: `k` host steps, read `k` stages later, is `k` law steps applied to the
current reading. Needs `Advances` to keep the intermediate points in their stages. -/
private theorem iterate_stagedSquare {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hadv : GrowingWorld.Advances U Ω) (hsq : GrowingWorld.StagedSquare U F ℓ Ω)
    {t : ℕ} {s : X} (hs : s ∈ Ω t) :
    ∀ k, ℓ (t + k) (U^[k] s) = F^[k] (ℓ t s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hmem : U^[k] s ∈ Ω (t + k) := mem_stage_of_advances hadv hs k
    have hstep := hsq (t + k) (U^[k] s) hmem
    have hidx : t + (k + 1) = t + k + 1 := rfl
    calc ℓ (t + (k + 1)) (U^[k + 1] s)
        = ℓ (t + k + 1) (U (U^[k] s)) := by rw [hidx, Function.iterate_succ_apply']
      _ = F (ℓ (t + k) (U^[k] s)) := hstep
      _ = F (F^[k] (ℓ t s)) := by rw [ih]
      _ = F^[k + 1] (ℓ t s) := (Function.iterate_succ_apply' F k (ℓ t s)).symm

/-- **Universality** ([RuleSpace] §2 Proposition 2.6(ii)): any staged-square reading with an
INJECTIVE law is merge-invariant per stage — two states admitted at the same stage that eventually
merge are read identically. So every reading with an injective law factors through the merge
quotient. -/
theorem merges_invariant_of_stagedSquare {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hF : Function.Injective F) (hadv : GrowingWorld.Advances U Ω)
    (hsq : GrowingWorld.StagedSquare U F ℓ Ω) :
    ∀ t, ∀ s ∈ Ω t, ∀ s' ∈ Ω t, Merges U s s' → ℓ t s = ℓ t s' := by
  rintro t s hs s' hs' ⟨k, hk⟩
  have h1 := iterate_stagedSquare hadv hsq hs k
  have h2 := iterate_stagedSquare hadv hsq hs' k
  rw [hk, h2] at h1
  exact hF.iterate k h1.symm

/-- **The stage-`t` image of any reading with an injective law injects into the merge classes over
`Ω t`** ([RuleSpace] §2 Proposition 2.6(ii)): the merge quotient is the maximal such reading, so
its retained profile ceilings every other one's. -/
theorem exists_mergeMk_injective {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hF : Function.Injective F) (hadv : GrowingWorld.Advances U Ω)
    (hsq : GrowingWorld.StagedSquare U F ℓ Ω) (t : ℕ) :
    ∃ g : ↥(GrowingWorld.guestStage ℓ Ω t) → MergeQuot U,
      (∀ m, g m ∈ GrowingWorld.guestStage (fun _ s => mergeMk U s) Ω t) ∧ Function.Injective g := by
  classical
  choose s hsmem hseq using fun m : ↥(GrowingWorld.guestStage ℓ Ω t) => m.2
  refine ⟨fun m => mergeMk U (s m), fun m => ⟨s m, hsmem m, rfl⟩, ?_⟩
  intro m m' hmm'
  have hmerges : Merges U (s m) (s m') := Quotient.exact hmm'
  have heq := merges_invariant_of_stagedSquare hF hadv hsq t (s m) (hsmem m) (s m') (hsmem m')
    hmerges
  exact Subtype.ext (by rw [← hseq m, ← hseq m', heq])

/-! ## The retained profile -/

/-- **The retained profile `R_t`** ([RuleSpace] §2 Definition 2.2): the merge quotient's own reading
stage — the classes represented among the states `Ω` admits at stage `t`. Reuses
`GrowingWorld.guestStage` directly; no new machinery. -/
def mergeStage (U : X → X) (Ω : ℕ → Set X) (t : ℕ) : Set (MergeQuot U) :=
  GrowingWorld.guestStage (fun _ s => mergeMk U s) Ω t

/-- **The stage-to-stage injection** ([RuleSpace] §2 Proposition 2.6(iii)): `mergeLaw` carries the
stage-`t` retained classes into the stage-`(t + 1)` ones, since the quotient is itself a reading of
`(U, Ω)` (`stagedSquare_merge`) and factor closure (`GrowingWorld.advances_guestStage`) applies with
no further hypothesis. -/
theorem advances_mergeStage {U : X → X} {Ω : ℕ → Set X} (hadv : GrowingWorld.Advances U Ω) :
    GrowingWorld.Advances (mergeLaw U) (mergeStage U Ω) :=
  GrowingWorld.advances_guestStage hadv (stagedSquare_merge U Ω)

/-- The stage-to-stage map is injective — `mergeLaw` never collapses distinct classes, at any
stage. -/
theorem mergeStage_injOn (U : X → X) (Ω : ℕ → Set X) (t : ℕ) :
    Set.InjOn (mergeLaw U) (mergeStage U Ω t) :=
  (mergeLaw_injective U).injOn

end GrowingCore
