module

public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.Iterate

/-!
# The nonautonomous kernel: semiconjugacies, factor closure and the merge quotient
([RuleSpace] §2 Definition 2.1, Definition 2.2, Proposition 2.5 and Proposition 2.6)

A **nonautonomous set** is a family of sets `Ω t`, the **fibers** `A(t)` in the terms of
Kloeden and Rasmussen, as used by Huynh, Kloeden and Pötzsche (2022). With an update `U` it is a
nonautonomous dynamical system in the sense of a sequence of sets with a map from each to the next
(Kawan 2017); the fibers here may be empty. The generic part of the development, over arbitrary
carrier types and nothing but Mathlib: a nonautonomous set `Ω : ℕ → Set X` is **positively
invariant** under an update `U` (`PositivelyInvariant`) when `U` carries the fiber at `t` into the
fiber at `t + 1`; a **semiconjugacy** from the nonautonomous system to an autonomous one, its map
depending on time (`Semiconj`; the word as in Brin and Stuck 2002, §1.1, where the map
is fixed and onto, and here it is neither), closes a factor map's law against the system's step;
the factor map's image of the fiber at `t` is a fiber of the factor (`imageFiber`); and a factor map
of a nonautonomous system is itself a nonautonomous system (`positivelyInvariant_imageFiber`).

Beside it, the **merge quotient** of an update `U`: two states eventually merge when some finite
iterate identifies them (`Nonautonomous.Merges`), the quotient by that relation carries an induced
law that is automatically injective, and every semiconjugate factor map with an injective law
factors through it (`Nonautonomous.Semiconj.merges_invariant`). On a finite set the
merge quotient is the eventual image (Leinster 2022, §6).

## Main results

* `Nonautonomous.PositivelyInvariant` / `Nonautonomous.Semiconj` /
  `Nonautonomous.imageFiber` — the invariance and semiconjugacy hypotheses, and the factor map's
  fibers.
* `Nonautonomous.positivelyInvariant_imageFiber` — **factor closure**: a factor map of a
  nonautonomous system is itself a nonautonomous system.
* `Nonautonomous.Merges` / `Nonautonomous.mergesSetoid` / `Nonautonomous.MergeQuot` — **the merge
  quotient**: eventual merging is an equivalence, and its quotient is the canonical carrier.
* `Nonautonomous.mergeLaw` / `Nonautonomous.mergeLaw_injective` /
  `Nonautonomous.semiconj_merge` —
  the induced law is well-defined, injective with no hypothesis, and the quotient map is a
  semiconjugacy at every nonautonomous set.
* `Nonautonomous.mergeMk_injective_of_injective` — at an injective `U`, `mergeMk U` is itself
  injective.
* `Nonautonomous.Semiconj.merges_invariant` /
  `Nonautonomous.exists_mergeMk_injective` —
  **universality**: any semiconjugate factor map with an injective law is merge-invariant per
  fiber.
* `Nonautonomous.mergeFiber` / `Nonautonomous.positivelyInvariant_mergeFiber` /
  `Nonautonomous.mergeFiber_injOn` —
  **the merge classes represented in the fibers**: the quotient's own fibers, positively invariant
  under `mergeLaw` and injected fiber to fiber by it.
-/


@[expose] public section

namespace Nonautonomous

variable {X M : Type*}

/-! ## Invariance and semiconjugacy, at an arbitrary carrier -/

/-- **Positive invariance**: the update carries the fiber at `t` into the fiber at `t + 1`.
Stated at an arbitrary carrier. -/
def PositivelyInvariant (U : X → X) (Ω : ℕ → Set X) : Prop :=
  ∀ t, ∀ s ∈ Ω t, U s ∈ Ω (t + 1)

/-- **The semiconjugacy** ([RuleSpace] §2 Definition 2.1): one
system step, read one time later, is one step of the factor map's own law `F` applied to the
current value, restricted at each `t` to the fiber `Ω t` the system admits there. -/
def Semiconj (U : X → X) (F : M → M) (ℓ : ℕ → X → M) (Ω : ℕ → Set X) : Prop :=
  ∀ t, ∀ s ∈ Ω t, ℓ (t + 1) (U s) = F (ℓ t s)

/-- The factor map's fiber at `t`: the image of the system's fiber at `t` under the factor map.
Surjectivity onto this set is definitional, not a further clause. -/
def imageFiber (ℓ : ℕ → X → M) (Ω : ℕ → Set X) (t : ℕ) : Set M := ℓ t '' Ω t

/-! ## Factor closure -/

/-- **Factor closure**, the module's reason to exist: a factor map of a nonautonomous system is
itself a nonautonomous system ([RuleSpace] §2 Proposition 2.5), its own fibers — the images of the
system's — positively invariant under the factor map's law `F`. One line from the semiconjugacy: a
point of the image steps, via `F`, to the image of the system's stepped point. -/
theorem positivelyInvariant_imageFiber {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hadv : PositivelyInvariant U Ω) (hsq : Semiconj U F ℓ Ω) :
    PositivelyInvariant F (imageFiber ℓ Ω) := by
  rintro t _ ⟨s, hs, rfl⟩
  exact ⟨U s, hadv t s hs, hsq t s hs⟩

/-! ## Eventual merging and its quotient -/

/-- **Eventual merging**: two states whose orbits are eventually identified by some common number of
steps. An equivalence relation (`Merges.refl` / `Merges.symm` / `Merges.trans`), and the object the
whole file is built on: it needs nothing beyond `U` itself, no factor map and no law. -/
def Merges (U : X → X) (s s' : X) : Prop := ∃ k, U^[k] s = U^[k] s'

/-- If two iterates agree at some exponent, they agree at every larger exponent — the monotonicity
that makes `Merges` transitive and that peels an injective law's iterate back to its base case. -/
private theorem merges_of_iterate_eq_ge {U : X → X} {s s' : X} {k m : ℕ}
    (h : U^[k] s = U^[k] s') (hm : k ≤ m) : U^[m] s = U^[m] s' := by
  have e : m - k + k = m := Nat.sub_add_cancel hm
  calc U^[m] s = U^[m - k] (U^[k] s) := by rw [← Function.iterate_add_apply, e]
    _ = U^[m - k] (U^[k] s') := by rw [h]
    _ = U^[m] s' := by rw [← Function.iterate_add_apply, e]

theorem Merges.refl (U : X → X) (s : X) : Merges U s s := ⟨0, rfl⟩

theorem Merges.symm {U : X → X} {s s' : X} (h : Merges U s s') : Merges U s' s :=
  ⟨h.choose, h.choose_spec.symm⟩

theorem Merges.trans {U : X → X} {s s' s'' : X} (h1 : Merges U s s') (h2 : Merges U s' s'') :
    Merges U s s'' := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  exact ⟨max k k', by
    rw [merges_of_iterate_eq_ge hk (le_max_left k k'),
      merges_of_iterate_eq_ge hk' (le_max_right k k')]⟩

/-- The setoid of eventual merging, over an arbitrary update `U`. -/
def mergesSetoid (U : X → X) : Setoid X where
  r := Merges U
  iseqv := ⟨Merges.refl U, Merges.symm, Merges.trans⟩

/-- The quotient by eventual merging — the canonical carrier every factor map with an injective law
factors through (`exists_mergeMk_injective`). Reducible: kept transparent so tactics see through it
to the underlying `Quotient` the way they see through any other type synonym in this development. -/
abbrev MergeQuot (U : X → X) : Type _ := Quotient (mergesSetoid U)

/-- The quotient map, spelled out so call sites need not spell the setoid. Reducible, for the same
reason as `MergeQuot`. -/
abbrev mergeMk (U : X → X) (s : X) : MergeQuot U := Quotient.mk (mergesSetoid U) s

/-- `U` respects eventual merging: stepping both sides by `U` preserves any common iterate one step
later. What makes `mergeLaw` well-defined. -/
theorem merge_respects (U : X → X) :
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
def mergeLaw (U : X → X) : MergeQuot U → MergeQuot U := Quotient.map U (merge_respects U)

@[simp] theorem mergeLaw_mergeMk (U : X → X) (s : X) : mergeLaw U (mergeMk U s) = mergeMk U (U s) :=
  Quotient.map_mk U (merge_respects U) s

/-- **The induced law is injective, with no hypothesis at all**: this is the whole reason eventual
merging yields a factor map with an injective law rather than merely a factor map. -/
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

/-- **The semiconjugacy, at every nonautonomous set, with no hypothesis**: the quotient map is a
time-independent factor map that closes the semiconjugacy against `mergeLaw` identically
([RuleSpace] §2 Proposition 2.6(i)). -/
theorem semiconj_merge (U : X → X) (Ω : ℕ → Set X) :
    Semiconj U (mergeLaw U) (fun _ s => mergeMk U s) Ω := by
  intro _t s _
  exact (mergeLaw_mergeMk U s).symm

/-! ## Universality: every semiconjugate factor map with an injective law factors through -/

/-- The system's forward orbit stays in its fibers: `k` steps from a state in the fiber at `t`
lands in the fiber at `t + k`. Repeated `PositivelyInvariant`. -/
private theorem mem_fiber_of_positivelyInvariant {U : X → X} {Ω : ℕ → Set X}
    (hadv : PositivelyInvariant U Ω)
    {t : ℕ} {s : X} (hs : s ∈ Ω t) : ∀ k, U^[k] s ∈ Ω (t + k) := by
  intro k
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have h := hadv (t + k) (U^[k] s) ih
    rw [Function.iterate_succ_apply']
    exact h

/-- The iterated semiconjugacy: `k` system steps, read `k` times later, is `k` law steps applied to
the current value. Needs `PositivelyInvariant` to keep the intermediate points in their fibers. -/
private theorem Semiconj.iterate {U : X → X} {F : M → M} {ℓ : ℕ → X → M}
    {Ω : ℕ → Set X}
    (hadv : PositivelyInvariant U Ω) (hsq : Semiconj U F ℓ Ω)
    {t : ℕ} {s : X} (hs : s ∈ Ω t) :
    ∀ k, ℓ (t + k) (U^[k] s) = F^[k] (ℓ t s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hmem : U^[k] s ∈ Ω (t + k) := mem_fiber_of_positivelyInvariant hadv hs k
    have hstep := hsq (t + k) (U^[k] s) hmem
    have hidx : t + (k + 1) = t + k + 1 := rfl
    calc ℓ (t + (k + 1)) (U^[k + 1] s)
        = ℓ (t + k + 1) (U (U^[k] s)) := by rw [hidx, Function.iterate_succ_apply']
      _ = F (ℓ (t + k) (U^[k] s)) := hstep
      _ = F (F^[k] (ℓ t s)) := by rw [ih]
      _ = F^[k + 1] (ℓ t s) := (Function.iterate_succ_apply' F k (ℓ t s)).symm

/-- **Universality** ([RuleSpace] §2 Proposition 2.6(ii)): any semiconjugate factor map with an
INJECTIVE law is merge-invariant per fiber — two states in the same fiber that eventually merge are
mapped identically. So every such factor map factors through the merge quotient. -/
theorem Semiconj.merges_invariant {U : X → X} {F : M → M} {ℓ : ℕ → X → M}
    {Ω : ℕ → Set X}
    (hF : Function.Injective F) (hadv : PositivelyInvariant U Ω)
    (hsq : Semiconj U F ℓ Ω) :
    ∀ t, ∀ s ∈ Ω t, ∀ s' ∈ Ω t, Merges U s s' → ℓ t s = ℓ t s' := by
  rintro t s hs s' hs' ⟨k, hk⟩
  have h1 := Semiconj.iterate hadv hsq hs k
  have h2 := Semiconj.iterate hadv hsq hs' k
  rw [hk, h2] at h1
  exact hF.iterate k h1.symm

/-- **The fiber at `t` of any semiconjugate factor map with an injective law injects into the merge
classes over `Ω t`** ([RuleSpace] §2 Proposition 2.6(ii)): the merge quotient is the maximal such
factor map, so its represented classes ceiling every other one's. -/
theorem exists_mergeMk_injective {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hF : Function.Injective F) (hadv : PositivelyInvariant U Ω)
    (hsq : Semiconj U F ℓ Ω) (t : ℕ) :
    ∃ g : ↥(imageFiber ℓ Ω t) → MergeQuot U,
      (∀ m, g m ∈ imageFiber (fun _ s => mergeMk U s) Ω t) ∧ Function.Injective g := by
  classical
  choose s hsmem hseq using fun m : ↥(imageFiber ℓ Ω t) => m.2
  refine ⟨fun m => mergeMk U (s m), fun m => ⟨s m, hsmem m, rfl⟩, ?_⟩
  intro m m' hmm'
  have hmerges : Merges U (s m) (s m') := Quotient.exact hmm'
  have heq := Semiconj.merges_invariant hF hadv hsq t (s m) (hsmem m) (s m')
    (hsmem m') hmerges
  exact Subtype.ext (by rw [← hseq m, ← hseq m', heq])

/-! ## The merge classes represented in the fibers -/

/-- **The classes of the merge quotient represented in the fiber at `t`** ([RuleSpace] §2
Definition 2.2): the merge quotient's own fiber — the classes of the states `Ω` admits at `t`.
Reuses `imageFiber` directly; no new machinery. -/
def mergeFiber (U : X → X) (Ω : ℕ → Set X) (t : ℕ) : Set (MergeQuot U) :=
  imageFiber (fun _ s => mergeMk U s) Ω t

/-- **Positive invariance of the represented classes** ([RuleSpace] §2 Proposition 2.6(iii)):
`mergeLaw` carries the classes represented in the fiber at `t` into those represented at `t + 1`,
since the quotient is itself a factor map of `(U, Ω)` (`semiconj_merge`) and factor
closure (`positivelyInvariant_imageFiber`) applies with no further hypothesis. -/
theorem positivelyInvariant_mergeFiber {U : X → X} {Ω : ℕ → Set X}
    (hadv : PositivelyInvariant U Ω) :
    PositivelyInvariant (mergeLaw U) (mergeFiber U Ω) :=
  positivelyInvariant_imageFiber hadv (semiconj_merge U Ω)

/-- The fiber-to-fiber map is injective — `mergeLaw` never collapses distinct classes, at any
time. -/
theorem mergeFiber_injOn (U : X → X) (Ω : ℕ → Set X) (t : ℕ) :
    Set.InjOn (mergeLaw U) (mergeFiber U Ω t) :=
  (mergeLaw_injective U).injOn

end Nonautonomous
