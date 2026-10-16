module

public import Nonautonomous.MergeQuotient
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Antichain
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The width of the reachability preorder on the merge quotient
([RuleSpace] §2 Definition 2.2, Proposition 2.7 and Proposition 2.8)

A count of the classes of the merge quotient represented in the fiber does not measure how much
state a system must keep: successor on the naturals has an unbounded set of represented classes
too, and its content is a clock, not a store. This file defines the quantity that does measure it,
and proves its shape.

On the merge quotient (`Nonautonomous.MergeQuot`) write `q` reaches `q'` when some number of
`mergeLaw` steps carries `q` to `q'`; this is a preorder. Its **width** — the size of its largest
antichain, the standard width of an order — at time `t` is taken inside the classes of the merge
quotient represented in the fiber, `mergeFiber U Ω t`: the largest set of represented classes no
one of which is a later version of another.

## Main results

* `Reaches` — the reachability relation `mergeLaw` induces on the merge quotient.
* `Reaches.mergeLaw` — `mergeLaw` is monotone for `Reaches`: the one further fact, beyond
  `Nonautonomous.mergeFiber_injOn`'s fiber-to-fiber injection, that a growing carrier's law needs.
* `mergeLaw_iterate_mergeMk` / `reaches_mergeMk_iterate` — the iterate transport `mergeLaw`
  induces on classes, and its `Reaches` corollary: every consumer that computes `Reaches` along a
  representative's orbit factors through these two lines.
* `width_le_encard_mergeFiber` — the generic width inequality, no antichain hypothesis
  consumed: every antichain witnessing the width is a subset of the represented classes.
* `width_eq_encard_of_is_root_antichain` — the class-level root-antichain width lemma: given a
  subset of a fiber that is already an antichain and which every class of the fiber reaches, the
  width equals that subset's cardinality exactly — no injectivity of the update and no notion of
  "component" enters either half. `width_eq_encard_of_root_set` is its corollary at a *state*-
  level root set `R` (`Q := mergeMk U '' R`); `PermutiveWidth.lean`'s exact-width capstones
  instantiate the corollary at a concrete root set.
* `exists_is_root_antichain_of_finite` / `exists_is_root_antichain_of_finite_fiber` — **a root
  antichain always exists at a finite fiber** ([RuleSpace] §2 Proposition 2.8(ii)):
  descend the reachability preorder to its minimal elements and pick one representative per
  mutual-reachability class among them.
* `width_eq_encard_canonical_of_antisymm_on` — the "how to find it" half, under an antisymmetry
  hypothesis: the root antichain is exactly the classes of the fiber no OTHER such class reaches,
  the form every growing instance this package carries actually sits at. Guard (a),
  `exists_canonical_set_empty_pos_width`, shows antisymmetry is load-bearing: at a finite
  system, the degenerate case, the canonical set is empty while the width is positive.
* `pos_width_not_exists_is_root_antichain_int_succ` — **guard (b)**: the successor system on `ℤ`
  pins the finiteness hypothesis of `exists_is_root_antichain_of_finite` — a bi-infinite chain has a
  positive width but no root antichain at all, so finiteness is not decorative.
* `width` — the width, `ℕ∞`-valued (`Set.encard`, not `Set.ncard`: an antichain inside an
  infinite set of represented classes can itself be infinite, and `ℕ`'s supremum of an unbounded set
  is silently `0`).
* `width_mono` — **monotone**, with no hypothesis on the system beyond `PositivelyInvariant`:
  `mergeLaw`'s
  bare injectivity carries an antichain to an antichain of the same size one time later.
* `width_mono_of_subset` — **monotone in the nonautonomous set, at a single time**: widening `Ω t`
  alone can only widen the width there, with no hypothesis at all — `GrowingWidth.lean`'s reason to
  consume it.
* `width_nat_succ_eq_one` — **the width of a clock**: the successor system's represented classes
  form a chain at any nonautonomous set, so its width is `1` throughout, at both a nested and a
  level admission schedule, while the set of represented classes itself is unbounded.
* `exists_conservation_factor_extent_gt_width` — **the ceiling does not hold in general**: a
  factor map with an injective law whose own fiber image is antichain-shaped under its own law can
  still exceed the width — a two-line counterexample at the nested clock, reported rather
  than forced.
* `mergeFiber_nat_succ_fast_clock_encard` — **the guard family**: the fast counter's represented
  classes are in bijection with `Bool^t` at every time, while its width is `1` throughout, so the
  count of represented classes decides nothing.

## Scope

**Not a dichotomy — a separation**: the ceiling half (an antichain-shaped factor map's image is at
most the width) is FALSE in general (`exists_conservation_factor_extent_gt_width`),
and the raw count of represented classes decides neither direction (the clock and the
guard family). Recovering the ceiling would need a hypothesis beyond "antichain-shaped under its
own law" — not supplied here.

`width`'s value is a property of the *presented* system `(X, U, Ω)`, not of `(X, U)` alone: a
system presented by its own trajectory (singleton fibers) has width `1` whatever it is, since there
is nothing co-present to store. This is not a defect — `mergeFiber` already depends on `Ω`, and
every instance below presents a system by a genuine nonautonomous set rather than by its bare orbit.

**Root sets.** `exists_is_root_antichain_of_finite`'s existence half and
`width_eq_encard_canonical_of_antisymm_on`'s "how to find it" half are independent: the first
needs only finiteness of the fiber, the second needs `Reaches` antisymmetric on the fiber as well,
and neither hypothesis is dropped for free — guard (a) refutes the canonical description without
antisymmetry, guard (b) refutes existence itself without finiteness. The count a root antichain
supplies is of minimal *mutual-reachability classes*, not of minimal states or of minimal classes:
at a finite system (a constant nonautonomous set over a finite carrier, the degenerate case)
`mergeLaw` is a bijection of the merge quotient, so every class is periodic and
none is canonical in the antisymmetric sense, which is exactly guard (a)'s content. No numbered
statement is claimed here: the order-theoretic content — a preorder generated by a function has
chain up-sets, and the maximum antichain of a finite such preorder is its minimal-class count — is
elementary and unattributed.
-/


@[expose] public section

namespace Nonautonomous


variable {X : Type*}

/-! ## The reachability relation, and the width -/

/-- **The reachability relation** `mergeLaw` induces on the merge quotient: `q` reaches `q'` when
some number of `mergeLaw` steps carries `q` to `q'`. Reflexive (`Reaches.refl`) and transitive
(`Reaches.trans`), so a preorder. -/
def Reaches (U : X → X) (q q' : MergeQuot U) : Prop := ∃ j, (mergeLaw U)^[j] q = q'

/-- **`Reaches` is reflexive**: zero steps. -/
theorem Reaches.refl (U : X → X) (q : MergeQuot U) : Reaches U q q := ⟨0, rfl⟩

/-- **`Reaches` is transitive**: sum the witnessing exponents. -/
theorem Reaches.trans {U : X → X} {p q r : MergeQuot U} (h1 : Reaches U p q) (h2 : Reaches U q r) :
    Reaches U p r := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨j + i, by rw [Function.iterate_add_apply, hi, hj]⟩

/-- **`mergeLaw` is monotone for reachability**: if `q` reaches `q'`, then `mergeLaw U q` reaches
`mergeLaw U q'` — `mergeLaw` commuting with its own iterates. The one further fact a growing
carrier's fiber-to-fiber law needs beyond `Nonautonomous.mergeFiber_injOn` and
`Nonautonomous.positivelyInvariant_mergeFiber`, and a fixed carrier does not: a bound on how much a
fiber's represented classes can be *saved* by the growing law is NOT a further consequence of this
fact alone — it is false in general, at the widths this file's own witnesses compute. -/
theorem Reaches.mergeLaw {U : X → X} {q q' : MergeQuot U} (h : Reaches U q q') :
    Reaches U (mergeLaw U q) (mergeLaw U q') := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hj]

/-- **The width at time `t`**: the extended-natural cardinality of the largest antichain of
`Reaches` inside the classes represented in the fiber, `mergeFiber U Ω t`. Valued in `ℕ∞`
(`Set.encard`) rather than `ℕ`: an antichain inside an infinite set of represented classes can
itself be infinite, and `ℕ`'s supremum of an unbounded set is silently `0`, which would corrupt
exactly the unbounded case. -/
noncomputable def width (U : X → X) (Ω : ℕ → Set X) (t : ℕ) : ℕ∞ :=
  sSup (Set.encard '' {A : Set (MergeQuot U) | A ⊆ mergeFiber U Ω t ∧ IsAntichain (Reaches U) A})

/-! ## Monotonicity: `mergeLaw`'s bare injectivity is the whole argument -/

/-- **Peeling one step**: if `mergeLaw U a` reaches `mergeLaw U b`, then `a` already reaches `b` —
`mergeLaw_injective` peeling the outer application off the witnessing iterate. The whole reason an
antichain's `mergeLaw`-image is again an antichain. -/
private theorem reaches_of_reaches_mergeLaw {U : X → X} {a b : MergeQuot U}
    (h : Reaches U (mergeLaw U a) (mergeLaw U b)) : Reaches U a b := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, mergeLaw_injective U ?_⟩
  calc mergeLaw U ((mergeLaw U)^[j] a) = (mergeLaw U)^[j + 1] a :=
        (Function.iterate_succ_apply' (mergeLaw U) j a).symm
    _ = (mergeLaw U)^[j] (mergeLaw U a) := Function.iterate_succ_apply (mergeLaw U) j a
    _ = mergeLaw U b := hj

/-- **`mergeLaw`'s image of an antichain is an antichain of the same size**: the
injective law never collapses distinct classes, and `reaches_of_reaches_mergeLaw` shows it never
manufactures a fresh comparability either. -/
private theorem isAntichain_image_mergeLaw {U : X → X} {A : Set (MergeQuot U)}
    (hA : IsAntichain (Reaches U) A) : IsAntichain (Reaches U) (mergeLaw U '' A) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne hreach
  exact hA ha hb (fun hab => hne (hab ▸ rfl)) (reaches_of_reaches_mergeLaw hreach)

/-- **Monotone, with no hypothesis on the system beyond `PositivelyInvariant`**: the image of an
antichain in the fiber at `t` under `mergeLaw` is an antichain in the fiber at `t + 1` of the same
cardinality, so the supremum only grows. -/
theorem width_mono {U : X → X} {Ω : ℕ → Set X} (hadv : PositivelyInvariant U Ω) :
    Monotone (width U Ω) := by
  apply monotone_nat_of_le_succ
  intro t
  apply sSup_le
  rintro _ ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
  have hsub : mergeLaw U '' A ⊆ mergeFiber U Ω (t + 1) := by
    rintro _ ⟨a, ha, rfl⟩
    exact positivelyInvariant_mergeFiber hadv t a (hAsub ha)
  have himg : (mergeLaw U '' A).encard = A.encard :=
    Function.Injective.encard_image (mergeLaw_injective U) A
  rw [← himg]
  exact le_sSup ⟨mergeLaw U '' A, ⟨hsub, isAntichain_image_mergeLaw hAanti⟩, rfl⟩

/-- **Monotone in the nonautonomous set, at a single time**: widening the admitted states at time
`t` alone can only widen the width there — `mergeFiber` is `mergeMk U`'s image of the state fiber
(`Set.image_mono`), and an antichain inside the narrower set of represented classes is still a
subset of the wider one, so the supremum can only grow. `Nonautonomous.PositivelyInvariant` plays no
role here: unlike `width_mono`, which moves `t` forward under one fixed `Ω`, this moves `Ω` at a
FIXED `t`, and needs nothing beyond monotonicity of the image. `GrowingWidth.lean`'s
`growingWidth_le_width` is this lemma's reason to exist: that file restricts `Ω` by intersecting
it with a further set, and this is the inequality that turns the restriction into a `≤` against the
unrestricted width. -/
theorem width_mono_of_subset {U : X → X} {Ω Ω' : ℕ → Set X} {t : ℕ} (h : Ω t ⊆ Ω' t) :
    width U Ω t ≤ width U Ω' t := by
  apply sSup_le
  rintro _ ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
  exact le_sSup ⟨A, ⟨hAsub.trans (Set.image_mono h), hAanti⟩, rfl⟩

/-! ## A reusable fact: `mergeLaw` iterated is `mergeMk` of `U` iterated -/

/-- `mergeLaw`'s iterate along a class is the class of `U`'s iterate along a representative — the
handle every instance below computes `Reaches` through. Public: `ForwardImages.lean`'s antichain
argument destructs a `Reaches` witness through this identity directly. -/
theorem mergeLaw_iterate_mergeMk (U : X → X) (j : ℕ) (s : X) :
    (mergeLaw U)^[j] (mergeMk U s) = mergeMk U (U^[j] s) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, mergeLaw_mergeMk, Function.iterate_succ_apply']

/-- **`mergeMk` of an iterate is `Reaches`**: the one-line corollary `PermutiveWidth.lean`'s
antichain witness converts through. -/
theorem reaches_mergeMk_iterate (U : X → X) (s : X) (j : ℕ) :
    Reaches U (mergeMk U s) (mergeMk U (U^[j] s)) :=
  ⟨j, mergeLaw_iterate_mergeMk U j s⟩

/-- **The generic width inequality**: every antichain witnessing the width is a subset of
the represented classes, so its cardinality never exceeds their number — no antichain hypothesis
consumed, a fact about the represented classes alone. `ForwardImages.lean`'s bound is exactly this
composed with a bound on their number. -/
theorem width_le_encard_mergeFiber (U : X → X) (Ω : ℕ → Set X) (t : ℕ) :
    width U Ω t ≤ (mergeFiber U Ω t).encard := by
  apply sSup_le
  rintro _ ⟨A, ⟨hAsub, -⟩, rfl⟩
  exact Set.encard_mono hAsub

/-- **The exact width at a class-level root antichain**: given `Q ⊆ mergeFiber U Ω t` that is
already an antichain (`hanti`) and which every time-`t` class reaches (`hcover`), the width is
exactly `Q`'s own cardinality. Neither half consumes injectivity of `U`, and no notion of
"component" is ever defined: `≥` is `le_sSup` at `Q` itself, and `≤` sends each element of a
competing antichain `A` to a chosen member of `Q` beneath it, an injective map on `A` because two
elements sharing the same chosen root would be `Reaches`-comparable to each other, contradicting
`A`'s own antichain property. `width_eq_encard_of_root_set` below is the corollary at
`Q := mergeMk U '' R` for a *state*-level root set `R`: the more general, class-level form is what
`exists_is_root_antichain_of_finite`'s existence argument actually produces, since its witness is
not handed to it as the image of a chosen set of states. -/
theorem width_eq_encard_of_is_root_antichain {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    {Q : Set (MergeQuot U)} (hsub : Q ⊆ mergeFiber U Ω t)
    (hanti : IsAntichain (Reaches U) Q)
    (hcover : ∀ q ∈ mergeFiber U Ω t, ∃ p ∈ Q, Reaches U p q) :
    width U Ω t = Q.encard := by
  classical
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
    set f : MergeQuot U → MergeQuot U := fun a =>
      if h : ∃ r ∈ Q, Reaches U r a then h.choose else a with hf_def
    have hex : ∀ {a : MergeQuot U}, a ∈ A → ∃ r ∈ Q, Reaches U r a := by
      intro a ha
      exact hcover a (hAsub ha)
    have hfR : ∀ a ∈ A, f a ∈ Q := by
      intro a ha
      rw [hf_def]
      simp only [dite_eq_left (hex ha)]
      exact (hex ha).choose_spec.1
    have hfReach : ∀ a ∈ A, Reaches U (f a) a := by
      intro a ha
      rw [hf_def]
      simp only [dite_eq_left (hex ha)]
      exact (hex ha).choose_spec.2
    have hfInj : Set.InjOn f A := by
      intro a ha b hb hab
      have hra := hfReach a ha
      rw [hab] at hra
      obtain ⟨i, hi⟩ := hra
      obtain ⟨j, hj⟩ := hfReach b hb
      rcases le_total i j with hij | hij
      · have e : (mergeLaw U)^[j - i] a = b := by
          rw [← hi, ← Function.iterate_add_apply, Nat.sub_add_cancel hij]
          exact hj
        by_contra hne
        exact hAanti ha hb hne ⟨j - i, e⟩
      · have e : (mergeLaw U)^[i - j] b = a := by
          rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel hij]
          exact hi
        by_contra hne
        exact hAanti hb ha (Ne.symm hne) ⟨i - j, e⟩
    calc A.encard = (f '' A).encard := hfInj.encard_image.symm
      _ ≤ Q.encard := Set.encard_mono (Set.image_subset_iff.mpr hfR)
  · exact le_sSup ⟨Q, ⟨hsub, hanti⟩, rfl⟩

/-- **The exact width at a root set**: given `R ⊆ Ω t` whose `mergeMk`-image is already an
antichain (`hanti`) and which every time-`t` state reaches (`hcover`), the width is exactly that
image's cardinality. The corollary of `width_eq_encard_of_is_root_antichain` at
`Q := mergeMk U '' R`. `PermutiveWidth.lean`'s exact-count capstones instantiate this at a
concrete root set. -/
theorem width_eq_encard_of_root_set {U : X → X} {Ω : ℕ → Set X} {t : ℕ} {R : Set X}
    (hsub : R ⊆ Ω t) (hanti : IsAntichain (Reaches U) (mergeMk U '' R))
    (hcover : ∀ s ∈ Ω t, ∃ r ∈ R, Reaches U (mergeMk U r) (mergeMk U s)) :
    width U Ω t = (mergeMk U '' R).encard := by
  apply width_eq_encard_of_is_root_antichain (Set.image_mono hsub) hanti
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨r, hr, hreach⟩ := hcover s hs
  exact ⟨mergeMk U r, ⟨r, hr, rfl⟩, hreach⟩

/-! ## Root sets: existence at a finite fiber -/

/-- **A root antichain always exists at a finite fiber**: a witness for
`width_eq_encard_of_is_root_antichain`'s hypotheses, built by descending the reachability
preorder to its minimal elements and picking one representative per mutual-reachability class
among them. Distinct such representatives are incomparable: comparable-and-mutual puts them in one
class, comparable-and-not forces the target's own minimality to make it mutual after all — so no
two representatives of distinct classes can reach one another. -/
theorem exists_is_root_antichain_of_finite {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (hfin : (mergeFiber U Ω t).Finite) :
    ∃ Q ⊆ mergeFiber U Ω t, IsAntichain (Reaches U) Q ∧
      ∀ q ∈ mergeFiber U Ω t, ∃ p ∈ Q, Reaches U p q := by
  classical
  let : Preorder (MergeQuot U) :=
    { le := Reaches U, le_refl := Reaches.refl U, le_trans := fun _ _ _ => Reaches.trans }
  set S := mergeFiber U Ω t with hS
  set M : Set (MergeQuot U) := {p | p ∈ S ∧ Minimal (· ∈ S) p} with hM
  let mutSetoid : Setoid (MergeQuot U) :=
    { r := fun p q => Reaches U p q ∧ Reaches U q p
      iseqv := ⟨fun p => ⟨Reaches.refl U p, Reaches.refl U p⟩,
        fun h => ⟨h.2, h.1⟩,
        fun h1 h2 => ⟨Reaches.trans h1.1 h2.1, Reaches.trans h2.2 h1.2⟩⟩ }
  let sM : Setoid ↥M := mutSetoid.comap (Subtype.val : ↥M → MergeQuot U)
  set Q : Set (MergeQuot U) := Set.range (fun c : Quotient sM => (Quotient.out c : ↥M).1) with hQ
  refine ⟨Q, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact (Quotient.out c : ↥M).2.1
  · rintro _ ⟨c1, rfl⟩ _ ⟨c2, rfl⟩ hne hreach
    apply hne
    have hp1 := (Quotient.out c1 : ↥M).2
    have hp2 := (Quotient.out c2 : ↥M).2
    have hmut : Reaches U (Quotient.out c2 : ↥M).1 (Quotient.out c1 : ↥M).1 :=
      hp2.2.le_of_le hp1.1 hreach
    have hrel : sM (Quotient.out c1 : ↥M) (Quotient.out c2 : ↥M) :=
      (Setoid.comap_rel _ _ _ _).mpr ⟨hreach, hmut⟩
    have hc : (Quotient.mk sM (Quotient.out c1 : ↥M) : Quotient sM) = Quotient.mk sM
        (Quotient.out c2 : ↥M) := Quotient.sound hrel
    rw [Quotient.out_eq, Quotient.out_eq] at hc
    exact congrArg (fun c : Quotient sM => (Quotient.out c : ↥M).1) hc
  · intro q hq
    obtain ⟨p, hple, hpmin⟩ := hfin.exists_le_minimal hq
    have hpM : p ∈ M := ⟨hpmin.1, hpmin⟩
    set c : Quotient sM := Quotient.mk sM (⟨p, hpM⟩ : ↥M) with hc_def
    have hrel : sM (Quotient.out c : ↥M) (⟨p, hpM⟩ : ↥M) := Quotient.exact (Quotient.out_eq c)
    have hreach : Reaches U (Quotient.out c : ↥M).1 p :=
      ((Setoid.comap_rel _ _ _ _).mp hrel).1
    exact ⟨(Quotient.out c : ↥M).1, ⟨c, rfl⟩, Reaches.trans hreach hple⟩

/-- **The corollary at a finite state fiber**: the finiteness clause of a nonautonomous system is
on `Ω t`, not directly on `mergeFiber U Ω t`, and `mergeFiber` is `mergeMk U`'s image of it, so a
root antichain exists whenever the *state* fiber is finite — the form the system's finiteness
clause actually supplies. -/
theorem exists_is_root_antichain_of_finite_fiber {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (hfin : (Ω t).Finite) :
    ∃ Q ⊆ mergeFiber U Ω t, IsAntichain (Reaches U) Q ∧
      ∀ q ∈ mergeFiber U Ω t, ∃ p ∈ Q, Reaches U p q :=
  exists_is_root_antichain_of_finite (hfin.image _)

/-! ## The canonical description, under antisymmetry -/

/-- **The canonical description, under antisymmetry**: at a finite fiber where `Reaches` is
antisymmetric, the root antichain is exactly the represented classes no OTHER represented class
reaches — the
"how to find it" half, and the form every growing instance this package carries actually sits at
(`PermutiveWidth.rootSet`; the case where `Reaches` happens to be
antisymmetric on the whole quotient is the simplest). Antisymmetry is load-bearing, not cosmetic:
guard (a) below refutes this description at the degenerate case, the finite system, where the
canonical set is empty while the width is positive. -/
theorem width_eq_encard_canonical_of_antisymm_on {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (hfin : (mergeFiber U Ω t).Finite)
    (hasymm : ∀ p ∈ mergeFiber U Ω t, ∀ q ∈ mergeFiber U Ω t,
        Reaches U p q → Reaches U q p → p = q) :
    width U Ω t
      = {q ∈ mergeFiber U Ω t |
          ∀ p ∈ mergeFiber U Ω t, Reaches U p q → p = q}.encard := by
  classical
  let : Preorder (MergeQuot U) :=
    { le := Reaches U, le_refl := Reaches.refl U, le_trans := fun _ _ _ => Reaches.trans }
  set S := mergeFiber U Ω t with hS
  set C : Set (MergeQuot U) := {q ∈ S | ∀ p ∈ S, Reaches U p q → p = q} with hC
  apply width_eq_encard_of_is_root_antichain
  · exact fun q hq => hq.1
  · rintro p ⟨hpS, -⟩ q ⟨hqS, hq⟩ hne hpq
    exact hne (hq p hpS hpq)
  · intro q hq
    obtain ⟨p, hple, hpmin⟩ := hfin.exists_le_minimal hq
    refine ⟨p, ⟨hpmin.1, ?_⟩, hple⟩
    intro y hyS hyp
    exact hasymm y hyS p hpmin.1 hyp (hpmin.le_of_le hyS hyp)

/-! ## Guard families -/

/-- **Guard (a)**: the two-state swap pins `width_eq_encard_canonical_of_antisymm_on`'s
antisymmetry hypothesis. `Bool.not` is injective, so `Merges` is equality and the merge quotient
over the constant nonautonomous set has exactly the two classes `mergeMk true` and `mergeMk false`,
each reaching the other in one step (`Bool.not` swaps them) — so the canonical set is EMPTY while
the width is positive. This is the smallest witness for the degenerate case, the
finite system: there `mergeLaw` is an injective self-map of a finite quotient, hence a bijection,
hence every class is periodic, so the canonical set is always empty there. -/
theorem exists_canonical_set_empty_pos_width :
    ∃ (U : Bool → Bool) (Ω : ℕ → Set Bool) (t : ℕ),
      {q ∈ mergeFiber U Ω t | ∀ p ∈ mergeFiber U Ω t, Reaches U p q → p = q} = ∅ ∧
      (1 : ℕ∞) ≤ width U Ω t := by
  classical
  refine ⟨Bool.not, fun _ => Set.univ, 0, ?_, ?_⟩
  · have hBoolInj : Function.Injective Bool.not := by decide
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨-, hq⟩
    induction q using Quotient.inductionOn with
    | _ s =>
      cases s with
      | true =>
        have hreach : Reaches Bool.not (mergeMk Bool.not false) (mergeMk Bool.not true) :=
          ⟨1, by simp⟩
        have heq := hq (mergeMk Bool.not false) ⟨false, Set.mem_univ _, rfl⟩ hreach
        obtain ⟨k, hk⟩ := Quotient.exact heq
        exact absurd (hBoolInj.iterate k hk) (by decide)
      | false =>
        have hreach : Reaches Bool.not (mergeMk Bool.not true) (mergeMk Bool.not false) :=
          ⟨1, by simp⟩
        have heq := hq (mergeMk Bool.not true) ⟨true, Set.mem_univ _, rfl⟩ hreach
        obtain ⟨k, hk⟩ := Quotient.exact heq
        exact absurd (hBoolInj.iterate k hk) (by decide)
  · exact le_sSup ⟨{mergeMk Bool.not true}, ⟨by
      rintro _ rfl; exact ⟨true, Set.mem_univ _, rfl⟩, IsAntichain.singleton⟩,
      Set.encard_singleton _⟩

/-- **Guard (b)**: the successor system on `ℤ` pins `exists_is_root_antichain_of_finite`'s
finiteness hypothesis. `(· + 1)` is injective, so `Merges` is again equality and the represented
classes form a bi-infinite chain — the width is positive — yet NO root antichain exists at all:
covering `mergeMk 0` supplies some `p = mergeMk m ∈ Q`, and covering `mergeMk (m - 1)` supplies some
`p' ∈ Q` reaching it, hence also reaching `p` one step later; `p' ≠ p` (their witnessing integers
differ, since `p'`'s integer is `≤ m - 1` while `p`'s is `m`, so they cannot be the same class of
an injective-law quotient with `p' ≠ p`) contradicts `Q`'s own antichain property. So a fiber can
carry a positive width and no root antichain at all — finiteness is not decorative. -/
theorem pos_width_not_exists_is_root_antichain_int_succ :
    (1 : ℕ∞) ≤ width (fun n : ℤ => n + 1) (fun _ => Set.univ) 0 ∧
    ¬ ∃ Q ⊆ mergeFiber (fun n : ℤ => n + 1) (fun _ => Set.univ) 0,
        IsAntichain (Reaches (fun n : ℤ => n + 1)) Q ∧
        ∀ q ∈ mergeFiber (fun n : ℤ => n + 1) (fun _ => Set.univ) 0,
          ∃ p ∈ Q, Reaches (fun n : ℤ => n + 1) p q := by
  set U : ℤ → ℤ := fun n => n + 1 with hUdef
  have hUinj : Function.Injective U := fun a b h => by simp only [hUdef] at h; omega
  have hiter : ∀ (j : ℕ) (x : ℤ), U^[j] x = x + (j : ℤ) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ n ih => intro x; rw [Function.iterate_succ_apply', ih]; simp [hUdef]; ring
  refine ⟨le_sSup ⟨{mergeMk U 0}, ⟨by
    rintro _ rfl; exact ⟨0, Set.mem_univ _, rfl⟩, IsAntichain.singleton⟩,
    Set.encard_singleton _⟩, ?_⟩
  rintro ⟨Q, hQsub, hQanti, hQcover⟩
  obtain ⟨p, hpQ, hpreach⟩ := hQcover (mergeMk U 0) ⟨0, Set.mem_univ _, rfl⟩
  obtain ⟨m, -, rfl⟩ := hQsub hpQ
  obtain ⟨p', hp'Q, hp'reach⟩ := hQcover (mergeMk U (m - 1)) ⟨m - 1, Set.mem_univ _, rfl⟩
  have hstep : Reaches U (mergeMk U (m - 1)) (mergeMk U m) := by
    have := reaches_mergeMk_iterate U (m - 1) 1
    rwa [show U^[1] (m - 1) = m from by rw [hiter]; push_cast; ring] at this
  have hp'p : Reaches U p' (mergeMk U m) := Reaches.trans hp'reach hstep
  have hne : p' ≠ mergeMk U m := by
    rintro rfl
    obtain ⟨j, hj⟩ := hp'reach
    rw [mergeLaw_iterate_mergeMk] at hj
    have hval : U^[j] m = m - 1 := mergeMk_injective_of_injective hUinj hj
    rw [hiter] at hval
    omega
  exact hQanti hp'Q hpQ hne hp'p

/-! ## A chain of represented classes has width one -/

/-- **The successor system's represented classes always form a chain**, at any nonautonomous set
whatsoever: `Merges Nat.succ` is equality (`Nat.succ` is injective), so on the quotient `Reaches`
is total — `Nat.le_total` transported through `mergeLaw_iterate_mergeMk`. -/
private theorem isChain_mergeFiber_nat_succ (Ω : ℕ → Set ℕ) (t : ℕ) :
    IsChain (Reaches Nat.succ) (mergeFiber Nat.succ Ω t) := by
  rintro _ ⟨s, -, rfl⟩ _ ⟨s', -, rfl⟩ hne
  rcases le_total s s' with h | h
  · exact Or.inl ⟨s' - s, by
      rw [mergeLaw_iterate_mergeMk, Nat.succ_iterate, Nat.add_sub_cancel' h]⟩
  · exact Or.inr ⟨s - s', by
      rw [mergeLaw_iterate_mergeMk, Nat.succ_iterate, Nat.add_sub_cancel' h]⟩

/-- **A chain of represented classes has width one, at any nonautonomous set** ([RuleSpace] §2
Proposition 2.7(ii)): chain-shaped represented classes have width exactly `1`, provided a state is
ever admitted. Instantiated below at
both a nested and a level presentation of the same successor system. -/
theorem width_nat_succ_eq_one {Ω : ℕ → Set ℕ} {t : ℕ} (hne : (Ω t).Nonempty) :
    width Nat.succ Ω t = 1 := by
  obtain ⟨s, hs⟩ := hne
  have hle : width Nat.succ Ω t ≤ 1 := by
    apply sSup_le
    rintro _ ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
    exact Set.encard_le_one_iff_subsingleton.mpr
      (subsingleton_of_isChain_of_isAntichain
        (IsChain.mono hAsub (isChain_mergeFiber_nat_succ Ω t)) hAanti)
  have hge : (1 : ℕ∞) ≤ width Nat.succ Ω t :=
    le_sSup ⟨{mergeMk Nat.succ s}, ⟨by
      rintro _ rfl; exact ⟨s, hs, rfl⟩, IsAntichain.singleton⟩,
      Set.encard_singleton _⟩
  exact le_antisymm hle hge

/-- `mergeMk Nat.succ` is injective: `Merges Nat.succ` is equality, `Nat.succ` being injective. -/
private theorem mergeMk_nat_succ_injective : Function.Injective (mergeMk Nat.succ) := by
  intro a b hab
  obtain ⟨k, hk⟩ := Quotient.exact hab
  simpa [Nat.succ_iterate] using hk

/-- **The represented classes, counted**: at any nonautonomous set, the successor system's fiber at
`t` represents exactly as many classes as the fiber itself admits states — `mergeMk` never
collapsing two of them. -/
private theorem mergeFiber_nat_succ_encard (Ω : ℕ → Set ℕ) (t : ℕ) :
    (mergeFiber Nat.succ Ω t).encard = (Ω t).encard :=
  Function.Injective.encard_image mergeMk_nat_succ_injective (Ω t)

/-- **Width one at a nested (level-set) nonautonomous set** ([RuleSpace] §2
Proposition 2.7(ii)): `Ω t = {n | n ≤ t}` presents the successor system with unboundedly many
represented classes (`t + 1` at time `t`) whose width is nonetheless `1` throughout — the slow
clock. -/
theorem width_nat_succ_slow_clock (t : ℕ) :
    width Nat.succ (fun t => Set.Iic t) t = 1 :=
  width_nat_succ_eq_one ⟨0, Set.mem_Iic.mpr (Nat.zero_le t)⟩

theorem mergeFiber_nat_succ_slow_clock_encard (t : ℕ) :
    (mergeFiber Nat.succ (fun t => Set.Iic t) t).encard = t + 1 := by
  rw [mergeFiber_nat_succ_encard]
  simp [Set.Finite.encard_eq_coe_toFinset_card (Set.finite_Iic t), Nat.card_Iic]

/-- **Width one at a level (fast) nonautonomous set** ([RuleSpace] §2
Proposition 2.7(ii) and (iii)): `Ω t = {n | n < 2 ^ t}` presents the SAME update at a faster
admission rate — `2 ^ t` classes at time `t`, again with width `1`. This is the fast counter,
computed as `width` rather than assumed: the represented classes are in bijection with `Bool ^ t`
(`mergeFiber_nat_succ_fast_clock_encard` below) while the width stays `1`, so the raw class count
does not measure the width. -/
theorem width_nat_succ_fast_clock (t : ℕ) :
    width Nat.succ (fun t => {n | n < 2 ^ t}) t = 1 :=
  width_nat_succ_eq_one ⟨0, pow_pos (show (0 : ℕ) < 2 by norm_num) t⟩

/-- **The guard family** ([RuleSpace] §2 Proposition 2.7(iii)): the fast counter's represented
classes are in bijection with `Bool ^ t`, i.e. `2 ^ t` classes at time `t`, at every time, while
`width_nat_succ_fast_clock` shows its width is `1` throughout. So the number of represented classes,
however large, decides nothing: the structural (antichain-width) quantity is the one that
measures co-presence. -/
theorem mergeFiber_nat_succ_fast_clock_encard (t : ℕ) :
    (mergeFiber Nat.succ (fun t => {n | n < 2 ^ t}) t).encard = 2 ^ t := by
  rw [mergeFiber_nat_succ_encard]
  have hfin : ({n | n < 2 ^ t} : Set ℕ).Finite := Set.finite_Iio (2 ^ t)
  rw [Set.Finite.encard_eq_coe_toFinset_card hfin]
  simp

/-! ## The ceiling does not hold in general -/

/-- The trivial law for the counterexample below: identity on `Bool`, injective for free. -/
private def ceilingCounterF : Bool → Bool := id

/-- The counterexample factor map: the parity of the elapsed time since a state was admitted. -/
private def ceilingCounterRead (t s : ℕ) : Bool := decide (Odd (t - s))

private theorem ceiling_counter_semiconj :
    Nonautonomous.Semiconj Nat.succ ceilingCounterF ceilingCounterRead
      (fun t => Set.Iic t) := by
  intro t s _
  simp only [ceilingCounterF, ceilingCounterRead, id, Nat.succ_sub_succ]

private theorem ceiling_counter_imageFiber_one :
    Nonautonomous.imageFiber ceilingCounterRead (fun t => Set.Iic t) 1 = {true, false} := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨s, hs, rfl⟩
    have hs1 : s ≤ 1 := Set.mem_Iic.mp hs
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs1 with rfl | rfl <;> simp [ceilingCounterRead]
  · rintro x hx
    rcases hx with rfl | rfl
    · exact ⟨0, Set.mem_Iic.mpr (by norm_num), by simp [ceilingCounterRead]⟩
    · exact ⟨1, Set.mem_Iic.mpr (by norm_num), by simp [ceilingCounterRead]⟩

/-- **The ceiling does not hold in general** ([RuleSpace] §2 Proposition 2.7(iv)): a factor map with
an injective law whose fiber image is antichain-shaped under its own law can still
exceed the width. At the nested successor system, `width ≡ 1` throughout
(`width_nat_succ_slow_clock`) — a chain — yet the trivial law `id` makes EVERY subset of
its image antichain-shaped (`id`'s own iterate never leaves a point), and the parity factor map's
image of the fiber at `1` is all of `Bool`, of cardinality `2`. So "the factor map's image is
antichain-shaped under its own law" is not by itself enough to bound it by `width`: recovering
a ceiling needs a hypothesis beyond that one, not supplied here. -/
theorem exists_conservation_factor_extent_gt_width :
    ∃ (F : Bool → Bool) (ℓ : ℕ → ℕ → Bool),
      Function.Injective F ∧
      Nonautonomous.Semiconj Nat.succ F ℓ (fun t => Set.Iic t) ∧
      IsAntichain (fun a b => ∃ j, F^[j] a = b)
        (Nonautonomous.imageFiber ℓ (fun t => Set.Iic t) 1) ∧
      width Nat.succ (fun t => Set.Iic t) 1 <
        (Nonautonomous.imageFiber ℓ (fun t => Set.Iic t) 1).encard :=
  ⟨ceilingCounterF, ceilingCounterRead, Function.injective_id, ceiling_counter_semiconj,
    fun a _ b _ hne ⟨j, hj⟩ => hne (by simpa [ceilingCounterF, Function.iterate_id] using hj), by
      rw [ceiling_counter_imageFiber_one, width_nat_succ_slow_clock,
        Set.encard_pair (by decide)]
      decide⟩

/-! ## A reusable fact about antichain-shaped represented classes -/

/-- A generic fact reusable elsewhere: the sup over subsets of a set that is ITSELF an antichain
is the set's own cardinality — no larger antichain can be found, and the set is a legal witness
for itself. -/
theorem width_eq_encard_of_isAntichain {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (h : IsAntichain (Reaches U) (mergeFiber U Ω t)) :
    width U Ω t = (mergeFiber U Ω t).encard := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨A, ⟨hAsub, -⟩, rfl⟩
    exact Set.encard_mono hAsub
  · exact le_sSup ⟨mergeFiber U Ω t, ⟨Set.Subset.rfl, h⟩, rfl⟩

end Nonautonomous

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/


set_option linter.style.longLine false in
/-- info: 'Nonautonomous.Reaches.mergeLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.Reaches.mergeLaw

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.mergeLaw_iterate_mergeMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.mergeLaw_iterate_mergeMk

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.reaches_mergeMk_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.reaches_mergeMk_iterate

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.width_le_encard_mergeFiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_le_encard_mergeFiber

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.width_eq_encard_of_root_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_eq_encard_of_root_set

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.width_eq_encard_of_is_root_antichain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_eq_encard_of_is_root_antichain

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.exists_is_root_antichain_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.exists_is_root_antichain_of_finite

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.width_eq_encard_canonical_of_antisymm_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_eq_encard_canonical_of_antisymm_on

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.exists_canonical_set_empty_pos_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.exists_canonical_set_empty_pos_width

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.pos_width_not_exists_is_root_antichain_int_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.pos_width_not_exists_is_root_antichain_int_succ

/-- info: 'Nonautonomous.width_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_mono

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.width_mono_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_mono_of_subset

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.width_nat_succ_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_nat_succ_eq_one

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.mergeFiber_nat_succ_fast_clock_encard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.mergeFiber_nat_succ_fast_clock_encard

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.exists_conservation_factor_extent_gt_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.exists_conservation_factor_extent_gt_width
