module

public import Nonautonomous.ReachabilityWidth

/-!
# Forward images: a system grown from a finite start set has bounded width

([RuleSpace] §2 Proposition 2.9)

The fibers of a nonautonomous set may be *given* (as a designed family) or *derived* from a
designated finite start region as forward images.
This file is the derived case, literally: the fiber at `t` is the `t`-th iterated image of a start
set `S` under the update `U`.
On such a system the width is bounded by the start set's own cardinality at every time — a
fact about the represented classes alone, since it needs no antichain hypothesis at all — which
closes the fixed-seed route to unbounded width for every update at once: a finite start set can
never supply an unbounded width.

## Main results

* `forwardImages` — the derived nonautonomous set, `forwardImages U S t := U^[t] '' S`.
* `positivelyInvariant_forwardImages` — a system derived this way is positively invariant, with
  equality: `U '' (U^[t] '' S) = U^[t + 1] '' S`.
* `mergeFiber_forwardImages_encard_le` — the classes of the merge quotient represented in the fiber
  at `t` are an image of an image of `S`, so their number never exceeds `S`'s cardinality.
* `width_forwardImages_le` — hence the width itself is capped by `S`'s cardinality at
  every time, composing the above with `Nonautonomous.width_le_encard_mergeFiber`.
* `width_forwardImages_ne_top` — at a finite start set the width stays finite at every time.

## Scope

The bound counts represented classes only: it consumes no antichain structure, so it says nothing
about whether the cap is attained or how far below it the true width sits at a particular update —
`PermutiveWidth.lean` is where a concrete update's width is computed exactly.
-/


@[expose] public section

namespace Nonautonomous


variable {X : Type*}

/-- **The forward images** ([RuleSpace] §2 Proposition 2.9): the fiber at `t` is the `t`-th iterated
image of the start set `S` under the update `U`. -/
def forwardImages (U : X → X) (S : Set X) (t : ℕ) : Set X := U^[t] '' S

/-- **The forward images are positively invariant, with equality**: `U` carries the `t`-th iterated
image into the `(t + 1)`-st, `Function.iterate_succ_apply'` supplying the one further step. -/
theorem positivelyInvariant_forwardImages (U : X → X) (S : Set X) :
    PositivelyInvariant U (forwardImages U S) := by
  intro t s hs
  obtain ⟨x, hx, rfl⟩ := hs
  exact ⟨x, hx, Function.iterate_succ_apply' U t x⟩

/-- **The represented classes are an image of an image of `S`**: `mergeFiber` unfolds to
`mergeMk U '' (U^[t] '' S)`, and `Set.encard_image_le` fires twice. -/
theorem mergeFiber_forwardImages_encard_le (U : X → X) (S : Set X) (t : ℕ) :
    (mergeFiber U (forwardImages U S) t).encard ≤ S.encard :=
  calc (mergeFiber U (forwardImages U S) t).encard
      = (mergeMk U '' (U^[t] '' S)).encard := rfl
    _ ≤ (U^[t] '' S).encard := Set.encard_image_le _ _
    _ ≤ S.encard := Set.encard_image_le _ _

/-- **The width is capped by the start set**: the width of the forward images of `S`
never exceeds `S`'s own cardinality, at every time — the fixed-seed route to an unbounded width is
closed for every update at once. -/
theorem width_forwardImages_le (U : X → X) (S : Set X) (t : ℕ) :
    width U (forwardImages U S) t ≤ S.encard :=
  (width_le_encard_mergeFiber U (forwardImages U S) t).trans
    (mergeFiber_forwardImages_encard_le U S t)

/-- At a finite start set the width stays finite at every time: it is capped by `S.encard`, which
is itself finite. -/
theorem width_forwardImages_ne_top (U : X → X) {S : Set X} (hS : S.Finite) (t : ℕ) :
    width U (forwardImages U S) t ≠ ⊤ :=
  (lt_of_le_of_lt (width_forwardImages_le U S t) hS.encard_lt_top).ne

end Nonautonomous

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/


set_option linter.style.longLine false in
/-- info: 'Nonautonomous.positivelyInvariant_forwardImages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.positivelyInvariant_forwardImages

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.mergeFiber_forwardImages_encard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.mergeFiber_forwardImages_encard_le

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.width_forwardImages_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_forwardImages_le

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.width_forwardImages_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.width_forwardImages_ne_top
