module

public import Nonautonomous.MergeQuotient

/-!
# Axiom audit for the `Nonautonomous` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration of the nonautonomous kernel drifts from the asserted one: the merge quotient, its
injective law, the universality of the quotient map among semiconjugate factor maps, and the
fibers it represents.
-/

@[expose] public section

-- The nonautonomous kernel (`Nonautonomous/MergeQuotient.lean`): the merge quotient carries a
-- factor map with an injective law, built from any update alone with no hypothesis, and every
-- semiconjugate factor map with an injective law factors through it (universality).
set_option linter.style.longLine false in
/-- info: 'Nonautonomous.mergeLaw_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.mergeLaw_injective

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.semiconj_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.semiconj_merge

/-- info: 'Nonautonomous.Semiconj.merges_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.Semiconj.merges_invariant

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.exists_mergeMk_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.exists_mergeMk_injective

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.positivelyInvariant_mergeFiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.positivelyInvariant_mergeFiber

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.mergeFiber_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.mergeFiber_injOn
