# lean-elementary-cellular-automata

[![CI](https://github.com/lividgreen/lean-elementary-cellular-automata/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/lividgreen/lean-elementary-cellular-automata/actions/workflows/lean_action_ci.yml)
[![API docs](https://img.shields.io/badge/docs-API%20reference-4c1)](https://lividgreen.github.io/lean-elementary-cellular-automata/)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23275249-blue)](https://doi.org/10.5281/zenodo.23275249)
[![Lean](https://img.shields.io/badge/Lean%204-Mathlib-black)](https://leanprover-community.github.io/)
[![License](https://img.shields.io/badge/license-Apache--2.0-lightgrey)](LICENSE)

**The elementary cellular automata, machine-checked in Lean 4: the 256 rules on
a line of binary cells in which a cell's next value depends on itself and its
two neighbours.** This library proves what the orbits of those rules do — which
rules grow from a finite configuration, what a column, a window or a ray of an
orbit looks like, which rules reproduce a pattern, and what it costs a rule to
erase a local perturbation — at every rule where it can, and exactly at rule
`90`.

## What it holds

- **Growth.** The growing width of a rule is zero at every time or unbounded at
  every one of the 128 quiescent rules, and unbounded at exactly 54 of them
  (`growth_census`), one theorem over the Wolfram number.
- **Columns, windows and rays.** At every quiescent rule whose diameter never
  grows, every column and every ray of rational speed of an orbit is
  eventually periodic; at every quiescent rule the columns between two
  eventually periodic columns are eventually periodic, and the error count of
  the best Markov predictor of a window, at any order of at least one, is at
  most the sum of its two end columns'.
- **The rays of rule `90`.** From a single cell, no ray of rational speed
  strictly between `0` and `1` is eventually periodic; the lines along which
  the orbit is eventually zero are exactly a named family; the ones on a ray
  are counted exactly at two speeds and capped by Fibonacci numbers at every
  speed.
- **Erasure of local perturbations.** At 164 of the 256 rules, two
  configurations each of which erases every perturbation of two cells have the
  same successor, at every scale — at some of those rules because no
  configuration erases at all.
- **Reproduction and self-simulation.** Rule `90` simulates itself by a
  blocking transformation, four rules are rule `90` on doubled configurations,
  and the quiescent rules that reproduce a pattern without bound number at
  least fourteen and lie among the 54 that grow.
- **The rule space itself.** The Wolfram number with its two symmetries acting
  on the dynamics, the 88 classes they generate, the permutive rules counted,
  the six rules that are injective, and the 226 shown not surjective.
- **The kernel underneath.** Nonautonomous sets, semiconjugacies, the merge
  quotient of an update and the width of its reachability preorder, over any
  carrier.

## Why it is worth having

A search of the Lean libraries and of the other provers, dated in the scope
section, found no statement of this library in any of them. In the literature
the same search found the growth of two rules observed by experiment and three
block mechanisms listed as computed table rows; it found no statement of the
growth dichotomy or its census, of rule `90`'s rays at every rational speed, of
the erasure classes or of the reproduction bracket. So these are proved here
for the first time as far as that search reaches, and they are proved over the
rule space — the quiescent half for growth, all 256 rules for erasure — by
classes decided on a rule's eight bits, with the counts checked by the kernel.

The classical results the proofs use — a finite system driven by an eventually
periodic input is eventually periodic, Jen's lemma on the columns between two
eventually periodic columns, rule `90`'s `2^j` identity, Pascal's triangle
modulo two and Lucas's criterion at the prime two — are in
[lean-classical-upstream](https://github.com/lividgreen/lean-classical-upstream)
(concept DOI [10.5281/zenodo.23257423](https://doi.org/10.5281/zenodo.23257423)),
which this package requires.

## What is proved here

The short form of each result. The package has two library roots: the four
modules on nonautonomous sets stand under `Nonautonomous`, in the namespace of
that name, and the radius-one modules under `ECA`, in the namespace of that
name, whose base module `Basic.lean` names the objects they are about: a local
rule (`LocalRule`), a configuration (`Configuration`) and a finite
configuration (`FiniteConfiguration`), each an abbreviation of its type. A
name about one of these objects stands in its namespace, so dot notation
reads it on a term of that type (`LocalRule.finRule` and `LocalRule.Quiescent`
on a local rule, `FiniteConfiguration.diam` on a finite configuration), and a
theorem whose principal hypothesis is a predicate stands in that predicate's
namespace, read on a proof of it (`ZeroByEndpoints.diamBounded`). Below,
names are given without their namespaces. A
statement's number in the library's paper is given where it has one.

### Nonautonomous sets and their widths (`Nonautonomous`)

- **Nonautonomous sets, semiconjugacies and the merge quotient**
  (`MergeQuotient.lean`): a nonautonomous set is a family of fibers, one for
  each time, positively invariant under an update when the update carries each
  fiber into the next (`PositivelyInvariant`); a factor map that is a semiconjugacy onto a
  law on its values, the map allowed to depend on time
  (`Semiconj`), has fibers of its own (`imageFiber`), positively
  invariant under that law (`positivelyInvariant_imageFiber`). Two states merge
  when some common iterate identifies them (`Merges`); the quotient's induced
  law is injective with no hypothesis (`mergeLaw_injective`), the quotient map
  is a semiconjugacy at every nonautonomous set (`semiconj_merge`),
  and every such factor map with an injective law factors through it
  (`Semiconj.merges_invariant`, `exists_mergeMk_injective`);
  the merge classes represented in a fiber (`mergeFiber`) are positively
  invariant and injected fiber to fiber (`positivelyInvariant_mergeFiber`,
  `mergeFiber_injOn`). On a finite set the merge quotient is the eventual
  image. *Rule Space* Definitions 2.1 and 2.2 and Propositions
  2.5 and 2.6.

- **The width of the reachability preorder** (`ReachabilityWidth.lean`): the
  size of the largest antichain among the merge classes represented in a
  fiber, under reachability by the induced law (`width`, `ℕ∞`-valued),
  monotone in time with no hypothesis beyond positive invariance
  (`width_mono`). Counting classes is not the same thing: on the successor
  map of the naturals the classes in a fiber are unbounded while the width
  stays at one (`width_nat_succ_eq_one`), and a fast counter has classes in
  bijection with `Bool^t` at every time, with the same width
  (`mergeFiber_nat_succ_fast_clock_encard`). The width is read off a **root
  set**: a subset of a fiber that is already an antichain and which every
  class of the fiber reaches names the width exactly, with no hypothesis on
  the update (`width_eq_encard_of_is_root_antichain`; at a state-level root
  set, `width_eq_encard_of_root_set`); a root antichain always exists at a
  finite fiber (`exists_is_root_antichain_of_finite_fiber`, by a classical
  choice), and under antisymmetry it is exactly the classes of the fiber no
  other class reaches (`width_eq_encard_canonical_of_antisymm_on`), each
  hypothesis shown needed by a counterexample — the canonical set is empty at
  a finite system whose width is positive
  (`exists_canonical_set_empty_pos_width`), and the successor map on `ℤ` has
  positive width and no root antichain at all
  (`pos_width_not_exists_is_root_antichain_int_succ`). Boundary: a separation,
  not a dichotomy — a factor map with an injective law whose image of a fiber
  is an antichain under its own law can exceed the width
  (`exists_conservation_factor_extent_gt_width`). *Rule Space*
  Propositions 2.6 to 2.8.

- **Forward images, and the width computed exactly at elementary cellular
  automata** (`ForwardImages.lean`, `PermutiveWidth.lean`): the nonautonomous
  set of the iterated images of a start region (`forwardImages`) has its merge
  classes, hence its width, capped by the region's own cardinality at every
  time (`width_forwardImages_le`), so a finite start region caps the width. On the finitely supported configurations of the
  line, the extreme-tap linear rules — elementary rules `90` and `150`
  (`rule90`, `rule150`) — are additive and injective (`rule90_injective`),
  spread their support by exactly one cell per step at each end, and every
  nonzero orbit eventually leaves any fixed finite region
  (`rule90_region_exit`); on the forward images of an `n`-cell region, read
  at the region itself, their width is at least `2^(n−1)`
  (`width_rule90_derived_ge`) and exactly the size of the **root set**, the
  region-supported states with no nonzero region-supported predecessor
  (`rootSet`, `width_rule90_derived_eq`), a count that closes in addition
  form, `(rootSet rule90 n).encard + 2^(n−2) = 2^n + 1` at `2 ≤ n`
  (`rootSet_encard_add`). Both facts are generic in the update and in two
  endpoint-move constants (`width_derived_eq_encard_rootSet`,
  `rootSet_encard_add_of_hyps`), the identity update the counterexample that separates
  them (`guard_id_rootSet_load_bearing`); a quiescent local rule gives a map
  on the finitely supported configurations (`finRule`), one-sided permutivity in solved
  form gives injectivity on that carrier
  (`finRule_injective_of_leftPermutive`,
  `finRule_injective_of_rightPermutive`), and four non-additive rules —
  `30`, `86`, `154`, `210` — meet the hypotheses and share the exact width,
  rule `30`'s equal to rule `90`'s (`width_rule30_derived_eq_rule90`); the
  two shifts, rules `170` and `240`, carry their own width and count at their
  true endpoint moves (`width_rule170_derived_eq`,
  `rootSet_encard_add_rule170`, `width_rule240_derived_eq`), and a counterexample
  shows quiescence and permutivity alone do not pin the class-level spread
  (`guard_rule170_max'_spread_load_bearing`). *Rule Space*
  Propositions 2.9 to 2.11. Boundary: the counts are
  additive (`ℕ∞` subtraction is truncated), the closed forms being the paper's
  restatement; the permutivity-to-injectivity route is classical; the
  cap says nothing about attainment beyond the rules named.
- **The growing width: six rules grow, the identity does not**
  (`GrowingWidth.lean`, `LightConeWidth.lean`): the width restricted to
  the states whose orbit has unbounded size (`GrowingPart`, `growingWidth`) —
  the part invariant and merge-saturated (`growingPart_of_merge`), the
  restricted family positively invariant (`positivelyInvariant_growingPart`), the width monotone and
  below the plain one (`growingWidth_mono`, `growingWidth_le_width`), and a
  genuine restriction: `0` against `t + 1` at the identity
  (`growingWidth_id_slow_clock_eq_zero_width_eq_succ`). Under the support
  diameter (`diam`) and along the light cone of an `n`-cell window
  (`lightCone`), an update with exact endpoint moves `(1, 1)` has the nonzero
  states as its growing part (`growingPart_eq_ne_zero`), and with a trivial
  kernel and injectivity its growing width is at least `2^(n+t−1)`
  (`two_pow_le_growingWidth_lightCone`), hence unbounded
  (`growingWidth_lightCone_unbounded`) — instantiated at rules `30`, `86`,
  `90`, `150`, `154`, `210` (`growingWidth_lightCone_unbounded_rule30`, …),
  jointly satisfiable at rule `90`, and `0` at the identity and both shifts
  (`growingWidth_lightCone_id_eq_zero`,
  `growingWidth_lightCone_rule170_eq_zero`). The plain width along the same
  cone is unbounded even at the identity, so this is the quantity that sees
  the rule. *Rule Space* Definition 2.3 and Propositions 2.12
  and 2.13. Boundary: a lower bound, not the value; the rate depends on the
  choice of the cone; the diameter is one measure of size; the part is not
  decidable in general; a separation at a hypothesis class, not genericity.

### Growth over the rule space

- **The growing width over the whole radius-one rule space: an engine without
  injectivity, and a bracket at the rule bits** (`EndpointClasses.lean`): an
  antichain of merge classes is a set of states with pairwise disjoint
  forward orbits, so at exact endpoint moves `(a, b)` with `a + b ≥ 1` on any
  update-invariant set containing every translate of one state, the
  translates in the light cone are pairwise orbit-disjoint and each is
  growing — the growing width is at least `n + 2t + 1 − diam s₀`
  (`linear_le_growingWidth_lightCone_of_invariant`), hence unbounded
  (`growingWidth_lightCone_unbounded_of_invariant`), with the six hypotheses
  jointly met at rule `202` on the right end-word set
  (`growingWidth_lightCone_unbounded_of_invariant_nonvacuous`). The moves are
  read off a rule's bits (`finRule_min'_of_leftTap`,
  `finRule_max'_of_rightHold`, `EndsOneOne.finRule_max'`, …), the
  cone is positively invariant under every quiescent rule (`positivelyInvariant_lightCone_finRule`), and a
  non-increasing diameter empties the growing part
  (`growingPart_eq_empty_of_diam_le`). Two classes of rules, each a
  disjunction of bit equations: `GrowsByEndpoints` — unbounded growing
  width at every member (`GrowsByEndpoints.growingWidth_lightCone_unbounded`),
  `52` of the `128` quiescent rules (`card_growsByEndpoints`,
  `card_quiescent`) — and `ZeroByEndpoints` — width identically `0`
  (`ZeroByEndpoints.growingWidth_lightCone_eq_zero`), `48` rules
  (`card_zeroByEndpoints`) — disjoint
  (`growsByEndpoints_zeroByEndpoints_disjoint`). *Rule Space*
  Proposition 3.1. Boundary: the bound is linear where
  the six-rule one is exponential; the `28` rules in neither class are not
  decided by these two classes (`Growth.lean` decides eighteen of them and
  `BlockCount.lean` the other ten);
  the counts are kernel decisions over the
  256-element rule type; the instances at rules `90` and `150` are at rules
  written out here, with no stated identity to `rule90` and `rule150`.
- **Zero or unbounded, by one state** (`Growth.lean`): at every quiescent
  radius-one rule, one state whose orbit has unbounded diameter gives a
  linear lower bound on the growing width along the light cone
  (`linear_le_growingWidth_lightCone_of_mem_growingPart`), so the width is
  zero at every time or unbounded (`growingWidth_lightCone_zero_or_unbounded`).
  A diameter that grows by at most a constant gives zero (`DiamBoundedBy`,
  `growingWidth_lightCone_eq_zero_of_diamBoundedBy`), and both sides pass to
  the mirror rule by reflection (`reflect`, `mirrorRule`,
  `finRule_mirrorRule_reflect`, `diamBoundedBy_mirrorRule`,
  `reflect_mem_growingPart_mirrorRule`). *Rule Space* Proposition
  3.2. Rule 106 and its mirror, rule 120, are the first rules
  between the two endpoint classes decided: the update at `f106` is injective
  (`finRule_f106_injective`), the two-cell state `seedOneOne` is the image
  of no state (`seedOneOne_notMem_range_f106`), and at an injective update
  with a left tap such a state has an orbit of unbounded diameter
  (`mem_growingPart_of_injective_of_notMem_range`), so the width is unbounded
  at both (`growingWidth_lightCone_unbounded_f106`,
  `growingWidth_lightCone_unbounded_mirror_f106`). *Rule Space*
  Proposition 3.3. Rules 38, 46, 66 and 174 and their mirrors do
  not grow: a set of pairs of end values closed under the rule, on which
  the cell past the end dies, holds every orbit's diameter within two of its
  start's (`diamBoundedBy_two_of_endClosure`, `diamBoundedBy_f38`,
  `diamBoundedBy_f46`, `diamBoundedBy_f66`, `diamBoundedBy_f174`), so the
  width is zero (`growingWidth_lightCone_eq_zero_f38` and its seven
  siblings). *Rule Space* Proposition 3.4. Rule 166 and
  its mirror, rule 180, do not grow either: every orbit's diameter is
  within one of its start's (`diamBoundedBy_f166`), by an invariant of the
  last block's parity, and the twelve rules are one statement with no
  hypothesis (`growingWidth_lightCone_middle_twelve`). *Rule Space*
  Proposition 3.5. The traffic class does not grow: at every
  rule that is one only where the traffic rule 184, mirrored, is one, a set
  cell stays or is pushed by the two cells behind it, and no orbit's diameter
  exceeds twice its start's (`diam_iterate_le_two_mul_of_traffic`), so the
  width is zero there and at the mirror
  (`growingWidth_lightCone_eq_zero_of_traffic`,
  `growingWidth_lightCone_eq_zero_mirror_of_traffic`); rules 98, 194 and 226
  are members (`f98_traffic`, `f194_traffic`, `f226_traffic`), and with
  their mirrors, rule 184 among them, six rules are decided
  (`growingWidth_lightCone_traffic_six`). The class hypothesis is needed
  (`traffic_hypothesis_load_bearing`). *Rule Space* Proposition
  3.6. Boundary: no rate of the diameter is stated at rule 106.
- **The last ten rules, by a count of blocks** (`BlockCount.lean`): a
  count that grows by one a step only where two further counted cells stand
  within a fixed distance behind stays under a line
  (`count_invariant_of_step`). Counting block starts, a rule that sets a cell
  only where its left neighbour was clear and it or its right neighbour was
  set holds every orbit's diameter within five times its start's plus five
  (`diam_iterate_le_of_leftClear`); rules 6 and 14 are members. Counting block
  ends gives the same bound at rule 142 (`diam_iterate_le_f142`); at rule 134
  long runs shorten until the update is rule 6's (`diam_iterate_le_f134`);
  at rule 74 the starts of blocks of two or more are counted after three
  steps (`diam_iterate_le_f74`). An affine diameter bound gives zero width
  (`growingWidth_lightCone_eq_zero_of_diam_le_affine`), so the ten rules —
  these five and their mirrors — do not grow
  (`growingWidth_lightCone_middle_ten`). *Rule Space* Proposition
  3.7. Boundary: no constant is shown sharp. That 54 of
  the 128 quiescent rules grow is one theorem over the Wolfram numeral
  (`growth_census`), *Rule Space* Proposition 3.8.
- **The census over the Wolfram numeral** (`WolframNumber.lean`):
  `LocalRule.ofWolfram n` is the rule with Wolfram number `n < 256`, equal to
  every hand-written rule at its number (`ofWolfram_30`, `ofWolfram_90`, …),
  with reflection and complement as maps on the numbers (`ofWolfram_mirrorNum`,
  `ofWolfram_complementNum`) and the eight additive rules counted
  (`card_additive`). A number is growing when its rule lies in the endpoint
  engine's class or is rule `106` or `120` (`Growing`), a
  decided condition, and at every quiescent number the growing width along every
  light cone is unbounded when it is growing and zero at every time when it
  is not, with 128 quiescent numbers, 54 growing and 74 not
  (`growth_census`, both branches met at rules `90` and `170` by
  `growth_census_nonvacuous`). *Rule Space* Proposition 3.8.
- **The symmetries of the rule space, and the permutive and bijective rules**
  (`WolframSymmetries.lean`, on `ElementaryRuleClasses.lean` of
  lean-classical-upstream): reflection of the line conjugates the step of
  every local rule to its mirror rule's, and the exchange of `0` and `1`
  conjugates it to its complement conjugate's, at every configuration of the
  line and every iterate (`lineRule_mirrorRule_reflect`,
  `iterate_lineRule_mirrorRule_reflect`, `lineRule_complement`,
  `iterate_lineRule_complement`), and so on the Wolfram number
  (`lineRule_ofWolfram_mirrorNum`, `lineRule_ofWolfram_complementNum`, with
  `iterate_lineRule_ofWolfram_mirrorNum` and
  `iterate_lineRule_ofWolfram_complementNum`).
  The number and its two maps are the classical package's
  (`ofWolfram_eq_elementaryRule`, `mirrorNum_eq_reflectNum`,
  `complementNum_eq_complementNum`), so the rules fall into 88 classes,
  counted by their least members (`card_classes_ofWolfram`), the count of Li and
  Packard (1990). Of the rules that
  are not quiescent, 64 have a quiescent complement conjugate, exactly those
  sending the all-one neighbourhood to one (`quiescent_complementNum_iff`,
  `card_quiescent_complementNum`). Sixteen rules are left-permutive, sixteen
  right-permutive, rules 90, 105, 150 and 165 both, and 28 one or the other
  (`card_leftPermutive`, `card_rightPermutive`, `permutive_both`,
  `card_permutiveEnd_ofWolfram`); the mirror carries one kind to the other
  (`rightPermutive_mirrorNum`), and the count over the numbers is the count
  over all rules, the numeral being a bijection (`ofWolfram_bijective`,
  `card_permutiveEnd_eq_card_numbers`). Six rules are written out and are
  bijections of the configurations of the line, each with its inverse: the
  identity, rule 204, the two shifts, rules 170 and 240, and those three
  followed by the exchange of `0` and `1`, rules 51, 85 and 15
  (`lineRule_ofWolfram_204`, `lineRule_ofWolfram_170`, `lineRule_ofWolfram_240`,
  `lineRule_ofWolfram_51`, `lineRule_ofWolfram_85`, `lineRule_ofWolfram_15`,
  `bijective_lineRule_ofWolfram_204` and its five siblings); at the identity the
  growing width along the light cone is zero at every time
  (`growingWidth_lightCone_ofWolfram_204_eq_zero`). In no paper. Boundary: the
  conjugations are on all configurations of the line, where the growth
  statements are on finitely supported ones, so no growth statement is
  carried to a rule that is not quiescent. Among the quiescent rules, the map
  on finitely supported configurations keeps the number of set cells of every
  state exactly at rules 170, 184, 204, 226 and 240
  (`card_support_finRule_ofWolfram_iff`), an instance of the classical package's
  statement in `NumberConservation.lean`, the list of Boccara and Fukś (1998).
- **Which rules are injective, and which are not surjective**
  (`Surjectivity.lean`, data in `SurjectivityCert.lean`): a word has no
  preimage word when the set of pairs of the last two cells of a preimage,
  advanced one letter at a time, ends empty (`hasNoPreimage`), and then no
  configuration of the line has it in its image at any place
  (`hasNoPreimage_sound`), so the rule is not surjective
  (`not_surjective_of_hasNoPreimage`). The kernel checks such a word, of
  length at most nine, at each of the 226 rules that are not permutive at an
  end and are not rule 51 or rule 204 (`orphans_pass`, `orphans_length_le`,
  `mem_orphans_iff`, `orphans_length`, `orphans_nodup`), so none of them is
  surjective
  (`not_surjective_lineRule_ofWolfram`). Two distinct words of one length whose
  cyclic neighbourhoods have equal values under the rule (`isCollision`) give
  two spatially periodic configurations with one image, so the rule is not
  injective (`not_injective_of_collision`); the kernel checks such a pair, of
  period at most four, at each of the 250 rules outside 15, 51, 85, 170, 204
  and 240 (`collisions_pass`, `collisions_length_le`, `mem_collisions_iff`,
  `not_injective_lineRule_ofWolfram`). With the six bijections, a rule is
  injective on the configurations of the line exactly when it is one of those
  six, and bijective exactly then (`injective_lineRule_ofWolfram_iff`,
  `bijective_lineRule_ofWolfram_iff`). In no paper. The lengths of the shortest
  words with no preimage were first tabulated by Wolfram (1986), Table 9.
  Boundary: the 28 permutive rules other than the two shifts and their
  complements are not shown surjective here; that nine is the least bound on
  a word's length is not stated; the lists are data the kernel checks.

### Columns, windows and rays

- **The observed column is eventually periodic wherever the diameter never grows**
  (`ObservedColumn.lean`): the column an observer reads at one cell along an
  orbit (`observedColumn`) is eventually periodic at every quiescent rule
  whose diameter never grows (`eventuallyPeriodic_observedColumn_of_diam_le`)
  — the pattern up to translation ranges over a finite set, so it recurs
  with a drift, and the column is periodic at zero drift and eventually `0`
  otherwise — hence at every zero-class rule
  (`ZeroByEndpoints.eventuallyPeriodic_observedColumn`); in the contrapositive,
  a column that is not eventually periodic forces the diameter to grow at
  some step of that seed's own orbit
  (`exists_diam_lt_iterate_of_not_eventuallyPeriodic`). The hypotheses are
  met at the shift `170` with its center column written out
  (`observedColumn_f170_single`), and the diameter hypothesis is needed
  at rule `30` (`diam_lt_finRule_f30_single`). The converse fails at a
  checked witness: rule `90` is in the growing class and its single-seed
  center column is `1` then `0` forever (`observedColumn_f90_single`).
  The rational ray at speed `p/q` reads the cell `e + ⌊pt/q⌋` at step `t`
  (`observedRationalRay`), the column at speed zero
  (`observedRationalRay_zero`); at every quiescent rule whose diameter never
  grows every rational ray is eventually periodic
  (`eventuallyPeriodic_observedRationalRay_of_diam_le`), reading one relative
  cell of the drifting pattern forever when its speed is the drift and zero
  forever otherwise, hence at every zero-class rule
  (`ZeroByEndpoints.eventuallyPeriodic_observedRationalRay`), the
  hypotheses met at the shift at speed one half
  (`eventuallyPeriodic_observedRationalRay_of_diam_le_nonvacuous`). The
  column's statements are *Rule Space* Remark 4.1, the rational ray as *Rule Space* Proposition 4.4. Boundary:
  existence of a
  period only, no bound on it or on the onset; one column or ray, not the
  configuration; beyond that one column of rule `90`, this module says nothing
  about the column or any ray at a rule whose diameter grows, rule `30`'s
  included.
- **Driven columns: what is eventually periodic at every rule, and a column
  that is not** (`ObservedRays.lean`, on `DrivenColumns.lean` and
  `LocalRuleColumns.lean` of lean-classical-upstream): a sequence in a finite type whose next
  value is, from some step on, a fixed function of its value and of an
  eventually periodic input is eventually periodic
  (`eventuallyPeriodic_of_driven`). For the rules' maps this gives, at
  every quiescent rule and every finitely supported state: a window of
  adjacent cells is eventually periodic exactly when the columns at its two
  end cells are (`eventuallyPeriodic_observedWindow_iff`), so the columns
  between two eventually periodic columns are eventually periodic
  (`eventuallyPeriodic_observedColumn_between`); and the rays that move one
  cell a step, in either direction and from every start cell, are
  eventually periodic (`eventuallyPeriodic_observedRay_one`,
  `eventuallyPeriodic_observedRay_neg_one`). At rule `90`, `2^j` steps of
  the rule send a state `s` to `i ↦ s(i − 2^j) + s(i + 2^j)`
  (`iterate_two_pow_f90`), and the single seed's column at cell `1` is not
  eventually periodic
  (`not_eventuallyPeriodic_observedColumn_f90_single_one`): it is live at
  every step `2^(j+1) − 1` and dead strictly between
  (`observedColumn_f90_single_one_live`,
  `observedColumn_f90_single_one_dead_between`). One eventually periodic end column does not
  make the column beside it so
  (`eventuallyPeriodic_observedColumn_between_guard`), and the rays'
  statement fails at velocity zero
  (`not_eventuallyPeriodic_observedRay_zero_f90`). The interior, the
  `2^j` identity and the column's non-periodicity are instances of the
  classical package's statements for any local rule on every configuration
  of the line (`coe_finRule_iterate`). *Rule Space*
  Proposition 4.2. Its column at cell `1` is also
  one equality, live exactly at the steps `t` with `t + 1 = 2^j` for some
  `j ≥ 1` (`observedColumn_f90_single_one`), and the driven interior's
  hypotheses are met together at the shift
  (`eventuallyPeriodic_observedColumn_between_nonvacuous`). Boundary:
  existence of a period only; velocities `1` and `−1` only; nothing about
  any other column of rule `90`, any other seed, or any column of another
  growing rule.
- **The Markov error count: a predictor on the last symbols, and what bounds
  its errors** (`MarkovErrorCount.lean`): a sequence is eventually exact at
  order `k` when one fixed function of its last `k` symbols gives the next
  symbol from some step on (`EventuallyExact`). An eventually periodic
  sequence is eventually exact at some order
  (`eventuallyExact_of_eventuallyPeriodic`), and over a finite alphabet the
  converse holds (`eventuallyPeriodic_of_eventuallyExact`), the two together
  one equivalence (`exists_eventuallyExact_iff_eventuallyPeriodic`); the
  finite alphabet is needed, the identity on the naturals being eventually
  exact at order one and not eventually periodic
  (`eventuallyExact_nat_id_not_eventuallyPeriodic`). The error count at a
  horizon is the fewest errors any such function makes before it, the minimum
  taken at each horizon separately (`predictorErrors`, `markovErrorCount`):
  the error count of the best Markov predictor of order `k` in hindsight,
  which divided by the horizon is the Markov predictability of Feder, Merhav
  and Gutman (1992), up to the convention for the first `k` symbols. Over a
  finite alphabet it is bounded in the horizon exactly when the sequence is
  eventually exact at that order
  (`markovErrorCount_bounded_iff_eventuallyExact`), and bounded at some order
  exactly when the sequence is eventually periodic
  (`exists_markovErrorCount_bounded_iff_eventuallyPeriodic`). At every
  quiescent rule and every finitely supported state, a window of adjacent
  cells meets either condition at some order exactly when the columns at
  its two end cells do, each at an order of its own
  (`exists_eventuallyExact_observedWindow_iff`,
  `exists_markovErrorCount_bounded_observedWindow_iff`). At rule `90` from the
  single seed the center column is eventually exact at order zero
  (`eventuallyExact_observedColumn_f90_single`) and the column at cell `1` at
  no order (`not_exists_eventuallyExact_observedColumn_f90_single_one`), its
  error count unbounded at every order
  (`markovErrorCount_observedColumn_f90_single_one_unbounded`). The two are the
  two sides of one class statement: at every rule of the zero class, from
  every finitely supported state and at every cell, some order gives the
  column's error count a bound in the horizon
  (`ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn`), and so
  for every window of adjacent cells
  (`ZeroByEndpoints.exists_markovErrorCount_bounded_observedWindow`), both
  hypotheses met at the shift `170`
  (`ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn_nonvacuous`);
  and the class hypothesis is needed, rule `90` lying in the growing
  class with its cell-one count unbounded
  (`exists_markovErrorCount_bounded_observedColumn_zero_class_guard`): the
  count is bounded wherever the rule does not grow. The two window
  statements are *Rule Space* Proposition 4.3(i); the rest is in no paper and
  extends *Rule Space* Propositions 3.1 and 4.2. Boundary: the orders and the
  bounds on the two sides of an equivalence are separate existential statements, none
  given in terms of another; no rate of the count is stated; the class
  statement says nothing at the twenty-eight rules in neither class.

- **A window's count against its ends'** (`WindowCount.lean`): the error
  count of a factor is the fewest errors, over the functions of the last `k`
  states, in predicting a fixed function of the next state
  (`factorPredictorErrors`, `factorErrorCount`); at the identity it is the
  Markov error count (`factorErrorCount_id`). A factor's count is at most the
  state's (`factorErrorCount_le_markovErrorCount`), and at most the count of
  the factor's own sequence (`factorErrorCount_le_markovErrorCount_comp`). At
  every quiescent rule, every finitely supported state, every window, every
  order of at least one and every horizon, the window's error count is at
  most the sum of the counts of its two end cells predicted from the window
  (`markovErrorCount_observedWindow_le_add_factorErrorCount`), hence at most
  the sum of its two end columns' error counts
  (`markovErrorCount_observedWindow_le_add_columns`); by the first comparison
  it is at least each end cell's count. The order is needed: at order zero
  the bound fails at the rule that sends everything to zero
  (`markovErrorCount_observedWindow_zero_memory_guard`). The end columns' own
  counts give no lower bound: at the shift, a window of two cells has no
  error in three steps at order one while the column at its first cell has
  one (`markovErrorCount_observedWindow_lt_column_f170`). The translating
  window at a rational speed `p/q` of at most one, with the phase `t mod q` of
  its own schedule (`movingWindow`), has at every quiescent rule, every
  finitely supported state, every start, every width of at least three, every
  order of at least one and every horizon an error count at most the sum of
  its two ends' counts, the trailing end's the cell it sits on and the
  leading end's the two cells it sits on and moves to
  (`markovErrorCount_movingWindow_le_add_factorErrorCount`), the hypotheses
  met at rule `90` at speed one half
  (`markovErrorCount_movingWindow_le_add_factorErrorCount_nonvacuous`) and the
  order needed at the zero rule, where a predictor of order zero cannot
  follow the phase (`markovErrorCount_movingWindow_zero_memory_guard`). The
  window at rest is *Rule Space* Proposition 4.3(ii)–(iii); the translating
  window is in no paper. Boundary: both sides of each bound are at the same
  order and horizon; no bound is stated at order zero, none for a window
  whose ends move at different speeds or at a speed above one, and each
  counterexample is a single instance.

- **Rule 90's rational rays: the three conditions** (`RationalRayRule90.lean`): a
  sequence with a one past every step and zero runs of every length past
  every step is not eventually periodic
  (`not_eventuallyPeriodic_of_late_one_of_late_zero_runs`, both hypotheses met
  at `not_eventuallyPeriodic_of_late_one_of_late_zero_runs_nonvacuous`). For
  rule `90` from the single seed and the ray of speed `p/q` from cell `e`,
  three named conditions — a one at every pair of naturals with no shared
  binary digit (`OneOfDisjoint`), such pairs on the ray past every step
  (`OnRay`, `LateDisjointOnRay`), and zero runs of every length past every
  step (`LateZeroRuns`) — give a one on the ray past every step
  (`exists_late_one_observedRationalRay_f90_single_of`) and a ray that is not
  eventually periodic
  (`not_eventuallyPeriodic_observedRationalRay_f90_single_of`). The first
  condition is proved (`oneOfDisjoint`): outside the light cone the single
  seed's orbit is zero (`f90_single_apply_eq_zero_of_lt`), a further `2^M`
  steps split an orbit into two translated copies
  (`f90_iterate_two_pow_add`), and the disjointness is needed, the
  rule reading zero at step two at the seeded cell (`oneOfDisjoint_guard`).
  The third condition is proved at every speed below one, from every cell
  (`lateZeroRuns`), and fails at speed one, where the ray rides the edge and
  never reads a zero (`lateZeroRuns_guard`). The second condition and the
  unconditional theorems are in `RationalRayPairs.lean`. *Rule Space* Proposition 5.1. Boundary: one rule and one seed;
  the second condition is a hypothesis within this module.
- **The arithmetic of rule 90's rays** (`RationalRayPairs.lean`): a pair of
  naturals lies on the ray of speed `p/q` from `e` exactly when
  `(q + p) b - (q - p) a + q e` lies in `[0, q)` (`onRay_iff`). Where both
  terms of the speed are odd: a pair with no shared binary digit and strip
  value zero exists (`exists_zero_pair`), and added above the digits of any
  disjoint pair it gives another disjoint pair (`and_add_shift_eq_zero`); a
  disjoint pair with one member a single bit lands in any prescribed window
  (`exists_single_bit_hit`); so a disjoint pair lies on the ray at every
  offset (`exists_disjoint_onRay_of_odd`) and past every step
  (`lateDisjointOnRay_of_odd`, its hypotheses met at
  `lateDisjointOnRay_of_odd_nonvacuous`). No zero pair exists at speed one
  half (`exists_zero_pair_guard`). Where the sum of the terms is odd and the
  speed is below one third: a pair whose first member is a multiple of a
  power of two lies on the ray whenever a divisibility and two bounds hold
  (`onRay_of_dvd`), some power of two puts the needed residue in the window
  (`exists_pow_residue_lt`), and so disjoint pairs lie on the ray past every
  step (`lateDisjointOnRay_of_three_mul_lt`, its hypotheses met at
  `lateDisjointOnRay_of_three_mul_lt_nonvacuous`). Where the sum is odd
  and the speed is above one third: a disjoint pair on the ray with its top
  digit in the first member exists (`exists_single_bit_hit_top`,
  `exists_top_disjoint_onRay`), and moving that digit up keeps it disjoint
  and on the ray (`and_pump_top`, `lateDisjointOnRay_of_lt_three_mul`, its
  hypotheses met at `lateDisjointOnRay_of_lt_three_mul_nonvacuous`). So at
  every speed strictly between 0 and 1 disjoint pairs lie on the ray past
  every step (`lateDisjointOnRay`), the ray of rule `90` from the single
  seed reads a one past every step
  (`exists_late_one_observedRationalRay_f90_single`) and is not eventually
  periodic (`not_eventuallyPeriodic_observedRationalRay_f90_single`, its
  hypotheses met at
  `not_eventuallyPeriodic_observedRationalRay_f90_single_nonvacuous`); at
  speeds 0 and 1 from cell 0 the ray is eventually periodic
  (`not_eventuallyPeriodic_observedRationalRay_f90_single_guard_zero`,
  `not_eventuallyPeriodic_observedRationalRay_f90_single_guard_one`).
  *Rule Space* Proposition 5.1. Boundary: rule `90`
  and the single seed only; existence of the ones and the zero runs, with
  no density or rate; rays toward decreasing cells are not stated.
- **A second seed of rule 90** (`RationalRaySeeds.lean`): from the single
  seed, rule 90 reads `0` at cell `a - b` at step `a + b` whenever `a` and
  `b` share a binary digit (`zeroOfShared`, the converse of
  `oneOfDisjoint`), and at every cell whose sum with the step is odd
  (`f90_single_apply_eq_zero_of_odd`). One step sends the single cell `1`
  to the two-cell seed `{0, 2}` (`finRule_f90_single_one`), whose orbit
  is the single seed's one step later, moved one cell
  (`f90_pair_iterate_apply`); so from that seed the rational ray of speed
  `1/3` from cell `1` reads `0` at every step and is eventually periodic
  (`observedRationalRay_f90_pair_eq_zero`,
  `eventuallyPeriodic_observedRationalRay_f90_pair`), the single seed of
  the rays above being needed. *Rule Space* Proposition
  5.2. At every speed `1/(2^m - 1)`, `m >= 2`, the single seed
  reads `0` at cell `(s - 1) / (2^m - 1)` at every step `s >= 1`
  (`f90_single_apply_zeroLine`, through the digit lemma
  `and_sub_div_two_pow_ne_zero`), so the ray of that speed reads `0` at
  every step from the two-cell seed and from one step of the single seed
  advanced by any multiple of `2^m - 1` steps
  (`observedRationalRay_f90_pair_eq_zero_pow`,
  `observedRationalRay_f90_zeroLine`). *Rule Space* Proposition
  5.3. Boundary: these speeds and seeds; that no other ray
  is eventually periodic is not stated.
- **The rate of rule 90's rays** (`RationalRayRate.lean`): from the single
  seed, the ray of speed `1/2` from cell `1` reads `1` exactly at the steps
  `(4^(i+1) - 1)/3` and twice them
  (`observedRationalRay_f90_single_half_one_iff`, through the digit lemmas
  `and_three_mul_add_one_eq_zero_iff` and
  `and_three_mul_add_two_eq_zero_iff`), and the ray of speed `1/3` from cell
  `0` exactly at the steps `3b` with `b &&& 2b = 0`
  (`observedRationalRay_f90_single_third_one_iff`; the parity of `C(3n, n)`,
  `choose_three_mul_mod_two_eq_one_iff` in lean-classical-upstream). The Markov error count of any binary sequence is at most the number of its
  ones (`markovErrorCount_le_card_ones`), so the speed-`1/2` ray's count is at
  most `2 * Nat.log 4 (T + k) + 2` (`markovErrorCount_f90_single_half_le`).
  *Rule Space* Proposition 5.4. Boundary: two rays of
  one seed; no lower bound and no other speed is stated.
- **A Fibonacci ceiling on rule 90's rays** (`RationalRayBound.lean`): the
  pairs below `2^K` with no shared binary digit on a line `D a - P b = c`
  (`lineCount`) number at most `Nat.fib (K + 1)` at every pair of positive
  integers (`lineCount_le_fib_of_pos`): the count is a two-branch recursion
  (`repCount`, by the bridges `lineCount_eq_repCount_of_even_odd`,
  `lineCount_eq_repCount_of_odd_even`, `lineCount_eq_repCount_of_odd_odd`)
  bounded through a product of Fibonacci numbers (`repCountBound`). So from
  the single seed every ray of speed `p / q` with `0 < p < q` reads at most
  `q * Nat.fib (K + 1)` ones below step `2^K`
  (`card_ones_observedRationalRay_f90_single_le_fib`). The pairs that are
  `Closing` have their own one-step proof (`lineCount_le_fib`,
  `card_ones_observedRationalRay_f90_single_le`). *Rule Space*
  Proposition 5.5. Boundary: positive coefficients
  (`lineCount_not_le_fib_of_neg`); an upper bound only.
- **The eventually periodic lines of rule 90** (`RationalRayLines.lean`): the line of
  slope `p / q` and offset `c` reads cell `(p s + c) / q` at step `s`
  (`OnLine`, `onLine_iff`). From the single seed, at coprime `0 < p < q`, a
  line reads `1` past every step exactly when it is not a `ZeroLine` — slope
  `1 / (2 ^ m - 1)`, offset `-1` (`exists_late_one_f90_single_onLine_iff`).
  Odd sums go through a residue engine (`lateDisjointOnLine_of_residue`,
  `exists_mul_residue_lt`, `exists_pow_residue_lt_of_two_mul_lt`); two odd
  terms through a gap lemma on the values `P b - D a` of pairs with no shared
  binary digit (`exists_disjoint_value_in_window`, its exception real by
  `not_exists_disjoint_value_at_exception`). A ray from the single seed
  advanced `k` steps is a line
  (`observedRationalRay_f90_iterate_single_eq_line`). *Rule Space*
  Proposition 5.6. Boundary: the single seed and its orbit.

### Erasure of local perturbations

- **The margin one cell's value allows** (`LocalMargin.lean`): a function of
  a state reads only a finite set of cells when its value is fixed by them
  (`ReadsOnly`), and holds within `e` at a state when every state differing
  from it at no more than `e` cells gives the same value (`HoldsWithin`). If
  a function reads only `N` and takes different values at two states, the
  two margins at which those values hold sum to less than the number of
  cells of `N` at which the states differ
  (`margins_add_lt_card_of_readsOnly`), a packing inequality at what one
  cell reads; the bound is met with equality on three
  Boolean cells at margins one and one
  (`margins_add_lt_card_of_readsOnly_nonvacuous`), and the inequality fails
  at an instance meeting every hypothesis but that one, at margins one and
  one against a set of one cell (`margins_add_lt_card_guard`). A radius-one
  rule's value at a cell after `τ` steps is fixed by the cells within `τ`
  of it (`finRule_iterate_apply_congr`), so on finitely supported states
  the margins at which its `τ`-step iterate erases (`ErasesAt`) sum to at
  most `2τ` at two states with different successors
  (`finRule_margins_add_le_two_mul`, its hypotheses met together at
  `finRule_margins_add_le_two_mul_nonvacuous`). On all functions of the line
  (`lineRule`, `ErasesWithin`), at a rule fixing both constant states: at no
  scale do both erase within two (`not_erasesWithin_two_const`), and at every
  positive scale both erase within one exactly when the rule is the majority
  of its three cells (`erasesWithin_one_const_iff`, `majRule`,
  `erasesWithin_one_const_majRule`); the zero state alone can erase within
  two (`erasesWithin_two_const_zero_guard`). At scale one, at every rule and
  on all functions of the line, two states each erasing within two have the
  same successor (`lineRule_eq_of_erasesWithin_two`), the two hypotheses met
  at two different states of the constant-zero rule
  (`lineRule_eq_of_erasesWithin_two_nonvacuous`); at the majority rule a
  margin of one at both constant states leaves the successors different
  (`lineRule_ne_of_erasesWithin_one_guard`). In no paper; it is
  the one-step form behind *Rule Space* §6. Boundary: the witnesses
  and counterexamples are existential statements, naming their margins and counts and
  not the function, rule or state that meets them; the scaled bound's witness
  has one margin zero, so the bound `2τ` is not shown attained; beyond scale
  one nothing is stated about two states that are not constant, and nothing at
  any scale about a rule of wider radius or more states, or about whether two
  finitely supported states can both hold a positive margin; `PersistentWord.lean`
  states every scale at a class of rules.
- **Erasing two cells at every scale** (`PersistentWord.lean`): a partial
  state on a finite set of cells forces a cell when every state extending it
  has one value there (`Forces`). At any update of the line commuting with
  translation, if a partial state on at most two cells forces some cell, every
  state erasing within two has a constant successor, the forced value
  (`eq_const_of_erasesWithin_two_of_forces`,
  `eq_of_erasesWithin_two_of_forces`), its hypotheses met at the product
  rule at scale two (`eq_of_erasesWithin_two_of_forces_nonvacuous`), and the
  two cells are needed: at the majority of five cells (`maj5Rule`) a
  partial state on three cells forces and the two constant states' successors
  differ (`eq_of_erasesWithin_two_of_forces_guard`). A rule has a persistent
  word when a chain of non-empty partial states, the first on at most two
  cells, is carried each into the next by one step (`StepsInto`,
  `HasPersistentWord`); then a two-cell partial state forces a cell at every
  scale (`HasPersistentWord.forces_iterate`, translation through
  `lineRule_iterate_shift`), at the majority rule
  (`hasPersistentWord_majRule`) and at the rule sending only `(0, 0, 1)` to
  one (`hasPersistentWord_lonelyOne`). At a rule permutive at an end
  (`LeftPermutive`, `RightPermutive`) no state erases within one at any scale
  (`LeftPermutive.not_erasesWithin_one`,
  `RightPermutive.not_erasesWithin_one`), rule `30` among them
  (`leftPermutive_rule30`). So at every rule with a persistent word or
  permutive at an end, at every scale, two states each erasing within two
  have the same successor
  (`lineRule_iterate_eq_of_erasesWithin_two_of_forcing`, its hypotheses met at
  the product rule at scale two,
  `lineRule_iterate_eq_of_erasesWithin_two_of_forcing_nonvacuous`). *Rule Space* Proposition 6.1. Boundary: the permutive half is
  vacuous; a persistent word bounds only its first member; the class is
  enumerated from below in `PersistentWordCount.lean`, and at a rule outside it
  nothing is stated past scale one.
- **The forcing class counted** (`PersistentWordCount.lean`): the three-valued step
  of a partial state (`stepWord`) keeps the cells at which one step of the
  rule has one value at every completion of the unknown neighbours; it is
  sound (`stepsInto_stepWord`), monotone in the known set (`stepWord_mono`)
  and commutes with translation (`stepWord_translate`). A word on at most two
  cells whose iterates are non-empty up to a step that contains a translate
  of an earlier iterate gives a persistent word
  (`hasPersistentWord_of_return`, its hypotheses met at the majority rule,
  `hasPersistentWord_of_return_nonvacuous`). The bounded form over six words,
  two steps and shifts of at most two cells is decidable (`ReturnsWithinTwo`)
  and sufficient (`ReturnsWithinTwo.hasPersistentWord`); over the 256
  radius-one rules it holds at 128, permutivity at an end at 28, both at 4
  and either at 152 (`card_returnsWithinTwo`, `card_permutiveEnd`,
  `card_returnsWithinTwo_and_permutiveEnd`, `card_forcingClass`), so the
  statement holds over that counted class
  (`lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass`, its hypotheses
  met at the product rule at scale two,
  `lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_nonvacuous`); the
  majority rule returns within two (`returnsWithinTwo_majRule`) and rule
  `90` does not (`not_returnsWithinTwo_add_ends`). *Rule Space*
  Proposition 6.2. Boundary: the certificate is sufficient and
  not shown necessary; the step is sound, not complete; nothing is stated
  about the 104 rules outside the class here, twelve of which
  `EndRegionClosure.lean` decides.
- **Twelve rules outside the forcing class** (`EndRegionClosure.lean`,
  data in `EndRegionCert.lean`): a region map packs the five-cell region a
  flip of a window's last five cells can reach, one word per flip pattern,
  into a natural number (`word`, `mkMap`); the step under a context pair
  (`stepMap`), the apex (`apex`), goodness at every pattern within two flips
  (`goodMap`), relabeling of the patterns (`relabel`) and membership up to it
  (`inCert`) make a Boolean check on a rule and a list (`certOK`), whose
  passing gives that no state of the line erases within two at any scale
  (`not_erasesWithin_two_of_certOK`, its hypotheses met at rule `38`,
  `not_erasesWithin_two_of_certOK_nonvacuous`; the check refuses rule `128`,
  `certOK_refuses_128`). The kernel decides the check at rules `38`, `46`,
  `66`, `139`, `155` and `189` (`certOK_38` to `certOK_189`), reflection
  carries erasure to the mirror rule (`erasesWithin_iterate_mirrorRule`),
  and the twelve rules (`endClosureRules`) each have no erasing state
  (`not_erasesWithin_two_of_mem_endClosureRules`), so the
  statement holds there vacuously and over the forcing class with them at
  164 rules (`card_forcingClass_or_endClosure`,
  `lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure`).
  *Rule Space* Proposition 6.3. Boundary: the lists
  are data the kernel checks; the twelve are listed, not characterized;
  nothing is stated at the 92 rules outside both.

### Reproduction and self-simulation

- **Rule 90's copies at rules that are not additive** (`ParityEmulation.lean`):
  a rule that agrees with rule 90 on the five neighbourhoods with no two
  adjacent set cells (`AgreesOffAdjacent`; eight rules,
  `card_agreesOffAdjacent`, rule 18 among them) steps as rule 90 does on every
  finitely supported state whose set cells lie on one parity
  (`OneParity.finRule_eq_f90`, `OneParity.iterate_eq_f90`), so a
  further power of two of steps gives two translated copies of the orbit
  (`OneParity.iterate_two_pow_add`), which do not overlap once the power
  exceeds the support's width (`two_pow_copies_disjoint`). At rule 18, from
  every state, setting cells that each sit between two set cells leaves the
  next state unchanged (`finRule_f18_add_gapFill`); off one parity the
  agreement fails (`f18_ne_f90_off_parity`), the gap is needed
  (`gapFill_erasure_needs_gap`), and rule 90 erases no such hit
  (`f90_does_not_erase_gapFill`). In no paper.
- **Rule 90 simulates itself** (`Decimation.lean`): keeping one cell in every
  `2 ^ M` (`decim`) takes `2 ^ M` steps of rule 90 to one step of rule 90 on
  the decimated state, at every state (`decim_iterate_f90`), and the map is
  onto (`decim_surjective`): a blocking transformation in Wolfram's (1986)
  sense. On the light cone it is a semiconjugacy
  (`positivelyInvariant_lightCone_iterate_f90`,
  `nonautonomousSemiconj_decim_f90`), its fibers the light cone of a window
  `2 ^ M` times narrower (`imageFiber_decim_f90`); two decimations compose
  into one (`decim_decim`), so they stack into a tower whose law never
  changes. Rule 30 admits no map on the even cells carrying its second
  iterate (`not_exists_decim_law_f30`). *Rule Space* Proposition
  5.7.

- **Rule 90 at half speed on doubled states** (`Doubling.lean`): writing each
  cell twice (`dbl`), every quiescent rule agreeing with rule 90 on the six
  neighbourhoods with two equal adjacent cells (`DoubledAgree`) takes the
  doubling of a state in two steps to the doubling of one step of rule 90
  (`finRule_two_dbl`), and in `2 ^ (M + 1)` steps to that of `2 ^ M`
  (`finRule_iterate_dbl`). Exactly four rules agree so
  (`card_doubledAgree`, `doubledAgree_cases`): 90, 94, 122 and 126. Rule 22
  does not, and two of its steps break a doubled state (`not_doubled_f22`).
  *Rule Space* Proposition 5.8.
- **The reproduction bracket** (`ReproductionBracket.lean`): a state is `k`
  copies of a pattern at gap `G` when it is the sum of `k` translates whose
  offsets step by at least the pattern's diameter plus `G` (`Copies`), and a
  map reproduces the pattern when every count and every gap are reached at
  some iterate (`Reproduces`; the exact-count form `ReproducesExactly` is
  refuted at rules 60 and 90, `not_reproduces_single_f90_f60`). The bracket
  (`reproduction_bracket`, its three hypotheses all proved,
  `reproduction_bracket_nonvacuous`): bounded diameter forbids reproduction
  (`copies_diam_le`, `not_reproduces_of_diamBounded`); every quiescent rule
  outside the 54 growing ones has bounded diameter from the
  per-rule bounds (`classify_outside_growing`,
  `diamBounded_of_not_growing`); and fourteen rules reproduce a pattern
  (`fourteen`, `reproduces_of_mem_fourteen`) — the linear rules a single
  cell by a squaring identity (`LinearTaps`, `LinearTaps.reproduces`), the
  seven agreeing with rule 90 off adjacent cells the two cells at distance
  two (`AgreesOffAdjacent.reproduces`), and the three doubled-agreement
  rules the adjacent pair (`DoubledAgree.reproduces`), each with a fixed
  instance. *Rule Space* Proposition 5.9. Boundary:
  neither end of the bracket is shown exact; three patterns only.

## Scope, and related formalizations

The carrier is the one every library of cellular automata on the line starts
from, a function from the integers to a finite alphabet, and the statements
here are about one thing those libraries do not treat: what the orbits of the
radius-one rules do — growth, eventual periodicity along columns, windows and
rays, reproduction, erasure. Read at the sources on 2026-10-09:
[hediet/lean-cellular-automata](https://github.com/hediet/lean-cellular-automata)
defines a radius-one automaton over an alphabet with an input embedding and an
output projection, its step the same neighbourhood update as here, and studies
cellular automata as language recognizers and real-time transducers; no
statement there is about an orbit's growth or a column.
[jkingsbery/ca-surjectivity](https://github.com/jkingsbery/ca-surjectivity)
defines a local rule of any width and its global map on the line and proves
that the map commutes with the shift, towards the Garden-of-Eden theorem.
Mathlib's symbolic-dynamics file (`Mathlib.Dynamics.SymbolicDynamics.Basic`) defines shifts, cylinders,
patterns and subshifts, and no cellular-automaton map.

A second read on 2026-10-11 found three neighbours in the literature and one in
another prover. Wolfram's 1986 tables of cellular automaton properties list, as
computed rows without proof, the three block mechanisms proved here: rules 18,
26, 146 and 154 simulating rule 90 on the blocks `00` and `10`, rules 94, 122
and 126 simulating it on the blocks `00` and `11`, and rule 90 simulating
itself, each in two steps (`ParityEmulation.lean`, `Doubling.lean`,
`Decimation.lean`). Brummitt and Rowland (2012) observed, from one seed and by
experiment, the unbounded growth of rules 106 and 120 that `Growth.lean`
proves, and the Markov error count is, before normalization, the Markov
predictability of Feder, Merhav and Gutman (1992). In cubical Agda,
[avikj/math](https://github.com/avikj/math) proves at rule 30 from a single
seed that no two adjacent columns are both eventually periodic and that every
right diagonal is periodic; no statement of this library was found in any
prover.

A preprint read on 2026-10-13, Chan-López and Martín-Ruiz (2026), gives rule
22's rows from a single cell in closed form, from which rule 22 reproduces a
single cell; that is not proved here, and the reproduction bracket's fourteen
do not include it. Corrections are welcome as issues.

What is not here: Wolfram's four classes, which are not a formal notion; rules
of wider radius or more states; and the surjectivity of the permutive rules, a
theorem of the literature the library does not state.

## Papers

This library has one paper, *Growth, Rays and the Erasure of Local
Perturbations in the Elementary Cellular Automata* (`[RuleSpace]`, in
preparation), self-contained: it defines every object it uses, cites the
classical results it stands on at their sources, and states the results proved
here at the numbers the docstrings cite by key; a statement with no key is
library content the paper does not state.

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).
- **Build-enforced axiom hygiene**: 520 `#guard_msgs in #print axioms` guards
  assert each capstone's exact axiom set — most in the audit modules
  `Nonautonomous/AxiomAudit.lean` and `ECA/AxiomAudit.lean`, the
  rest in-file in the modules they certify; `lake build` fails on any drift.
- **CI-enforced whole-library audit**: every declaration under
  `Nonautonomous` and `ECA` is checked against the checked-in
  `forgive.yml` by [`forgive`](https://github.com/FormalizedFormalLogic/forgive) on each CI run.
- **Targeted imports and module-system code**: every module names exactly the
  Mathlib files it uses, and every file is a Lean `module`.

## Building

Pinned toolchain (`lean-toolchain`, `lake-manifest.json`):

```bash
lake exe cache get
lake build Nonautonomous ECA
```

As a dependency:

```toml
[[require]]
name = "elementary_cellular_automata"
git = "https://github.com/lividgreen/lean-elementary-cellular-automata"
rev = "<tag>"  -- pin to a tagged release
```

## Citation and license

See `CITATION.cff` — concept DOI
[10.5281/zenodo.23275249](https://doi.org/10.5281/zenodo.23275249)
always resolves to the latest archived version. For a specific tagged
version and its own version DOI, see the
[GitHub Releases page](https://github.com/lividgreen/lean-elementary-cellular-automata/releases)
and `CITATION.cff`. Code is Apache-2.0 (`LICENSE`). Developed by Mykola
Palamarchuk (independent researcher), with substantial AI assistance (Claude
Code, Anthropic) under the author's direction and review — every result is
machine-checked by Lean.
