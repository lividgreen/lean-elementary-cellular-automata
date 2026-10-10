# lean-elementary-cellular-automata

[![CI](https://github.com/lividgreen/lean-elementary-cellular-automata/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/lividgreen/lean-elementary-cellular-automata/actions/workflows/lean_action_ci.yml)
[![API docs](https://img.shields.io/badge/docs-API%20reference-4c1)](https://lividgreen.github.io/lean-elementary-cellular-automata/)
[![Lean](https://img.shields.io/badge/Lean%204-Mathlib-black)](https://leanprover-community.github.io/)
[![License](https://img.shields.io/badge/license-Apache--2.0-lightgrey)](LICENSE)

**The radius-one rule space, machine-checked in Lean 4: which elementary
cellular automata grow, what an observer of one cell, window or ray of them
pays, and what robustness to two cells costs — every quiescent table decided.**

The elementary cellular automata are the 256 rules on a line of binary cells
in which a cell's next value depends on itself and its two neighbours. This
library reads them as hosts nobody built to carry anything, and asks of every
rule at once whether the patterns it carries grow, in a sense defined here: the
growing width, the largest number of co-present retained classes among the
states whose orbits grow. At every one of the 128 quiescent rules that width
is zero at every stage or unbounded, and it is unbounded at exactly 54 of them
(`accretion_census`). The library also reads rule `90`'s orbit from a single
cell along rays of every rational speed, decides which columns and windows of a
table settle, brackets which tables replicate a pattern, and shows what erasing
every perturbation of two cells costs a table at every scale.

The classical results these proofs use — a finite system driven by an
eventually periodic input settles, Jen's lemma on the columns between two
settled columns, rule `90`'s `2^j` identity, Pascal's triangle modulo two and
Lucas's criterion at the prime two — are in
[lean-classical-upstream](https://github.com/lividgreen/lean-classical-upstream)
(concept DOI [10.5281/zenodo.23257423](https://doi.org/10.5281/zenodo.23257423)),
which this package requires. What is here is what nobody had stated before.

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).
- **Build-enforced axiom hygiene**: 494 `#guard_msgs in #print axioms` guards
  assert each capstone's exact axiom set — most in the audit module
  `CellularAutomata/AxiomAudit.lean`, the rest in-file in the modules they
  certify; `lake build` fails on any drift.
- **CI-enforced whole-library audit**: every declaration under
  `CellularAutomata` is checked against the checked-in `forgive.yml` by
  [`forgive`](https://github.com/FormalizedFormalLogic/forgive) on each CI run.
- **Targeted imports and module-system code**: every module names exactly the
  Mathlib files it uses, and every file is a Lean `module`.

## Building

Pinned toolchain (`lean-toolchain`, `lake-manifest.json`):

```bash
lake exe cache get
lake build CellularAutomata
```

As a dependency:

```toml
[[require]]
name = "elementary_cellular_automata"
git = "https://github.com/lividgreen/lean-elementary-cellular-automata"
rev = "<tag>"  -- pin to a tagged release
```

## What is proved here

Module names follow the paper's sections; the namespaces inside some modules
keep the names they had when the library was part of a larger one.

### The growing world and its widths

- **Growing worlds and the merge quotient** (`MergeQuotient.lean`): a growing
  world is an update with a family of stages it advances (`Advances`); a reading
  closing the staged square (`StagedSquare`) has its own stages
  (`guestStage`), and they advance under the law (`advances_guestStage`). Two
  states merge when some common iterate identifies them (`Merges`); the
  quotient's induced law is injective with no hypothesis (`mergeLaw_injective`),
  closes the staged square at every stage family (`stagedSquare_merge`), and
  every reading with an injective law factors through it
  (`merges_invariant_of_stagedSquare`, `exists_mergeMk_injective`); the
  retained classes of a stage (`mergeStage`) advance and inject stage to stage
  (`advances_mergeStage`, `mergeStage_injOn`). Registered as *Rule Space*
  Definitions 2.1 and 2.2 and Propositions 2.5 and 2.6, rows RS-34 to RS-36.
- **The memory width: a clock is not a memory** (`MemoryWidth.lean`): the
  antichain width of the retained profile under the induced law's
  reachability (`memWidth`, `ℕ∞`-valued), monotone with no hypothesis beyond
  `Advances` (`memWidth_mono`). The successor world's retained profile is
  unbounded while its width stays at one (`memWidth_nat_succ_eq_one`), and a
  fast counter has a profile in bijection with `Bool^t` at every stage, with
  the same width
  (`mergeStage_nat_succ_fastClock_encard`): the raw class count decides
  nothing. The width is
  read off a **root set**: a subset of a stage that is already an antichain
  and which every stage class reaches names the width exactly, with no
  hypothesis on the update (`memWidth_eq_encard_of_isRootAntichain`; at a
  state-level root set, `memWidth_eq_encard_of_rootSet`); a root antichain
  always exists at a finite stage (`exists_isRootAntichain_of_finite_stage`,
  classically), and under antisymmetry it is exactly the stage classes no
  other stage class reaches (`memWidth_eq_encard_canonical_of_antisymmOn`),
  each hypothesis pinned by a guard — the canonical set is empty at a finite
  world whose width is positive (`exists_canonicalSet_empty_pos_memWidth`),
  and the successor world on `ℤ` has positive width and no root antichain at
  all (`pos_memWidth_not_exists_isRootAntichain_intSucc`). Boundary: a
  separation, not a dichotomy — a reading with an injective law whose stage
  image is an antichain under its own law can exceed the width
  (`exists_conservationGuest_extent_gt_memWidth`). Registered as *Rule Space*
  Propositions 2.6 to 2.8, rows RS-36 to RS-38.
- **Derived worlds, and the width computed exactly at elementary cellular
  automata** (`DerivedStages.lean`, `PermutiveWidth.lean`): a world grown from a start region as its iterated
  images (`derivedStages`) has its retained profile, hence its memory width,
  capped by the region's own cardinality at every stage
  (`memWidth_derivedStages_le`), so a finite start region caps the memory a
  derived world can hold. On the finitely-supported configurations of the
  line, the extreme-tap linear rules — elementary tables `90` and `150`
  (`rule90`, `rule150`) — are additive and injective (`rule90_injective`),
  spread their support by exactly one cell per step at each end, and every
  nonzero orbit eventually leaves any fixed finite region
  (`rule90_region_exit`); on the world derived from an `n`-cell region, read
  at the region itself, their width is at least `2^(n−1)`
  (`memWidth_rule90_derived_ge`) and exactly the size of the **root set**, the
  region-supported states with no nonzero region-supported predecessor
  (`rootSet`, `memWidth_rule90_derived_eq`), a count that closes in addition
  form, `(rootSet rule90 n).encard + 2^(n−2) = 2^n + 1` at `2 ≤ n`
  (`rootSet_encard_add`). Both facts are generic in the update and in two
  endpoint-move constants (`memWidth_derived_eq_encard_rootSet`,
  `rootSet_encard_add_of_hyps`), the identity update the guard that separates
  them (`guard_id_rootSet_load_bearing`); a local table with a quiescent zero
  becomes a radius-one rule (`tableRule`), one-sided permutivity in solved
  form gives injectivity on that carrier
  (`tableRule_injective_of_leftPermutive`,
  `tableRule_injective_of_rightPermutive`), and four non-additive tables —
  `30`, `86`, `154`, `210` — meet the hypotheses and share the exact width,
  rule `30`'s equal to rule `90`'s (`memWidth_rule30_derived_eq_rule90`); the
  two shifts, tables `170` and `240`, carry their own width and count at their
  true endpoint moves (`memWidth_rule170_derived_eq`,
  `rootSet_encard_add_rule170`, `memWidth_rule240_derived_eq`), and a guard
  shows quiescence and permutivity alone do not pin the class-level spread
  (`guard_rule170_max'_spread_load_bearing`). Registered as *Rule Space*
  Propositions 2.9 to 2.11, rows RS-39 to RS-41. Boundary: the counts are
  additive (`ℕ∞` subtraction is truncated), the closed forms being the paper's
  restatement; the permutivity-to-injectivity route is classical; the derived
  cap says nothing about attainment beyond the tables named.
- **The growing width: six tables accrete, the identity does not**
  (`GrowingWidth.lean`, `LightConeWidth.lean`): the memory width restricted to
  the states whose orbit has unbounded size (`GrowingPart`, `growingWidth`) —
  the part invariant and merge-saturated (`growingPart_of_merge`), the
  restricted family advancing (`advances_growingPart`), the width monotone and
  below the plain one (`growingWidth_mono`, `growingWidth_le_memWidth`), and a
  genuine restriction: `0` against `t + 1` at the identity
  (`growingWidth_id_slowClock_eq_zero_memWidth_eq_succ`). Under the support
  diameter (`diam`) and along the light cone of an `n`-cell window
  (`lightCone`), an update with exact endpoint moves `(1, 1)` has the nonzero
  states as its growing part (`growingPart_eq_ne_zero`), and with a trivial
  kernel and injectivity its growing width is at least `2^(n+t−1)`
  (`two_pow_le_growingWidth_lightCone`), hence unbounded
  (`growingWidth_lightCone_unbounded`) — instantiated at tables `30`, `86`,
  `90`, `150`, `154`, `210` (`growingWidth_lightCone_unbounded_rule30`, …),
  jointly satisfiable at rule `90`, and `0` at the identity and both shifts
  (`growingWidth_lightCone_id_eq_zero`,
  `growingWidth_lightCone_rule170_eq_zero`). The plain width along the same
  cone is unbounded even at the identity, so this is the quantity that sees
  the rule. Registered as *Rule Space* Definition 2.3 and Propositions 2.12
  and 2.13, rows RS-34, RS-42 and RS-43. Boundary: a lower bound, not the value; the rate is the
  presentation's; the diameter is one reading of size; the part is not
  decidable in general; a separation at a hypothesis class, not genericity.

### Accretion over the rule space

- **The growing width over the whole radius-one rule space: an engine without
  injectivity, and a bracket at the table bits** (`EndpointClasses.lean`): an
  antichain of the retained profile is a set of states with pairwise disjoint
  forward orbits, so at exact endpoint moves `(a, b)` with `a + b ≥ 1` on any
  update-invariant set containing every translate of one state, the
  translates in the light cone are pairwise orbit-disjoint and each is
  growing — the growing width is at least `n + 2t + 1 − diam s₀`
  (`linear_le_growingWidth_lightCone_of_invariant`), hence unbounded
  (`growingWidth_lightCone_unbounded_of_invariant`), with the six hypotheses
  jointly met at table `202` on the right end-word set
  (`growingWidth_lightCone_unbounded_of_invariant_nonvacuous`). The moves are
  read off a table's bits (`tableRule_min'_of_leftTap`,
  `tableRule_max'_of_rightHold`, `tableRule_max'_of_endsOneOne`, …), every
  quiescent table advances the cone (`advances_lightCone_tableRule`), and a
  non-increasing diameter empties the growing part
  (`growingPart_eq_empty_of_diam_le`). Two classes of tables, each a
  disjunction of bit equations: `AccretesByEndpoints` — unbounded growing
  width at every member (`growingWidth_lightCone_unbounded_of_accretesByEndpoints`),
  `52` of the `128` quiescent tables (`card_accretesByEndpoints`,
  `card_quiescent`) — and `ZeroByEndpoints` — width identically `0`
  (`growingWidth_lightCone_eq_zero_of_zeroByEndpoints`), `48` tables
  (`card_zeroByEndpoints`) — disjoint
  (`accretesByEndpoints_zeroByEndpoints_disjoint`). Registered as *Rule Space*
  Proposition 3.1, rows RS-1 and RS-2. Boundary: the bound is linear where
  the six-table one is exponential; the `28` tables in neither class are not
  decided by these two classes (`Accretion.lean` decides eighteen of them and
  `BlockCount.lean` the other ten);
  the counts are kernel decisions over the
  256-element table type; the instances at rules `90` and `150` are at tables
  written out here, with no stated identity to `rule90` and `rule150`.
- **Zero or unbounded, by one state** (`Accretion.lean`): at every quiescent
  radius-one table, one state whose orbit has unbounded diameter gives a
  linear lower bound on the growing width along the light cone
  (`linear_le_growingWidth_lightCone_of_mem_growingPart`), so the width is
  zero at every stage or unbounded (`growingWidth_lightCone_zero_or_unbounded`).
  A diameter that grows by at most a constant gives zero (`DiamBoundedBy`,
  `growingWidth_lightCone_eq_zero_of_diamBoundedBy`), and both sides pass to
  the mirror table by reflection (`reflect`, `mirrorTable`,
  `tableRule_mirrorTable_reflect`, `diamBoundedBy_mirrorTable`,
  `reflect_mem_growingPart_mirrorTable`). Registered as *Rule Space* Proposition
  3.2, row RS-18. Rule 106 and its mirror, rule 120, are the first tables
  between the two endpoint classes decided: the update at `f106` is injective
  (`tableRule_f106_injective`), the two-cell state `seedOneOne` is the image
  of no state (`seedOneOne_notMem_range_f106`), and at an injective update
  with a left tap such a state has an orbit of unbounded diameter
  (`mem_growingPart_of_injective_of_notMem_range`), so the width is unbounded
  at both (`growingWidth_lightCone_unbounded_f106`,
  `growingWidth_lightCone_unbounded_mirror_f106`). Registered as *Rule Space*
  Proposition 3.3, row RS-19. Rules 38, 46, 66 and 174 and their mirrors do
  not accrete: a set of pairs of end values closed under the rule, on which
  the cell past the end dies, holds every orbit's diameter within two of its
  start's (`diamBoundedBy_two_of_endClosure`, `diamBoundedBy_f38`,
  `diamBoundedBy_f46`, `diamBoundedBy_f66`, `diamBoundedBy_f174`), so the
  width is zero (`growingWidth_lightCone_eq_zero_f38` and its seven
  siblings). Registered as *Rule Space* Proposition 3.4, row RS-20. Rule 166 and
  its mirror, rule 180, do not accrete either: every orbit's diameter is
  within one of its start's (`diamBoundedBy_f166`), by an invariant of the
  last block's parity, and the twelve tables are one statement with no
  hypothesis (`growingWidth_lightCone_middle_twelve`). Registered as *Rule Space*
  Proposition 3.5, row RS-21. The traffic class does not accrete: at every
  table that is one only where the traffic rule 184, mirrored, is one, a set
  cell stays or is pushed by the two cells behind it, and no orbit's diameter
  exceeds twice its start's (`diam_iterate_le_two_mul_of_traffic`), so the
  width is zero there and at the mirror
  (`growingWidth_lightCone_eq_zero_of_traffic`,
  `growingWidth_lightCone_eq_zero_mirror_of_traffic`); rules 98, 194 and 226
  are members (`f98_traffic`, `f194_traffic`, `f226_traffic`), and with
  their mirrors, rule 184 among them, six tables are decided
  (`growingWidth_lightCone_traffic_six`). The class is needed
  (`traffic_hypothesis_load_bearing`). Registered as *Rule Space* Proposition
  3.6, row RS-22. Boundary: no rate of the diameter is stated at rule 106.
- **The last ten tables, by a count of blocks** (`BlockCount.lean`): a
  count that grows by one a step only where two further counted cells stand
  within a fixed distance behind stays under a line
  (`count_invariant_of_step`). Counting block starts, a table that sets a cell
  only where its left neighbour was clear and it or its right neighbour was
  set holds every orbit's diameter within five times its start's plus five
  (`diam_iterate_le_of_leftClear`); rules 6 and 14 are members. Counting block
  ends gives the same bound at rule 142 (`diam_iterate_le_f142`); at rule 134
  long runs shorten until the update is rule 6's (`diam_iterate_le_f134`);
  at rule 74 the starts of blocks of two or more are counted after three
  steps (`diam_iterate_le_f74`). An affine diameter bound gives zero width
  (`growingWidth_lightCone_eq_zero_of_diam_le_affine`), so the ten tables —
  these five and their mirrors — do not accrete
  (`growingWidth_lightCone_middle_ten`). Registered as *Rule Space* Proposition
  3.7, rows RS-23 to RS-25. Boundary: no constant is shown sharp. That 54 of
  the 128 quiescent tables accrete is one theorem over the Wolfram numeral
  (`accretion_census`), *Rule Space* Proposition 3.8, row RS-32.
- **The census over the Wolfram numeral** (`WolframNumber.lean`): `eca n` is
  the table with Wolfram number `n < 256`, equal to every hand-written table at
  its number (`eca_30`, `eca_90`, …), with reflection and complement as maps on
  the numbers (`eca_mirrorNum`, `eca_complementNum`) and the eight additive
  tables counted (`card_additive`). A number is accreting when its table lies
  in the endpoint engine's class or is table `106` or `120` (`Accreting`), a
  decided condition, and at every quiescent number the growing width along every
  light cone is unbounded when it is accreting and zero at every stage when it
  is not, with 128 quiescent numbers, 54 accreting and 74 not
  (`accretion_census`, both branches met at tables `90` and `170` by
  `accretion_census_nonvacuous`). Registered as *Rule Space* Proposition 3.8,
  row RS-32.

### Columns, windows and rays

- **The observed column settles wherever the diameter never grows**
  (`ObservedColumn.lean`): the column an observer reads at one cell along an
  orbit (`observedColumn`) is eventually periodic at every quiescent table
  whose diameter never grows (`eventuallyPeriodic_observedColumn_of_diam_le`)
  — the pattern up to translation ranges over a finite set, so it recurs
  with a drift, and the column is periodic at zero drift and eventually `0`
  otherwise — hence at every zero-class table
  (`eventuallyPeriodic_observedColumn_of_zeroByEndpoints`); contrapositively
  a column that is not eventually periodic forces the diameter to grow at
  some stage of that seed's own orbit
  (`exists_diam_lt_iterate_of_not_eventuallyPeriodic`). The hypotheses are
  met at the shift `170` with its center column written out
  (`observedColumn_f170_single`), and the diameter hypothesis is load-bearing
  at rule `30` (`diam_lt_tableRule_f30_single`). The converse fails at a
  checked witness: rule `90` is in the accreting class and its single-seed
  center column is `1` then `0` forever (`observedColumn_f90_single`).
  The rational ray at speed `p/q` reads the cell `e + ⌊pt/q⌋` at step `t`
  (`observedRationalRay`), the column at speed zero
  (`observedRationalRay_zero`); at every quiescent table whose diameter never
  grows every rational ray is eventually periodic
  (`eventuallyPeriodic_observedRationalRay_of_diam_le`), reading one relative
  cell of the drifting pattern for ever when its speed is the drift and zero
  for ever otherwise, hence at every zero-class table
  (`eventuallyPeriodic_observedRationalRay_of_zeroByEndpoints`), the
  hypotheses met at the shift at speed one half
  (`eventuallyPeriodic_observedRationalRay_of_diam_le_nonvacuous`). The
  column's statements are registered as *Rule Space* Remark 4.1, rows RS-3 and
  RS-4, the rational ray as *Rule Space* Proposition 4.4, row RS-9. Boundary:
  existence of a
  period only, no bound on it or on the onset; one column or ray, not the
  configuration; beyond that one column of rule `90`, this module says nothing
  about the column or any ray at a table whose diameter grows, rule `30`'s
  included.
- **Driven columns: what settles at every table, and a column that never
  does** (`ObservedRays.lean`, on `DrivenColumns.lean` and
  `LocalRuleColumns.lean` of lean-classical-upstream): a sequence in a finite type whose next
  value is, from some step on, a fixed function of its value and of an
  eventually periodic input is eventually periodic
  (`eventuallyPeriodic_of_driven`). Over the table rules this gives, at
  every quiescent table and every finitely-supported state: a window of
  adjacent cells is eventually periodic exactly when the columns at its two
  end cells are (`eventuallyPeriodic_observedWindow_iff`), so the columns
  between two settled columns settle
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
  `observedColumn_f90_single_one_dead_between`). One settled end does not
  settle the cell beside it
  (`eventuallyPeriodic_observedColumn_between_guard`), and the rays'
  statement fails at velocity zero
  (`not_eventuallyPeriodic_observedRay_zero_f90`). The interior, the
  `2^j` identity and the column's non-periodicity are instances of the
  classical package's statements for any local rule on every configuration
  of the line (`coe_tableRule_iterate`). Registered as *Rule Space*
  Proposition 4.2, rows RS-5, RS-6 and RS-31. Its column at cell `1` is also
  one equality, live exactly at the steps `t` with `t + 1 = 2^j` for some
  `j ≥ 1` (`observedColumn_f90_single_one`), and the driven interior's
  hypotheses are met together at the shift
  (`eventuallyPeriodic_observedColumn_between_nonvacuous`). Boundary:
  existence of a period only; velocities `1` and `−1` only; nothing about
  any other column of rule `90`, any other seed, or any column of another
  accreting table.
- **The hindsight count: a law on the last readings, and what bounds its
  misses** (`HindsightCount.lean`): a sequence is
  eventually exact at memory
  `k` when one fixed function of its last `k` readings gives the next
  reading from some step on (`EventuallyExact`). An eventually periodic
  sequence is eventually exact at some memory
  (`eventuallyExact_of_eventuallyPeriodic`), and over a finite alphabet the
  converse holds (`eventuallyPeriodic_of_eventuallyExact`), the two together
  one equivalence (`exists_eventuallyExact_iff_eventuallyPeriodic`); the
  finite alphabet is load-bearing, the identity on the naturals being
  eventually exact at memory one and not eventually periodic
  (`eventuallyExact_nat_id_not_eventuallyPeriodic`). The hindsight count at
  a horizon is the fewest misses any such function makes before it, the
  minimum taken at each horizon separately (`lawMisses`, `hindsightCount`);
  over a finite alphabet it is bounded in the horizon exactly when the
  sequence is eventually exact at that memory
  (`hindsightCount_bounded_iff_eventuallyExact`), and bounded at some memory
  exactly when the sequence is eventually periodic
  (`exists_hindsightCount_bounded_iff_eventuallyPeriodic`). At every
  quiescent table and every finitely-supported state, a window of adjacent
  cells meets either condition at some memory exactly when the columns at
  its two end cells do, each at a memory of its own
  (`exists_eventuallyExact_observedWindow_iff`,
  `exists_hindsightCount_bounded_observedWindow_iff`). At rule `90` from the single seed the center column is eventually
  exact at memory zero (`eventuallyExact_observedColumn_f90_single`) and the
  column at cell `1` at no memory
  (`not_exists_eventuallyExact_observedColumn_f90_single_one`), its
  hindsight count unbounded at every memory
  (`hindsightCount_observedColumn_f90_single_one_unbounded`). The two are the
  two sides of one class statement: at every table of the zero class, from
  every finitely-supported state and at every cell, some memory gives the
  column's hindsight count a bound in the horizon
  (`exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints`), and so
  for every window of adjacent cells
  (`exists_hindsightCount_bounded_observedWindow_of_zeroByEndpoints`), both
  hypotheses met at the shift `170`
  (`exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints_nonvacuous`);
  and the class hypothesis is load-bearing, rule `90` lying in the accreting
  class with its cell-one count unbounded
  (`exists_hindsightCount_bounded_observedColumn_zero_class_guard`) — the
  observer's bill read against the world's growth, bounded wherever the world
  does not accrete. The two window statements are registered as *Rule Space*
  Proposition 4.3(i), row RS-7; the rest is registered in no paper and
  extends *Rule Space* Propositions 3.1 and 4.2. Boundary: the memories and the
  bounds on the two sides of an equivalence are separate existentials, none
  given in terms of another; no rate of the count is stated; the class
  statement says nothing at the twenty-eight tables in neither class.
- **A window's count against its ends'** (`WindowCount.lean`): the hindsight
  count of a reading is the fewest misses, over the functions of the last
  `k` states, in answering a fixed function of the next state
  (`readingMisses`, `readingCount`); at the identity it is the hindsight
  count (`readingCount_id`). A reading's count is at most the state's
  (`readingCount_le_hindsightCount`), and at most the count of the read
  sequence taken on its own (`readingCount_le_hindsightCount_comp`). At
  every quiescent table, every finitely-supported state, every window, every
  memory of at least one and every horizon, the window's hindsight count is
  at most the sum of the counts of its two end cells read with the window as
  context (`hindsightCount_observedWindow_le_add_readingCount`), hence at
  most the sum of its two end columns' hindsight counts
  (`hindsightCount_observedWindow_le_add_columns`); by the first comparison
  it is at least each end reading's count. The memory is load-bearing: at
  memory zero the bound fails at the table that sends everything to zero
  (`hindsightCount_observedWindow_zero_memory_guard`). The end columns' own
  counts give no lower bound: at the shift, a window of two cells has no
  miss in three steps at memory one while the column at its first cell has
  one (`hindsightCount_observedWindow_lt_column_f170`). The translating window
  at a rational speed `p/q` of at most one, read with the phase `t mod q` of
  its own schedule (`movingWindow`), has at every quiescent table, every
  finitely-supported state, every start, every width of at least three, every
  memory of at least one and every horizon a hindsight count at most the sum
  of its two end readings' counts, the trailing end's the cell it sits on and
  the leading end's the two cells it sits on and moves to
  (`hindsightCount_movingWindow_le_add_readingCount`), the hypotheses met at
  table `90` at speed one half
  (`hindsightCount_movingWindow_le_add_readingCount_nonvacuous`) and the
  memory load-bearing at the zero table, where a memory-zero law cannot follow
  the phase (`hindsightCount_movingWindow_zero_memory_guard`). The window at
  rest is registered as *Rule Space* Proposition 4.3(ii)–(iii), row RS-8; the
  translating window is registered in no paper. Boundary: both sides of each
  bound are at the same memory and horizon; no bound is stated at memory zero,
  none for a window whose ends move at different speeds or at a speed above
  one, and each guard is a single instance.
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
  (`f90_iterate_two_pow_add`), and the disjointness is load-bearing, the
  rule reading zero at step two at the seeded cell (`oneOfDisjoint_guard`).
  The third condition is proved at every speed below one, from every cell
  (`lateZeroRuns`), and fails at speed one, where the ray rides the edge and
  never reads a zero (`lateZeroRuns_guard`). The second condition and the
  unconditional theorems are in `RationalRayPairs.lean`. Registered as
  *Rule Space* Proposition 5.1, row RS-11. Boundary: one table and one seed;
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
  Registered as *Rule Space* Proposition 5.1, row RS-11. Boundary: rule `90`
  and the single seed only; existence of the ones and the zero runs, with
  no density or rate; rays toward decreasing cells are not stated.
- **A second seed of rule 90** (`RationalRaySeeds.lean`): from the single
  seed, rule 90 reads `0` at cell `a - b` at step `a + b` whenever `a` and
  `b` share a binary digit (`zeroOfShared`, the converse of
  `oneOfDisjoint`), and at every cell whose sum with the step is odd
  (`f90_single_apply_eq_zero_of_odd`). One step sends the single cell `1`
  to the two-cell seed `{0, 2}` (`tableRule_f90_single_one`), whose orbit
  is the single seed's one step later, moved one cell
  (`f90_pair_iterate_apply`); so from that seed the rational ray of speed
  `1/3` from cell `1` reads `0` at every step and is eventually periodic
  (`observedRationalRay_f90_pair_eq_zero`,
  `eventuallyPeriodic_observedRationalRay_f90_pair`), the single seed of
  the rays above being load-bearing. Registered as *Rule Space* Proposition
  5.2, row RS-12. At every speed `1/(2^m - 1)`, `m >= 2`, the single seed
  reads `0` at cell `(s - 1) / (2^m - 1)` at every step `s >= 1`
  (`f90_single_apply_zeroLine`, through the digit lemma
  `and_sub_div_two_pow_ne_zero`), so the ray of that speed reads `0` at
  every step from the two-cell seed and from one step of the single seed
  advanced by any multiple of `2^m - 1` steps
  (`observedRationalRay_f90_pair_eq_zero_pow`,
  `observedRationalRay_f90_zeroLine`). Registered as *Rule Space* Proposition
  5.3, row RS-13. Boundary: these speeds and seeds; that no other ray
  settles is not stated.
- **The rate of rule 90's rays** (`RationalRayRate.lean`): from the single
  seed, the ray of speed `1/2` from cell `1` reads `1` exactly at the steps
  `(4^(i+1) - 1)/3` and twice them
  (`observedRationalRay_f90_single_half_one_iff`, through the digit lemmas
  `and_three_mul_add_one_eq_zero_iff` and
  `and_three_mul_add_two_eq_zero_iff`), and the ray of speed `1/3` from cell
  `0` exactly at the steps `3b` with `b &&& 2b = 0`
  (`observedRationalRay_f90_single_third_one_iff`, the classical parity of
  `C(3n, n)`). The hindsight count of any binary sequence is at most its
  ones (`hindsightCount_le_card_ones`), so the speed-`1/2` ray's count is at
  most `2 * Nat.log 4 (T + k) + 2` (`hindsightCount_f90_single_half_le`).
  Registered as *Rule Space* Proposition 5.4, row RS-14. Boundary: two rays of
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
  `card_ones_observedRationalRay_f90_single_le`). Registered as *Rule Space*
  Proposition 5.5, rows RS-15 and RS-16. Boundary: positive coefficients
  (`lineCount_not_le_fib_of_neg`); an upper bound only.
- **The lines of rule 90 that settle** (`RationalRayLines.lean`): the line of
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
  (`observedRationalRay_f90_iterate_single_eq_line`). Registered as *Rule Space*
  Proposition 5.6, row RS-17. Boundary: the single seed and its orbit.

### Robustness to small perturbations

- **The margin a cell's reading allows** (`LocalMargin.lean`): a function of
  a state reads only a finite set of cells when its value is fixed by them
  (`ReadsOnly`), and holds within `e` at a state when every state differing
  from it at no more than `e` cells gives the same value (`HoldsWithin`). If
  a function reads only `N` and takes different values at two states, the
  two margins at which those values hold sum to less than the number of
  cells of `N` at which the states differ
  (`margins_add_lt_card_of_readsOnly`), a packing inequality read at what one
  cell reads; the bound is met with equality on three
  Boolean cells at margins one and one
  (`margins_add_lt_card_of_readsOnly_nonvacuous`), and the inequality fails
  at an instance meeting every hypothesis but that one, at margins one and
  one against a set of one cell (`margins_add_lt_card_guard`). A radius-one
  table's value at a cell after `τ` steps is fixed by the cells within `τ`
  of it (`tableRule_iterate_apply_congr`), so on finitely-supported states
  the margins at which its `τ`-step iterate erases (`ErasesAt`) sum to at
  most `2τ` at two states with different successors
  (`tableRule_margins_add_le_two_mul`, its hypotheses met together at
  `tableRule_margins_add_le_two_mul_nonvacuous`). On all functions of the line
  (`lineRule`, `ErasesWithin`), at a table fixing both constant states: at no
  scale do both erase within two (`not_erasesWithin_two_const`), and at every
  positive scale both erase within one exactly when the table is the majority
  of its three cells (`erasesWithin_one_const_iff`, `majTable`,
  `erasesWithin_one_const_majTable`); the zero state alone can erase within
  two (`erasesWithin_two_const_zero_guard`). At scale one, at every table and
  on all functions of the line, two states each erasing within two have the
  same successor (`lineRule_eq_of_erasesWithin_two`), the two hypotheses met
  at two different states of the constant-zero table
  (`lineRule_eq_of_erasesWithin_two_nonvacuous`); at the majority table a
  margin of one at both constant states leaves the successors different
  (`lineRule_ne_of_erasesWithin_one_guard`). Registered in no paper; it is
  the one-step form behind *Rule Space* §6. Boundary: the witnesses
  and guards are existential statements, naming their margins and counts and
  not the function, table or state that meets them; the scaled bound's witness
  has one margin zero, so the bound `2τ` is not shown attained; beyond scale
  one nothing is stated about two states that are not constant, and nothing at
  any scale about a table of wider radius or more states, or about whether two
  finitely-supported states can both hold a positive margin; `PersistentWord.lean`
  states every scale at a class of tables.
- **Robustness to two cells at every scale** (`PersistentWord.lean`): a partial
  state on a finite set of cells forces a cell when every state extending it
  has one value there (`Forces`). At any update of the line commuting with
  translation, if a partial state on at most two cells forces some cell, every
  state erasing within two has a constant successor, the forced value
  (`eq_const_of_erasesWithin_two_of_forces`,
  `eq_of_erasesWithin_two_of_forces`), its hypotheses met at the product
  table at scale two (`eq_of_erasesWithin_two_of_forces_nonvacuous`), and the
  two cells are load-bearing: at the majority of five cells (`maj5Rule`) a
  partial state on three cells forces and the two constant states' successors
  differ (`eq_of_erasesWithin_two_of_forces_guard`). A table has a persistent
  word when a chain of non-empty partial states, the first on at most two
  cells, is carried each into the next by one step (`StepsInto`,
  `HasPersistentWord`); then a two-cell partial state forces a cell at every
  scale (`forces_iterate_of_hasPersistentWord`, translation through
  `lineRule_iterate_shift`), at the majority table
  (`hasPersistentWord_majTable`) and at the table sending only `(0, 0, 1)` to
  one (`hasPersistentWord_lonelyOne`). At a table permutive at an end
  (`LeftPermutive`, `RightPermutive`) no state erases within one at any scale
  (`not_erasesWithin_one_of_leftPermutive`,
  `not_erasesWithin_one_of_rightPermutive`), rule `30` among them
  (`leftPermutive_rule30`). So at every table with a persistent word or
  permutive at an end, at every scale, two states each erasing within two
  have the same successor
  (`lineRule_iterate_eq_of_erasesWithin_two_of_forcing`, its hypotheses met at
  the product table at scale two,
  `lineRule_iterate_eq_of_erasesWithin_two_of_forcing_nonvacuous`). Registered
  as *Rule Space* Proposition 6.1, row RS-10. Boundary: the permutive half is
  vacuous; a persistent word bounds only its first member; the class is
  enumerated from below in `PersistentWordCount.lean`, and at a table outside it
  nothing is stated past scale one.
- **The forcing class counted** (`PersistentWordCount.lean`): the three-valued step
  of a partial state (`stepWord`) keeps the cells at which one step of the
  table has one value at every completion of the unknown neighbours; it is
  sound (`stepsInto_stepWord`), monotone in the known set (`stepWord_mono`)
  and commutes with translation (`stepWord_translate`). A word on at most two
  cells whose iterates are non-empty up to a step that contains a translate
  of an earlier iterate gives a persistent word
  (`hasPersistentWord_of_return`, its hypotheses met at the majority table,
  `hasPersistentWord_of_return_nonvacuous`). The bounded form over six words,
  two steps and shifts of at most two cells is decidable (`ReturnsWithinTwo`)
  and sufficient (`hasPersistentWord_of_returnsWithinTwo`); over the 256
  radius-one tables it holds at 128, permutivity at an end at 28, both at 4
  and either at 152 (`card_returnsWithinTwo`, `card_permutiveEnd`,
  `card_returnsWithinTwo_and_permutiveEnd`, `card_forcingClass`), so the
  robustness statement holds over that counted class
  (`lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass`, its hypotheses
  met at the product table at scale two,
  `lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_nonvacuous`); the
  majority table returns within two (`returnsWithinTwo_majTable`) and rule
  `90` does not (`not_returnsWithinTwo_add_ends`). Registered as *Rule Space*
  Proposition 6.2, row RS-26. Boundary: the certificate is sufficient and
  not shown necessary; the step is sound, not complete; nothing is stated
  about the 104 tables outside the class here, twelve of which
  `EndRegionClosure.lean` decides.
- **Twelve tables outside the forcing class** (`EndRegionClosure.lean`,
  data in `EndRegionCert.lean`): a region map packs the five-cell region a
  flip of a window's last five cells can reach, one word per flip pattern,
  into a natural number (`word`, `mkMap`); the step under a context pair
  (`stepMap`), the apex (`apex`), goodness at every pattern within two flips
  (`goodMap`), relabeling of the patterns (`relabel`) and membership up to it
  (`inCert`) make a Boolean check on a table and a list (`certOK`), whose
  passing gives that no state of the line erases within two at any scale
  (`not_erasesWithin_two_of_certOK`, its hypotheses met at table `38`,
  `not_erasesWithin_two_of_certOK_nonvacuous`; the check refuses table `128`,
  `certOK_refuses_128`). The kernel decides the check at tables `38`, `46`,
  `66`, `139`, `155` and `189` (`certOK_38` to `certOK_189`), reflection
  carries erasure to the mirror table (`erasesWithin_iterate_mirrorTable`),
  and the twelve tables (`endClosureTables`) each have no erasing state
  (`not_erasesWithin_two_of_mem_endClosureTables`), so the robustness
  statement holds there vacuously and over the forcing class with them at
  164 tables (`card_forcingClass_or_endClosure`,
  `lineRule_iterate_eq_of_erasesWithin_two_of_forcingClass_or_endClosure`).
  Registered as *Rule Space* Proposition 6.3, row RS-29. Boundary: the lists
  are data the kernel checks; the twelve are listed, not characterized;
  nothing is stated at the 92 tables outside both.

### Replication and self-hosting

- **Rule 90's copies at tables that are not additive** (`ParityEmulation.lean`):
  a table that agrees with rule 90 on the five neighbourhoods with no two
  adjacent set cells (`AgreesOffAdjacent`; eight tables,
  `card_agreesOffAdjacent`, rule 18 among them) steps as rule 90 does on every
  finitely supported state whose set cells lie on one parity
  (`tableRule_eq_f90_of_oneParity`, `iterate_eq_f90_of_oneParity`), so a
  further power of two of steps gives two translated copies of the orbit
  (`iterate_two_pow_add_of_oneParity`), which do not overlap once the power
  exceeds the support's width (`two_pow_copies_disjoint`). At rule 18, from
  every state, setting cells that each sit between two set cells leaves the
  next state unchanged (`tableRule_f18_add_gapFill`); off one parity the
  agreement fails (`f18_ne_f90_off_parity`), the gap is needed
  (`gapFill_erasure_needs_gap`), and rule 90 erases no such hit
  (`f90_does_not_erase_gapFill`). Registered in no paper.
- **Rule 90 hosts itself** (`Decimation.lean`): reading one residue every
  `2 ^ M` cells (`decim`) takes `2 ^ M` steps of rule 90 to one step of rule 90
  on the decimated state, at every state (`decim_iterate_f90`), and the reading
  is onto (`decim_surjective`). On the light cone it closes the staged square
  of a reading (`advances_lightCone_iterate_f90`, `stagedSquare_decim_f90`),
  the reading's stages the light cone of a window `2 ^ M` times narrower
  (`guestStage_decim_f90`); two decimations compose into one (`decim_decim`),
  so the readings stack into a tower whose law never changes. Rule 30 admits no
  map on the even cells carrying its second iterate (`not_exists_decim_law_f30`).
  Registered as *Rule Space* Proposition 5.7, row RS-27.
- **Rule 90 at half speed on doubled states** (`Doubling.lean`): writing each
  cell twice (`dbl`), every quiescent table agreeing with rule 90 on the six
  neighbourhoods with two equal adjacent cells (`DoubledAgree`) takes the
  doubling of a state in two steps to the doubling of one step of rule 90
  (`tableRule_two_dbl`), and in `2 ^ (M + 1)` steps to that of `2 ^ M`
  (`tableRule_iterate_dbl`). Exactly four tables agree so
  (`card_doubledAgree`, `doubledAgree_cases`): 90, 94, 122 and 126. Rule 22
  does not, and two of its steps break a doubled state (`not_doubled_f22`).
  Registered as *Rule Space* Proposition 5.8, row RS-28.
- **The replication bracket** (`ReplicationBracket.lean`): a state is `k`
  copies of a pattern at gap `G` when it is the sum of `k` translates whose
  offsets step by at least the pattern's diameter plus `G` (`Copies`), and a
  map replicates the pattern when every count and every gap are reached at
  some iterate (`Replicates`; the exact-count reading `ReplicatesExactly` is
  refuted at rules 60 and 90, `not_replicates_single_f90_f60`). The bracket
  (`replication_bracket`, its three hypotheses all proved,
  `replication_bracket_nonvacuous`): bounded diameter forbids replication
  (`copies_diam_le`, `not_replicates_of_diamBounded`); every quiescent table
  outside the 54 accreting ones has bounded diameter from the landed
  per-table bounds (`classify_outside_accreting`,
  `diamBounded_of_not_accreting`); and fourteen tables replicate a pattern
  (`fourteen`, `replicates_of_mem_fourteen`) — the linear tables a single
  cell by a squaring identity (`LinearTaps`, `replicates_of_linear`), the
  seven agreeing with rule 90 off adjacent cells the two cells at distance
  two (`replicates_of_agreesOffAdjacent`), and the three doubled-agreement
  tables the adjacent pair (`replicates_of_doubledAgree`), each with a fixed
  instance. Registered as *Rule Space* Proposition 5.9, row RS-30. Boundary:
  neither end of the bracket is shown exact; three patterns only.

## Scope, and related formalizations

The carrier is the one every library of cellular automata on the line starts
from, a function from the integers to a finite alphabet, and the statements
here are about one thing those libraries do not treat: what the orbits of the
radius-one rules do — growth, settling along columns, windows and rays,
replication, erasure. Read at the sources on 2026-10-09:
[hediet/lean-cellular-automata](https://github.com/hediet/lean-cellular-automata)
defines a radius-one automaton over an alphabet with an input embedding and an
output projection, its step the same neighbourhood update as here, and studies
cellular automata as language recognizers and real-time transducers; no
statement there is about an orbit's growth or a column.
[jkingsbery/ca-surjectivity](https://github.com/jkingsbery/ca-surjectivity)
defines a local rule of any width and its global map on the line and proves
that the map commutes with the shift, towards the Garden-of-Eden theorem.
Mathlib's symbolic-dynamics file (`Mathlib.Dynamics.SymbolicDynamics.Basic`) defines shifts, cylinders,
patterns and subshifts, and no cellular-automaton map. Corrections are welcome
as issues.

## Papers

This library has one paper, *Rule Space* (`[RuleSpace]`, in preparation),
self-contained: it defines every object it uses, cites the classical results
it stands on at their sources, and registers the statements proved here at
the numbers the docstrings cite by key; a statement with no key is library
content the paper does not state. The paper and this library depend on
nothing else of ours. The library's first consumer is
[lean-algorithmic-learning-theory](https://github.com/lividgreen/lean-algorithmic-learning-theory),
which requires this package for the memory width of a growing world computed
at elementary cellular automata — hosts nobody built for the purpose, where
the census says at which of them a growing reading can exist at all.

## Citation and license

Apache-2.0 (see `LICENSE`). Cite the concept DOI of a tagged release; the
`CITATION.cff` carries the metadata.
