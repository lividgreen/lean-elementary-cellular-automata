module

public import ECA.ObservedRays
public import Mathlib.Data.Fintype.Pigeonhole

/-!
# The Markov error count: a law on the last `k` symbols, and its bound

`DrivenColumns.lean` proves a finite-valued sequence driven by an eventually periodic input
eventually periodic, and exhibits a column that is not. This file connects two currencies: a
sequence is eventually periodic exactly when SOME fixed law on its last `k` symbols answers
correctly from some point on, and exactly when the fewest errors any such law makes stays bounded as
the horizon grows. The fewest errors any such predictor makes before a horizon `T` is the error
count of the best Markov predictor of order `k` in hindsight; divided by `T` it is the `k`-th order
Markov predictability of Feder, Merhav and Gutman (1992), up to the convention for the first `k`
symbols.

A sequence is **eventually exact at order `k`** when some law on its last `k` symbols answers the
next symbol from some step on (`EventuallyExact`).

## Main results

* `EventuallyExact` — the order-`k` law condition. `eventuallyExact_of_eventuallyPeriodic` reads
  it off eventual periodicity directly, at the period as order;
  `eventuallyPeriodic_of_eventuallyExact` is the converse, over a finite alphabet, by casting the
  law's own driven register (`shiftAppendStep`) as an instance of
  `DrivenColumns.eventuallyPeriodic_of_driven`; `exists_eventuallyExact_iff_eventuallyPeriodic`
  folds the two directions into one equivalence, and
  `eventuallyExact_nat_id_not_eventuallyPeriodic` guards the finite-alphabet hypothesis: the
  naturals' own identity is exact at order `1` yet never eventually periodic.
* `predictorErrors`, `markovErrorCount` — how many errors a fixed law makes before a horizon, and
  the fewest errors any law on the given order makes. `markovErrorCount_bounded_iff_eventuallyExact`
  and `exists_markovErrorCount_bounded_iff_eventuallyPeriodic` are the two count-currency
  counterparts of the law-currency facts above, the second existentially over the order.
* `exists_eventuallyExact_observedWindow_iff` / `exists_markovErrorCount_bounded_observedWindow_iff`
  — both currencies of `eventuallyPeriodic_observedWindow_iff`'s window form, read at
  a local rule's observed window: the width-`(m + 1)` window meets the condition iff its two
  boundary columns each do, at their own (separate) orders.
* `eventuallyExact_observedColumn_f90_single`,
  `not_exists_eventuallyExact_observedColumn_f90_single_one`,
  `markovErrorCount_observedColumn_f90_single_one_unbounded` — the guard pair, both currencies, at
  the column `not_eventuallyPeriodic_observedColumn_f90_single_one` already treats: the
  center column is eventually exact at order `0`, and the cell beside it is eventually exact at NO
  order, with an unbounded Markov error count at every order.
* `LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn`,
  `LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedWindow` — the observer's bill
  against the system's growth read at the class level: at every rule of the zero class some order
  gives every cell's count, and every window's, a bound.
  `LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn_nonvacuous` meets both
  named hypotheses at once at rule `170`, and
  `exists_markovErrorCount_bounded_observedColumn_zero_class_guard` shows the class hypothesis
  load-bearing: rule `90` is in the other class and one cell's count there is unbounded at every
  order.

## Scope

The two window theorems are registered as `[RuleSpace] §4 Proposition 4.3`, clause (i), row RS-7;
nothing else here is registered against any paper: the class-level corollary is registered against
none, `[RuleSpace] §3 Proposition 3.1` being the class it ranges over and Proposition 4.3 the
count's registration, cited for that reason alone, and it claims nothing at the twenty-eight
rules in neither class; `[RuleSpace] §4 Proposition 4.2` is what the rest extends, cited for that
reason alone. The two window theorems are stated at a general local rule `LocalRule.finRule f hq`,
never specialized beyond the guard pair's own column.
-/


@[expose] public section

namespace ECA

open LocalRule

open DrivenColumns

/-! ## A law on the last `k` symbols, and eventual periodicity -/

/-- **A law on the last `k` symbols**: some function of the window `x t, …, x (t + k - 1)`
answers `x (t + k)`, from some point on. -/
def EventuallyExact {α : Type*} (k : ℕ) (x : ℕ → α) : Prop :=
  ∃ (L : (Fin k → α) → α) (N : ℕ), ∀ t, N ≤ t → L (fun i => x (t + (i : ℕ))) = x (t + k)

/-- **Eventual periodicity gives a law**: the law that answers the oldest symbol its own period
holds, at the period as order. -/
theorem eventuallyExact_of_eventuallyPeriodic {α : Type*} {x : ℕ → α}
    (hx : DrivenColumns.EventuallyPeriodic x) : ∃ k, EventuallyExact k x := by
  obtain ⟨P, N, hP, hper⟩ := hx
  exact ⟨P, fun w => w ⟨0, hP⟩, N, fun t ht => (hper t ht).symm⟩

/-- **The shift-and-append step**: read one cell further along the window when there is one, and
answer with the law otherwise. -/
private def shiftAppendStep {α : Type*} (k : ℕ) (L : (Fin k → α) → α) :
    (Fin k → α) → (Fin k → α) :=
  fun w j => if hj : (j : ℕ) + 1 < k then w ⟨(j : ℕ) + 1, hj⟩ else L w

/-- **A law gives eventual periodicity**, over a finite alphabet. At `k = 0` the law directly gives
`x` eventually constant. At `k > 0` the block of the last `k` symbols is itself driven — over a
one-point input, by `shiftAppendStep` — hence eventually periodic by `eventuallyPeriodic_of_driven`,
and `x` is its `0`-th coordinate. -/
theorem eventuallyPeriodic_of_eventuallyExact {α : Type*} [Finite α] {k : ℕ} {x : ℕ → α}
    (hx : EventuallyExact k x) : DrivenColumns.EventuallyPeriodic x := by
  classical
  obtain ⟨L, N, hL⟩ := hx
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    refine ⟨1, N, one_pos, fun t ht => ?_⟩
    have hw : (fun i : Fin 0 => x (t + (i : ℕ))) = fun i : Fin 0 => x (t + 1 + (i : ℕ)) :=
      Subsingleton.elim _ _
    have h0 := hL t ht
    have h1 := hL (t + 1) (Nat.le_succ_of_le ht)
    rw [Nat.add_zero] at h0
    rw [Nat.add_zero, ← hw] at h1
    rw [h1] at h0
    exact h0
  · have hstep : ∃ N', ∀ t, N' ≤ t →
        (fun i : Fin k => x (t + 1 + (i : ℕ))) =
          shiftAppendStep k L (fun i : Fin k => x (t + (i : ℕ))) := by
      refine ⟨N, fun t ht => ?_⟩
      funext j
      show x (t + 1 + (j : ℕ)) = shiftAppendStep k L (fun i : Fin k => x (t + (i : ℕ))) j
      unfold shiftAppendStep
      rcases lt_or_ge ((j : ℕ) + 1) k with hj | hj
      · rw [dite_eq_left hj]
        change x (t + 1 + (j : ℕ)) = x (t + ((j : ℕ) + 1))
        congr 1
        omega
      · rw [dite_eq_right (by omega)]
        have hLt := hL t ht
        rw [hLt]
        have hjlt := j.isLt
        congr 1
        omega
    have hu : DrivenColumns.EventuallyPeriodic (fun _ : ℕ => ()) :=
      ⟨1, 0, one_pos, fun _ _ => rfl⟩
    have hblock : DrivenColumns.EventuallyPeriodic
        (fun t : ℕ => (fun i : Fin k => x (t + (i : ℕ)))) := by
      obtain ⟨N', hN'⟩ := hstep
      exact eventuallyPeriodic_of_driven (fun (w : Fin k → α) (_ : Unit) => shiftAppendStep k L w)
        hu ⟨N', fun t ht => hN' t ht⟩
    have h0 : (0 : ℕ) < k := hkpos
    have heq : (fun w : Fin k → α => w ⟨0, h0⟩) ∘
        (fun t : ℕ => (fun i : Fin k => x (t + (i : ℕ)))) = x := by
      funext t
      change x (t + (0 : ℕ)) = x t
      rw [Nat.add_zero]
    have hcomp := eventuallyPeriodic_comp hblock (fun w : Fin k → α => w ⟨0, h0⟩)
    rwa [heq] at hcomp

/-- **The two directions above, as one equivalence.** -/
theorem exists_eventuallyExact_iff_eventuallyPeriodic {α : Type*} [Finite α] (x : ℕ → α) :
    (∃ k, EventuallyExact k x) ↔ DrivenColumns.EventuallyPeriodic x := by
  constructor
  · rintro ⟨k, hk⟩
    exact eventuallyPeriodic_of_eventuallyExact hk
  · intro hx
    exact eventuallyExact_of_eventuallyPeriodic hx

/-- **The finite alphabet is load-bearing** in `eventuallyPeriodic_of_eventuallyExact`: the law
that adds one to its one symbol is exact from the start, and the identity on the naturals repeats
nowhere. -/
theorem eventuallyExact_nat_id_not_eventuallyPeriodic :
    EventuallyExact 1 (fun t : ℕ => t) ∧
      ¬ DrivenColumns.EventuallyPeriodic (fun t : ℕ => t) := by
  refine ⟨⟨fun w => w 0 + 1, 0, fun t _ => by simp⟩, ?_⟩
  rintro ⟨P, N, hP, hper⟩
  have h : N + P = N := hper N le_rfl
  omega

/-! ## The Markov error count -/

/-- **How many errors a fixed law on the last `k` symbols makes**, before horizon `T`. -/
noncomputable def predictorErrors {α : Type*} [DecidableEq α] (k : ℕ) (L : (Fin k → α) → α)
    (x : ℕ → α) (T : ℕ) : ℕ :=
  ((Finset.range T).filter fun t => L (fun i => x (t + (i : ℕ))) ≠ x (t + k)).card

/-- **The Markov error count**: the fewest errors any law on the last `k` symbols makes before `T`.
-/
noncomputable def markovErrorCount {α : Type*} [DecidableEq α] (k : ℕ) (x : ℕ → α) (T : ℕ) : ℕ :=
  ⨅ L : (Fin k → α) → α, predictorErrors k L x T

private theorem predictorErrors_succ {α : Type*} [DecidableEq α] (k : ℕ) (L : (Fin k → α) → α)
    (x : ℕ → α) (T : ℕ) :
    predictorErrors k L x (T + 1) =
      predictorErrors k L x T + (if L (fun i => x (T + (i : ℕ))) ≠ x (T + k) then 1 else 0) := by
  rw [predictorErrors, predictorErrors, Finset.range_add_one, Finset.filter_insert]
  by_cases h : L (fun i => x (T + (i : ℕ))) ≠ x (T + k)
  · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
  · rw [ite_eq_right h, ite_eq_right h, Nat.add_zero]

private theorem predictorErrors_mono {α : Type*} [DecidableEq α] (k : ℕ) (L : (Fin k → α) → α)
    (x : ℕ → α) : Monotone (predictorErrors k L x) :=
  monotone_nat_of_le_succ (fun T => by rw [predictorErrors_succ]; omega)

/-- **A monotone `ℕ`-sequence bounded above is eventually constant.** Self-contained, by strong
induction on the bound: if the bound is hit, the sequence is pinned at it from there on; if not,
the tighter bound applies. -/
private theorem exists_eventually_eq_succ_of_monotone_bddAbove :
    ∀ (B : ℕ) (g : ℕ → ℕ), Monotone g → (∀ t, g t ≤ B) → ∃ N, ∀ t, N ≤ t → g (t + 1) = g t := by
  intro B
  induction B with
  | zero =>
      intro g _ hbdd
      refine ⟨0, fun t _ => ?_⟩
      have h1 := hbdd (t + 1)
      have h2 := hbdd t
      omega
  | succ B ih =>
      intro g hmono hbdd
      by_cases hcase : ∃ t0, g t0 = B + 1
      · obtain ⟨t0, ht0⟩ := hcase
        refine ⟨t0, fun t ht => ?_⟩
        have hle1 := hmono ht
        have hle2 := hbdd t
        have hle3 := hbdd (t + 1)
        have hle4 := hmono (show t ≤ t + 1 by omega)
        omega
      · push Not at hcase
        have hbdd' : ∀ t, g t ≤ B := fun t => by
          have h1 := hbdd t
          have h2 := hcase t
          omega
        exact ih g hmono hbdd'

/-- **A bounded Markov error count is a law**: the laws are finitely many, the infimum over a
nonempty finite family in `ℕ` is attained at each `T` (`ciInf_mem`), so one law attains the
infimum at infinitely many `T` (`Finite.exists_infinite_fiber`, the pigeonhole), hence — by
monotonicity — at every `T`; a monotone count bounded above stops rising, and from the last rise on
that law never errs. -/
theorem markovErrorCount_bounded_iff_eventuallyExact {α : Type*} [Finite α] [DecidableEq α]
    (k : ℕ) (x : ℕ → α) :
    (∃ B, ∀ T, markovErrorCount k x T ≤ B) ↔ EventuallyExact k x := by
  constructor
  · rintro ⟨B, hB⟩
    have : Nonempty α := ⟨x 0⟩
    have hattain : ∀ T, ∃ L, predictorErrors k L x T = markovErrorCount k x T :=
      fun T => ciInf_mem (fun L => predictorErrors k L x T)
    choose choiceL hchoiceL using hattain
    obtain ⟨L, hLfiberTC⟩ := Finite.exists_infinite_fiber choiceL
    have hLfiber : (choiceL ⁻¹' {L}).Infinite := Set.infinite_coe_iff.mp hLfiberTC
    have hbddT : ∀ T, predictorErrors k L x T ≤ B := by
      intro T
      obtain ⟨T', hT'mem, hT'gt⟩ := hLfiber.exists_notMem_finset (Finset.range (T + 1))
      have heq : choiceL T' = L := by simpa using hT'mem
      have hTT' : T ≤ T' := by
        simp only [Finset.mem_range, not_lt] at hT'gt
        omega
      calc predictorErrors k L x T ≤ predictorErrors k L x T' := predictorErrors_mono k L x hTT'
        _ = predictorErrors k (choiceL T') x T' := by rw [heq]
        _ = markovErrorCount k x T' := hchoiceL T'
        _ ≤ B := hB T'
    obtain ⟨N, hN⟩ :=
      exists_eventually_eq_succ_of_monotone_bddAbove B (predictorErrors k L x)
        (predictorErrors_mono k L x) hbddT
    refine ⟨L, N, fun t ht => ?_⟩
    have heq := hN t ht
    rw [predictorErrors_succ] at heq
    by_contra hne
    rw [ite_eq_left hne] at heq
    omega
  · rintro ⟨L, N, hL⟩
    refine ⟨N, fun T => ?_⟩
    have hle : markovErrorCount k x T ≤ predictorErrors k L x T := ciInf_le' _ L
    have hsub : (Finset.range T).filter (fun t => L (fun i => x (t + (i : ℕ))) ≠ x (t + k))
        ⊆ Finset.range N := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      rw [Finset.mem_range]
      by_contra hc
      push Not at hc
      exact ht.2 (hL t hc)
    have : predictorErrors k L x T ≤ N := by
      calc predictorErrors k L x T ≤ (Finset.range N).card := Finset.card_le_card hsub
        _ = N := Finset.card_range N
    omega

/-- **The existential count-currency form**: bounded Markov error count at SOME order, exactly when
eventually periodic. -/
theorem exists_markovErrorCount_bounded_iff_eventuallyPeriodic {α : Type*} [Finite α]
    [DecidableEq α] (x : ℕ → α) :
    (∃ k B, ∀ T, markovErrorCount k x T ≤ B) ↔ DrivenColumns.EventuallyPeriodic x := by
  constructor
  · rintro ⟨k, B, hB⟩
    exact eventuallyPeriodic_of_eventuallyExact
      ((markovErrorCount_bounded_iff_eventuallyExact k x).mp ⟨B, hB⟩)
  · intro hx
    obtain ⟨k, hk⟩ := eventuallyExact_of_eventuallyPeriodic hx
    obtain ⟨B, hB⟩ := (markovErrorCount_bounded_iff_eventuallyExact k x).mpr hk
    exact ⟨k, B, hB⟩

/-! ## The window of a local rule -/

/-- **The window's law-currency form**: the width-`(m + 1)` window is eventually exact at SOME
order iff its two boundary columns each are, at their own (separate) orders — three applications
of the pieces above around `eventuallyPeriodic_observedWindow_iff`. -/
theorem exists_eventuallyExact_observedWindow_iff
    (f : LocalRule) (hq : f 0 0 0 = 0) (s₀ : FiniteConfiguration)
    (a : ℤ) (m : ℕ) :
    (∃ k, EventuallyExact k (observedWindow (finRule f hq) s₀ a (m + 1))) ↔
      (∃ k, EventuallyExact k (observedColumn (finRule f hq) s₀ a)) ∧
      (∃ k, EventuallyExact k (observedColumn (finRule f hq) s₀ (a + (m : ℤ)))) := by
  constructor
  · rintro ⟨k, hk⟩
    have hep := eventuallyPeriodic_of_eventuallyExact hk
    rw [eventuallyPeriodic_observedWindow_iff] at hep
    exact ⟨eventuallyExact_of_eventuallyPeriodic hep.1, eventuallyExact_of_eventuallyPeriodic hep.2⟩
  · rintro ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
    have hep : DrivenColumns.EventuallyPeriodic
        (observedWindow (finRule f hq) s₀ a (m + 1)) := by
      rw [eventuallyPeriodic_observedWindow_iff]
      exact ⟨eventuallyPeriodic_of_eventuallyExact hk1, eventuallyPeriodic_of_eventuallyExact hk2⟩
    exact eventuallyExact_of_eventuallyPeriodic hep

/-- **The window's count-currency form**, the same fact read through `markovErrorCount`: both sides
reduce to `exists_markovErrorCount_bounded_iff_eventuallyPeriodic`, and what remains is exactly
`eventuallyPeriodic_observedWindow_iff`. -/
theorem exists_markovErrorCount_bounded_observedWindow_iff
    (f : LocalRule) (hq : f 0 0 0 = 0) (s₀ : FiniteConfiguration)
    (a : ℤ) (m : ℕ) :
    (∃ k B, ∀ T,
        markovErrorCount k (observedWindow (finRule f hq) s₀ a (m + 1)) T ≤ B) ↔
      (∃ k B, ∀ T, markovErrorCount k (observedColumn (finRule f hq) s₀ a) T ≤ B) ∧
      (∃ k B, ∀ T, markovErrorCount k (observedColumn (finRule f hq) s₀ (a + (m : ℤ))) T ≤ B) := by
  simp only [exists_markovErrorCount_bounded_iff_eventuallyPeriodic]
  exact eventuallyPeriodic_observedWindow_iff f hq s₀ a m

/-! ## The guards at rule `90` -/

/-- **The center column is eventually exact at order `0`**: it is eventually `0`, from step `1` on.
-/
theorem eventuallyExact_observedColumn_f90_single :
    EventuallyExact 0
      (observedColumn (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0) := by
  refine ⟨fun _ => 0, 1, fun t ht => ?_⟩
  change (0 : ZMod 2) = observedColumn (finRule f90 hq90)
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 (t + 0)
  rw [Nat.add_zero, observedColumn_f90_single]
  have ht0 : t ≠ 0 := by omega
  simp [ht0]

/-- **The cell beside it is eventually exact at NO order.** -/
theorem not_exists_eventuallyExact_observedColumn_f90_single_one :
    ¬ ∃ k, EventuallyExact k
      (observedColumn (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) := by
  rintro ⟨k, hk⟩
  exact not_eventuallyPeriodic_observedColumn_f90_single_one
    (eventuallyPeriodic_of_eventuallyExact hk)

/-- **Its Markov error count is unbounded, at every order.** -/
theorem markovErrorCount_observedColumn_f90_single_one_unbounded (k B : ℕ) :
    ∃ T, B < markovErrorCount k
      (observedColumn (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) T := by
  by_contra hcon
  push Not at hcon
  have hee : EventuallyExact k
      (observedColumn (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) :=
    (markovErrorCount_bounded_iff_eventuallyExact k _).mp ⟨B, hcon⟩
  exact not_exists_eventuallyExact_observedColumn_f90_single_one ⟨k, hee⟩

/-! ## The count at the two classes of rules -/

/-- **The observer's bill at the zero class**: at every rule of the zero class, every cell's
Markov error count is bounded at some order. It is
`exists_markovErrorCount_bounded_iff_eventuallyPeriodic` read through
`LocalRule.ZeroByEndpoints.eventuallyPeriodic_observedColumn`; the class is
`[RuleSpace] §3 Proposition 3.1`'s and the count's registration `[RuleSpace] §4 Proposition 4.3`,
cited for that reason alone. -/
theorem LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn
    (f : LocalRule) (hq : f 0 0 0 = 0) (hf : ZeroByEndpoints f)
    (s₀ : FiniteConfiguration) (i : ℤ) :
    ∃ k B, ∀ T, markovErrorCount k (observedColumn (finRule f hq) s₀ i) T ≤ B :=
  (exists_markovErrorCount_bounded_iff_eventuallyPeriodic _).mpr
    (LocalRule.ZeroByEndpoints.eventuallyPeriodic_observedColumn f hq hf s₀ i)

/-- **The same bill at every window** of the zero class: the width-`(m + 1)` window at cell `a`
has a bounded count at some order, by the window form through the column form at its two end
cells. -/
theorem LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedWindow
    (f : LocalRule) (hq : f 0 0 0 = 0) (hf : ZeroByEndpoints f)
    (s₀ : FiniteConfiguration) (a : ℤ) (m : ℕ) :
    ∃ k B, ∀ T,
      markovErrorCount k (observedWindow (finRule f hq) s₀ a (m + 1)) T ≤ B :=
  (exists_markovErrorCount_bounded_observedWindow_iff f hq s₀ a m).mpr
    ⟨LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn f hq hf s₀ a,
      LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn f hq hf s₀ (a + (m :
        ℤ))⟩

/-- **Both hypotheses of the corollary hold at once**, at rule `170` (the shift) from the single
seed `1` at cell `0`, and its conclusion is asserted there. -/
theorem LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn_nonvacuous :
    f170 0 0 0 = 0 ∧ ZeroByEndpoints f170 ∧
      ∃ k B, ∀ T, markovErrorCount k
        (observedColumn (finRule f170 hq170) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0) T ≤ B :=
  ⟨hq170, zeroByEndpoints_f170,
    LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn f170 hq170
      zeroByEndpoints_f170 _ _⟩

/-- **The class hypothesis is load-bearing**: rule `90` lies in the other class, and at it the
cell-one column's Markov error count exceeds every bound, at every order. -/
theorem exists_markovErrorCount_bounded_observedColumn_zero_class_guard :
    GrowsByEndpoints f90 ∧ ∀ k B, ∃ T, B < markovErrorCount k
      (observedColumn (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) T :=
  ⟨growsByEndpoints_f90, markovErrorCount_observedColumn_f90_single_one_unbounded⟩

end ECA

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

/-- info: 'ECA.eventuallyExact_of_eventuallyPeriodic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyExact_of_eventuallyPeriodic

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_of_eventuallyExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_of_eventuallyExact

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_bounded_iff_eventuallyExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_bounded_iff_eventuallyExact

set_option linter.style.longLine false in
/-- info: 'ECA.exists_markovErrorCount_bounded_iff_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_markovErrorCount_bounded_iff_eventuallyPeriodic

set_option linter.style.longLine false in
/-- info: 'ECA.exists_eventuallyExact_observedWindow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_eventuallyExact_observedWindow_iff

set_option linter.style.longLine false in
/-- info: 'ECA.exists_markovErrorCount_bounded_observedWindow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_markovErrorCount_bounded_observedWindow_iff

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyExact_observedColumn_f90_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyExact_observedColumn_f90_single

set_option linter.style.longLine false in
/-- info: 'ECA.not_exists_eventuallyExact_observedColumn_f90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_exists_eventuallyExact_observedColumn_f90_single_one

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_observedColumn_f90_single_one_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_observedColumn_f90_single_one_unbounded

set_option linter.style.longLine false in
/-- info: 'ECA.exists_eventuallyExact_iff_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_eventuallyExact_iff_eventuallyPeriodic

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyExact_nat_id_not_eventuallyPeriodic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyExact_nat_id_not_eventuallyPeriodic

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedWindow

set_option linter.style.longLine false in
/-- info: 'ECA.LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ECA.LocalRule.ZeroByEndpoints.exists_markovErrorCount_bounded_observedColumn_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.exists_markovErrorCount_bounded_observedColumn_zero_class_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_markovErrorCount_bounded_observedColumn_zero_class_guard
