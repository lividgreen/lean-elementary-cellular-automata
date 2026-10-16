module

public import Nonautonomous.ReachabilityWidth

/-!
# The growing width: the width at a system's growing part
([RuleSpace] §2 Definition 2.3 and Proposition 2.12)

Unbounded growth is a property of a TRAJECTORY, and the width is a property of the
PRESENTED SYSTEM `(X, U, Ω)`. This file builds the object in which both are visible, and it is a
restriction rather than a new invention: the width taken at the states whose `U`-orbit has
unbounded `size`, rather than at every admitted state.

## Main results

* `GrowingPart` — the growing part at an arbitrary `size : X → ℕ`: the states whose orbit under `U`
  has unbounded `size`.
* `mem_growingPart_iff_apply` / `mem_growingPart_iff_iterate` — the part is invariant under `U` and
  under any of its iterates, the second by induction on the first.
* `growingPart_of_merge` — the part is MERGE-SATURATED: two states some common iterate identifies
  are on the same side of it, which is what licenses reading the restriction on the merge quotient.
* `positivelyInvariant_growingPart` — the growing-part restriction of a positively invariant
  nonautonomous set is itself positively invariant, so `Nonautonomous.width` is defined on it
  exactly as on the unrestricted fibers.
* `growingWidth` — the width read at the growing part: `Nonautonomous.width` applied to the
  nonautonomous set intersected with `GrowingPart`, so every fact `ReachabilityWidth.lean` proves
  about `width`'s SHAPE is inherited rather than reproved.
* `growingWidth_mono` — monotone, with no hypothesis beyond `PositivelyInvariant`:
  `Nonautonomous.width_mono` applied to `positivelyInvariant_growingPart`, nothing further.
* `growingWidth_le_width` — never exceeds the unrestricted width, via
  `Nonautonomous.width_mono_of_subset` applied to the restriction's own inclusion.
* The guard family, both at `Ω t = {n | n ≤ t}` on `ℕ`:
  `growingWidth_id_slow_clock_eq_zero_width_eq_succ` — **the separating system**, pinning that
  `growingWidth` is a genuine restriction of `width` and not the same quantity under a different
  name — and `growingWidth_nat_succ_eq_one` — **the non-vacuity twin**, pinning that the restriction
  is not vacuously zero.

## Scope

**Registered as [RuleSpace] §2 Definition 2.3 and Proposition 2.12** (FV rows RS-34 and RS-42):
the growing part, the growing width, its monotonicity and its bound by the plain width, and the two
systems at which the restriction is genuine.

`growingWidth` inherits `width`'s own dependence on the presented nonautonomous set, not only on
`(X, U)`: `width` is a property of `(X, U, Ω)` (see [RuleSpace] §2 Proposition 2.7), and
restricting further by `GrowingPart U size` adds a second axis of dependence, on `size`, without
removing the first. The guard family's own witnesses instantiate both: the identity update kills the
part outright regardless of `Ω` (`growingPart_id_eq_empty`), while the successor update's part is
everything regardless of `Ω` (`growingPart_nat_succ_eq_univ`) — in neither instance does the
restriction interact with which nonautonomous set is chosen, but nothing here claims that holds in
general.

`size` is left an arbitrary `X → ℕ`, on purpose: this file
owes no encoding — a consumer supplying one specializes `size` at the call site.

`GrowingPart`'s defining condition ranges over an entire orbit (`∀ N, ∃ k, …`), so it is not
decidable, and every proof below is classical; no `Decidable` instance is attempted or needed.
-/


@[expose] public section

namespace Nonautonomous


variable {X : Type*}

/-! ## The growing part -/

/-- **The growing part** ([RuleSpace] §2 Definition 2.3): the states whose
orbit under `U` has `size` unbounded along it. -/
def GrowingPart (U : X → X) (size : X → ℕ) : Set X :=
  {x | ∀ N, ∃ k, N < size (U^[k] x)}

/-- **The part is `U`-invariant**: a state is in the part exactly when its `U`-image is. Forward:
given `N`, unboundedness at `max N (size x)` supplies a `k` that cannot be `0` (that would force
`max N (size x) < size x`, false since `size x ≤ max N (size x)`), so `k = j + 1` and `U^[j] (U x)`
is the witness for `N`. Backward: `U^[k] (U x) = U^[k + 1] x` supplies the witness directly, one
step later. -/
theorem mem_growingPart_iff_apply (U : X → X) (size : X → ℕ) (x : X) :
    x ∈ GrowingPart U size ↔ U x ∈ GrowingPart U size := by
  constructor
  · intro hx N
    obtain ⟨k, hk⟩ := hx (max N (size x))
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp only [Function.iterate_zero_apply] at hk
      exact absurd hk (not_lt.mpr (le_max_right N (size x)))
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    refine ⟨j, ?_⟩
    rw [Function.iterate_succ_apply] at hk
    exact lt_of_le_of_lt (le_max_left N (size x)) hk
  · intro hUx N
    obtain ⟨k, hk⟩ := hUx N
    exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- **The part is invariant under every iterate of `U`**, by induction over
`mem_growingPart_iff_apply`. -/
theorem mem_growingPart_iff_iterate (U : X → X) (size : X → ℕ) (x : X) (k : ℕ) :
    x ∈ GrowingPart U size ↔ U^[k] x ∈ GrowingPart U size := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← mem_growingPart_iff_apply]
    exact ih

/-- **The part is merge-saturated**: two states some common iterate of `U` identifies are on the
same side of it — the fact that licenses reading the restriction on the merge quotient rather than
only on individual states. -/
theorem growingPart_of_merge {U : X → X} {size : X → ℕ} {x y : X} {k : ℕ}
    (h : U^[k] x = U^[k] y) : x ∈ GrowingPart U size ↔ y ∈ GrowingPart U size := by
  rw [mem_growingPart_iff_iterate U size x k, h, ← mem_growingPart_iff_iterate U size y k]

/-- **The growing-part restriction of a positively invariant nonautonomous set is itself positively
invariant**: immediate from `PositivelyInvariant`'s own unfolding and `mem_growingPart_iff_apply`.
-/
theorem positivelyInvariant_growingPart {U : X → X} {Ω : ℕ → Set X} {size : X → ℕ}
    (hadv : PositivelyInvariant U Ω) :
    PositivelyInvariant U (fun t => Ω t ∩ GrowingPart U size) := by
  rintro t s ⟨hsΩ, hsG⟩
  exact ⟨hadv t s hsΩ, (mem_growingPart_iff_apply U size s).mp hsG⟩

/-! ## The growing width -/

/-- **The growing width** ([RuleSpace] §2 Definition 2.3, the width read at the growing
part): `Nonautonomous.width` applied to the nonautonomous set restricted to the
states whose orbit has unbounded `size`. -/
noncomputable def growingWidth (U : X → X) (size : X → ℕ) (Ω : ℕ → Set X) (t : ℕ) : ℕ∞ :=
  Nonautonomous.width U (fun t => Ω t ∩ GrowingPart U size) t

/-- **Monotone, with no hypothesis beyond `PositivelyInvariant`**: `Nonautonomous.width_mono`
applied to `positivelyInvariant_growingPart`, nothing further — the point of defining `growingWidth`
as a restricted `width` rather than as a fresh supremum. -/
theorem growingWidth_mono {U : X → X} {size : X → ℕ} {Ω : ℕ → Set X}
    (hadv : PositivelyInvariant U Ω) : Monotone (growingWidth U size Ω) :=
  Nonautonomous.width_mono (positivelyInvariant_growingPart hadv)

/-- **Never exceeds the unrestricted width**: `Nonautonomous.width_mono_of_subset` applied to
the restriction's own inclusion, `Ω t ∩ GrowingPart U size ⊆ Ω t`. -/
theorem growingWidth_le_width {U : X → X} {size : X → ℕ} {Ω : ℕ → Set X} {t : ℕ} :
    growingWidth U size Ω t ≤ Nonautonomous.width U Ω t :=
  Nonautonomous.width_mono_of_subset Set.inter_subset_left

/-! ## The guard family, at `Ω t = {n | n ≤ t}` on `ℕ` -/

/-- **The growing part is EMPTY at the identity update**, whatever `size`: the orbit of any point is
constant, so no `size` is unbounded along it — `N := size x` refutes unboundedness outright. The
first half of guard (a): the separating witness. -/
theorem growingPart_id_eq_empty (size : X → ℕ) : GrowingPart (id : X → X) size = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨k, hk⟩ := hx (size x)
  simp only [Function.iterate_id, id_eq] at hk
  exact absurd hk (lt_irrefl _)

/-- **The growing part is EVERYTHING at the successor update read by `id`**: `Nat.succ^[k] x = x +
k` is unbounded in `k` for every `x`, so every point already qualifies. The first half of guard (b):
the non-vacuity twin. -/
theorem growingPart_nat_succ_eq_univ : GrowingPart Nat.succ (id : ℕ → ℕ) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x N
  refine ⟨N + 1, ?_⟩
  simp only [id_eq, Nat.succ_iterate]
  omega

/-- `mergeLaw (id : X → X)` fixes every class hit by `mergeMk`: `mergeLaw_mergeMk` at `U = id`
reduces the target back to the source, and `id`'s iterates change nothing further. What makes
`Reaches (id : X → X)` trivial (`isAntichain_reaches_id`). -/
private theorem mergeLaw_id_iterate_mergeMk (j : ℕ) (s : X) :
    (mergeLaw (id : X → X))^[j] (mergeMk (id : X → X) s) = mergeMk (id : X → X) s := by
  induction j with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, mergeLaw_mergeMk]; rfl

/-- **`Reaches` is trivial at the identity update**: the classes of the merge quotient represented
in the fibers of `id`, for ANY nonautonomous set, form an antichain — `id`'s induced law fixes every
class outright, so no class ever reaches a distinct one. -/
private theorem isAntichain_reaches_id (Ω : ℕ → Set X) (t : ℕ) :
    IsAntichain (Nonautonomous.Reaches (id : X → X)) (mergeFiber (id : X → X) Ω t) := by
  rintro _ ⟨s, -, rfl⟩ _ ⟨s', -, rfl⟩ hne ⟨j, hj⟩
  rw [mergeLaw_id_iterate_mergeMk] at hj
  exact hne hj

/-- The classes represented in a fiber of the identity update are as many as the states of the
fiber, `mergeMk id` never merging distinct states. -/
private theorem mergeFiber_id_encard (Ω : ℕ → Set X) (t : ℕ) :
    (mergeFiber (id : X → X) Ω t).encard = (Ω t).encard :=
  Function.Injective.encard_image (mergeMk_injective_of_injective Function.injective_id) (Ω t)

/-- The identity update's represented classes, at the initial-segment nonautonomous set, number
exactly `t + 1` — `Set.Iic t` counted, transported through `mergeFiber_id_encard`. -/
private theorem mergeFiber_id_slow_clock_encard (t : ℕ) :
    (mergeFiber (id : ℕ → ℕ) (fun t => Set.Iic t) t).encard = t + 1 := by
  rw [mergeFiber_id_encard]
  simp [Set.Finite.encard_eq_coe_toFinset_card (Set.finite_Iic t), Nat.card_Iic]

/-- **Guard (a), the separating witness**: at the identity update on `ℕ` (any `size`, since the part
is empty regardless), the growing width is `0` at every time of the initial-segment family, while
the unrestricted width there grows without bound — `mergeMk id` never merges, so the classes
represented in the fiber form trivially an antichain (`isAntichain_reaches_id`) of the fiber's own
count (`mergeFiber_id_slow_clock_encard`), `t + 1`. So `growingWidth` is a genuine restriction of
`width`, not the same quantity under a different name. -/
theorem growingWidth_id_slow_clock_eq_zero_width_eq_succ (size : ℕ → ℕ) (t : ℕ) :
    growingWidth (id : ℕ → ℕ) size (fun t => Set.Iic t) t = 0 ∧
      Nonautonomous.width (id : ℕ → ℕ) (fun t => Set.Iic t) t = t + 1 := by
  refine ⟨?_, ?_⟩
  · change Nonautonomous.width (id : ℕ → ℕ)
        (fun t' => Set.Iic t' ∩ GrowingPart (id : ℕ → ℕ) size) t = 0
    rw [Nonautonomous.width_eq_encard_of_isAntichain
        (isAntichain_reaches_id (fun t' => Set.Iic t' ∩ GrowingPart (id : ℕ → ℕ) size) t)]
    change (mergeMk (id : ℕ → ℕ) '' (Set.Iic t ∩ GrowingPart (id : ℕ → ℕ) size)).encard = 0
    rw [growingPart_id_eq_empty, Set.inter_empty, Set.image_empty, Set.encard_empty]
  · rw [Nonautonomous.width_eq_encard_of_isAntichain
        (isAntichain_reaches_id (fun t => Set.Iic t) t), mergeFiber_id_slow_clock_encard]

/-- `width` depends on the nonautonomous set only through the single value `mergeFiber U Ω t`, so
equal represented classes at `t` give equal widths there — the transport
`growingWidth_nat_succ_eq_one` needs to fold its restricted family back into the plain one. -/
private theorem width_eq_of_mergeFiber_eq {U : X → X} {Ω Ω' : ℕ → Set X} {t : ℕ}
    (h : mergeFiber U Ω t = mergeFiber U Ω' t) :
    Nonautonomous.width U Ω t = Nonautonomous.width U Ω' t := by
  unfold Nonautonomous.width
  rw [h]

/-- Intersecting with the successor update's growing part (`Set.univ`, by
`growingPart_nat_succ_eq_univ`) changes nothing. -/
private theorem inter_growingPart_nat_succ (Ω : ℕ → Set ℕ) (t : ℕ) :
    Ω t ∩ GrowingPart Nat.succ (id : ℕ → ℕ) = Ω t := by
  rw [growingPart_nat_succ_eq_univ, Set.inter_univ]

/-- **Guard (b), the non-vacuity twin**: at the successor update read by `id`, the growing part is
everything (`growingPart_nat_succ_eq_univ`), so the restriction removes nothing and the growing
width agrees with `Nonautonomous.width_nat_succ_eq_one`'s clock value, `1`, at any admitted
nonautonomous set. So the restriction is not vacuously zero. -/
theorem growingWidth_nat_succ_eq_one {Ω : ℕ → Set ℕ} {t : ℕ} (hne : (Ω t).Nonempty) :
    growingWidth Nat.succ (id : ℕ → ℕ) Ω t = 1 := by
  have hstage : mergeFiber Nat.succ (fun t' => Ω t' ∩ GrowingPart Nat.succ (id : ℕ → ℕ)) t
      = mergeFiber Nat.succ Ω t := by
    change mergeMk Nat.succ '' (Ω t ∩ GrowingPart Nat.succ (id : ℕ → ℕ)) = mergeMk Nat.succ '' Ω t
    rw [inter_growingPart_nat_succ]
  change Nonautonomous.width Nat.succ (fun t' => Ω t' ∩ GrowingPart Nat.succ (id : ℕ → ℕ)) t = 1
  rw [width_eq_of_mergeFiber_eq hstage]
  exact Nonautonomous.width_nat_succ_eq_one hne

end Nonautonomous

/-! ## Axiom audit

Both guard theorems are `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/


set_option linter.style.longLine false in
/-- info: 'Nonautonomous.growingWidth_id_slow_clock_eq_zero_width_eq_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.growingWidth_id_slow_clock_eq_zero_width_eq_succ

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.growingWidth_nat_succ_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.growingWidth_nat_succ_eq_one
