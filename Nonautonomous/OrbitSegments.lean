module

public import Nonautonomous.MergeQuotient
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Orbit segments: the union of the first `t + 1` forward images of a start set
([RuleSpace] §2)

The fibers of a nonautonomous set may be derived from a finite start set `S` and an update `U` in
two ways: as the forward images `U^[t] '' S`, the states reached at time exactly `t`, or
cumulatively, as the states reached within `t` steps. This file is the cumulative case: the fiber
at `t` is the union of the orbit segments of length `t + 1` from the points of `S`, which is
positively invariant for any update. Its size is at most `|S| * (t + 1)` at every time, and it is
bounded in `t` exactly when every orbit from `S` is finite.

## Main results

* `orbitSegments` — the cumulative nonautonomous set, `{y | ∃ x ∈ S, ∃ k ≤ t, U^[k] x = y}`.
* `positivelyInvariant_orbitSegments` — it is positively invariant under `U`, with no hypothesis.
* `encard_orbitSegments_le` — the fiber at `t` has at most `S.encard * (t + 1)` states.
* `bounded_encard_orbitSegments_iff` — at a finite start set the fibers' sizes are bounded
  exactly when every orbit from `S` is finite.
-/

@[expose] public section

namespace Nonautonomous

variable {X : Type*}

/-- The union of the orbit segments of length `t + 1` from the points of `S`. -/
def orbitSegments (U : X → X) (S : Set X) (t : ℕ) : Set X :=
  {y | ∃ x ∈ S, ∃ k ≤ t, U^[k] x = y}

/-- **The orbit segments are positively invariant**, for every update and every start set: a state
reached at step `k ≤ t` is carried by `U` to the state reached at step `k + 1 ≤ t + 1`. -/
theorem positivelyInvariant_orbitSegments (U : X → X) (S : Set X) :
    PositivelyInvariant U (orbitSegments U S) := by
  rintro t s ⟨x, hx, k, hk, rfl⟩
  exact ⟨x, hx, k + 1, Nat.succ_le_succ hk, Function.iterate_succ_apply' U k x⟩

/-- **The fiber at `t` has at most `S.encard * (t + 1)` states**: it is the image of
`S ×ˢ {k | k ≤ t}` under `(x, k) ↦ U^[k] x`. -/
theorem encard_orbitSegments_le (U : X → X) (S : Set X) (t : ℕ) :
    (orbitSegments U S t).encard ≤ S.encard * (t + 1) := by
  have himg : orbitSegments U S t = (fun p : X × ℕ => U^[p.2] p.1) '' (S ×ˢ Set.Iic t) := by
    ext y
    simp only [orbitSegments, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Iic,
      Prod.exists]
    constructor
    · rintro ⟨x, hx, k, hk, rfl⟩
      exact ⟨x, k, ⟨hx, hk⟩, rfl⟩
    · rintro ⟨x, k, ⟨hx, hk⟩, rfl⟩
      exact ⟨x, hx, k, hk, rfl⟩
  have hIic : (Set.Iic t).encard = (t + 1 : ℕ) := by
    rw [Set.Finite.encard_eq_coe_toFinset_card (Set.finite_Iic t)]
    simp
  rw [himg]
  refine (Set.encard_image_le _ _).trans ?_
  rw [Set.encard_prod, hIic]
  norm_cast

/-- Each fiber of the orbit segments at a finite start set is contained in the union of the orbits
of the start points. -/
private theorem orbitSegments_subset_iUnion_range (U : X → X) (S : Set X) (t : ℕ) :
    orbitSegments U S t ⊆ ⋃ x ∈ S, Set.range fun k => U^[k] x := by
  rintro y ⟨x, hx, k, -, rfl⟩
  exact Set.mem_biUnion hx ⟨k, rfl⟩

/-- A single infinite orbit makes the fibers' sizes unbounded: a finite set of `B + 1` states of the
orbit is reached within some number of steps. -/
private theorem not_bounded_of_infinite_range {U : X → X} {S : Set X} {x : X} (hx : x ∈ S)
    (hinf : (Set.range fun k => U^[k] x).Infinite) (B : ℕ) :
    ¬ ∀ t, (orbitSegments U S t).encard ≤ B := by
  intro hB
  have hle : ((B + 1 : ℕ) : ℕ∞) ≤ (Set.range fun k => U^[k] x).encard := by
    rw [hinf.encard_eq]
    exact le_top
  obtain ⟨T, hTsub, hTenc⟩ := Set.exists_subset_encard_eq hle
  have hTfin : T.Finite := by
    rw [← Set.encard_lt_top_iff, hTenc]
    exact ENat.natCast_lt_top _
  choose! kf hkf using fun y (hy : y ∈ T) => hTsub hy
  obtain ⟨t, ht⟩ := (Set.Finite.image kf hTfin).bddAbove
  have hTsub' : T ⊆ orbitSegments U S t := by
    intro y hy
    exact ⟨x, hx, kf y, ht ⟨y, hy, rfl⟩, hkf y hy⟩
  have h1 := (Set.encard_le_encard hTsub').trans (hB t)
  rw [hTenc] at h1
  have h2 : B + 1 ≤ B := by exact_mod_cast h1
  omega

/-- **The sizes of the fibers are bounded exactly when every orbit from the start set is finite**,
at a finite start set: a bound `B` caps the number of distinct states along each orbit, and
conversely the fibers all lie in the finite union of the orbits. -/
theorem bounded_encard_orbitSegments_iff {U : X → X} {S : Set X} (hS : S.Finite) :
    (∃ B : ℕ, ∀ t, (orbitSegments U S t).encard ≤ B) ↔
      ∀ x ∈ S, (Set.range fun k => U^[k] x).Finite := by
  constructor
  · rintro ⟨B, hB⟩ x hx
    by_contra hinf
    exact not_bounded_of_infinite_range hx hinf B hB
  · intro h
    have hfin : (⋃ x ∈ S, Set.range fun k => U^[k] x).Finite :=
      Set.Finite.biUnion hS fun x hx => h x hx
    refine ⟨hfin.toFinset.card, fun t => ?_⟩
    refine (Set.encard_le_encard (orbitSegments_subset_iUnion_range U S t)).trans ?_
    rw [hfin.encard_eq_coe_toFinset_card]

end Nonautonomous

/-! ## Axiom audit

The capstone above is `#print axioms`-clean on the standard triple, and the guard below makes that
build-enforced. -/

set_option linter.style.longLine false in
/-- info: 'Nonautonomous.bounded_encard_orbitSegments_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.bounded_encard_orbitSegments_iff
