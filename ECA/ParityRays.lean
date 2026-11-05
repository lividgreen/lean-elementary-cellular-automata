module

public import ECA.Doubling
public import ECA.ParityEmulation
public import ECA.RationalRayBound
public import ECA.RationalRayLines

/-!
# The single seed's rays over the one-parity class
([RuleSpace] §5)

The eight rules that agree with rule `90` off adjacent set cells (`LocalRule.AgreesOffAdjacent`)
step a one-parity state as `90` does, so a ray read from such a state is the ray of `90`. The single
set cell is of one parity, hence every statement about the rays of `90` from the single seed holds
over the class.

* `FiniteConfiguration.OneParity.observedRationalRay_eq_f90` — over the class, a one-parity state's
  rational rays are those of `90`; `FiniteConfiguration.oneParity_single` is the single cell.
* `LocalRule.AgreesOffAdjacent.not_eventuallyPeriodic_observedRationalRay_single` — a ray of speed
  strictly between `0` and `1` from the single seed is not eventually periodic.
* `LocalRule.AgreesOffAdjacent.single_apply_zeroLine` — the zero lines of the single seed's orbit.
* `LocalRule.AgreesOffAdjacent.card_ones_observedRationalRay_single_le_fib` — the Fibonacci bound
  on the ones of such a ray.
* `LocalRule.AgreesOffAdjacent.exists_late_one_single_onLine_iff` — the lines along which the
  orbit reads a one past every step.
* **Guard.** The class is load-bearing: rule `254` is outside it and its ray of speed `1 / 2` from
  the single cell is constant (`eventuallyPeriodic_observedRationalRay_wolfram254_single`).
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- The single set cell is a one-parity state. -/
theorem FiniteConfiguration.oneParity_single :
    FiniteConfiguration.OneParity (Finsupp.single (0 : ℤ) (1 : ZMod 2)) := by
  intro i j hi hj
  have hi0 : i = 0 := by
    by_contra h
    exact hi (by simp [Ne.symm h])
  have hj0 : j = 0 := by
    by_contra h
    exact hj (by simp [Ne.symm h])
  subst hi0 hj0
  simp

/-- **Over the class a one-parity state's rational rays are rule `90`'s.** -/
theorem FiniteConfiguration.OneParity.observedRationalRay_eq_f90 (f : LocalRule)
    (h : f.AgreesOffAdjacent) (s : FiniteConfiguration) (hs : s.OneParity) (p q : ℕ) (e : ℤ) :
    observedRationalRay (finRule f h.1) s p q e
      = observedRationalRay (finRule f90 hq90) s p q e := by
  funext t
  unfold observedRationalRay
  rw [FiniteConfiguration.OneParity.iterate_eq_f90 f h s hs]

/-- **Rule `90`'s ray statement over the class**: a ray of speed `p / q` with `0 < p < q` from the
single seed is not eventually periodic, from every cell. -/
theorem LocalRule.AgreesOffAdjacent.not_eventuallyPeriodic_observedRationalRay_single
    {f : LocalRule} (h : f.AgreesOffAdjacent) (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedRationalRay (finRule f h.1) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e) := by
  rw [FiniteConfiguration.OneParity.observedRationalRay_eq_f90 f h _
    FiniteConfiguration.oneParity_single p q e]
  exact not_eventuallyPeriodic_observedRationalRay_f90_single p q hp hpq e

/-- **The zero lines of the single seed's orbit over the class**: the orbit reads `0` along the
cells `⌊(s - 1) / (2 ^ m - 1)⌋` at step `s ≥ 1`, for every `m ≥ 2`. -/
theorem LocalRule.AgreesOffAdjacent.single_apply_zeroLine {f : LocalRule}
    (h : f.AgreesOffAdjacent) (m s : ℕ) (hm : 2 ≤ m) (hs : 1 ≤ s) :
    ((finRule f h.1)^[s] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
      (((s - 1) / (2 ^ m - 1) : ℕ) : ℤ) = 0 := by
  rw [FiniteConfiguration.OneParity.iterate_eq_f90 f h _ FiniteConfiguration.oneParity_single]
  exact f90_single_apply_zeroLine m s hm hs

/-- **The Fibonacci bound over the class**: a ray of speed `p / q` with `0 < p < q` from the single
seed reads at most `q * Nat.fib (K + 1)` ones below step `2 ^ K`. -/
theorem LocalRule.AgreesOffAdjacent.card_ones_observedRationalRay_single_le_fib
    {f : LocalRule} (h : f.AgreesOffAdjacent) (p q : ℕ) (hp : 0 < p) (hpq : p < q) (e : ℤ)
    (K : ℕ) :
    ((Finset.range (2 ^ K)).filter fun t =>
      observedRationalRay (finRule f h.1) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) p q e t
        = 1).card ≤ q * Nat.fib (K + 1) := by
  rw [FiniteConfiguration.OneParity.observedRationalRay_eq_f90 f h _
    FiniteConfiguration.oneParity_single p q e]
  exact card_ones_observedRationalRay_f90_single_le_fib p q hp hpq e K

/-- **The lines of the single seed's orbit over the class**: for coprime `0 < p < q`, the orbit
reads a `1` past every step along the line of slope `p / q` and offset `c` exactly when the line
is not a zero line. -/
theorem LocalRule.AgreesOffAdjacent.exists_late_one_single_onLine_iff {f : LocalRule}
    (h : f.AgreesOffAdjacent) (p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (c : ℤ) :
    (∀ T : ℕ, ∃ s : ℕ, T ≤ s ∧
      ((finRule f h.1)^[s] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (((p : ℤ) * s + c) / q) = 1) ↔ ¬ ZeroLine p q c := by
  have key : ∀ s : ℕ, (finRule f h.1)^[s] (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      = (finRule f90 hq90)^[s] (Finsupp.single (0 : ℤ) (1 : ZMod 2)) := fun s =>
    FiniteConfiguration.OneParity.iterate_eq_f90 f h _ FiniteConfiguration.oneParity_single s
  refine Iff.trans ?_ (exists_late_one_f90_single_onLine_iff p q hp hpq hcop c)
  refine forall_congr' fun T => exists_congr fun s => and_congr_right fun _ => ?_
  rw [key s]

/-- **Joint satisfiability** at rule `18`: it meets the agreement, `0 < 1`, `1 < 2`, `1` and `2` are
coprime, and the ray at speed `1 / 2` from cell zero is not eventually periodic. -/
theorem LocalRule.AgreesOffAdjacent.not_eventuallyPeriodic_observedRationalRay_single_nonvacuous :
    f18.AgreesOffAdjacent ∧ 0 < 1 ∧ 1 < 2 ∧ Nat.Coprime 1 2 ∧
      ¬ DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule f18 hq18) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1 2 0) :=
  ⟨agreesOffAdjacent_f18, by decide, by decide, by decide,
    LocalRule.AgreesOffAdjacent.not_eventuallyPeriodic_observedRationalRay_single
      agreesOffAdjacent_f18 1 2 (by decide) (by decide) 0⟩

/-- Rule `254` sets a cell whenever one of its three neighbourhood cells is set. -/
private theorem wolframRule_254_of (a b c : ZMod 2) (h : a = 1 ∨ b = 1 ∨ c = 1) :
    wolframRule 254 a b c = 1 := by
  revert a b c; decide

/-- From the single cell, rule `254` sets every cell of `[-t, t]` at step `t`. -/
private theorem wolfram254_single_iterate_apply (hq : wolframRule 254 0 0 0 = 0) (t : ℕ) :
    ∀ i : ℤ, |i| ≤ t →
      ((finRule (wolframRule 254) hq)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i = 1 := by
  induction t with
  | zero =>
    intro i hi
    have : i = 0 := by simpa using hi
    subst this
    simp
  | succ n ih =>
    intro i hi
    rw [Function.iterate_succ_apply', finRule_apply]
    apply wolframRule_254_of
    rw [abs_le] at hi
    by_cases h1 : |i - 1| ≤ n
    · exact Or.inl (ih _ h1)
    by_cases h2 : |i| ≤ n
    · exact Or.inr (Or.inl (ih _ h2))
    · refine Or.inr (Or.inr (ih _ ?_))
      rw [abs_le]
      rw [abs_le] at h1 h2
      push Not at h1 h2
      constructor <;> omega

/-- **The class is load-bearing**: rule `254` is outside it, and from the single cell its ray of
speed `1 / 2` from cell `0` reads `1` at every step, so is eventually periodic. -/
theorem eventuallyPeriodic_observedRationalRay_wolfram254_single
    (hq : wolframRule 254 0 0 0 = 0) :
    ¬ (wolframRule 254).AgreesOffAdjacent ∧
      DrivenColumns.EventuallyPeriodic
        (observedRationalRay (finRule (wolframRule 254) hq) (Finsupp.single (0 : ℤ) (1 : ZMod 2))
          1 2 0) := by
  refine ⟨?_, 1, 0, by decide, fun u _ => ?_⟩
  · intro h
    have := h.2.2.2.1
    revert this
    decide
  · unfold observedRationalRay
    rw [wolfram254_single_iterate_apply hq, wolfram254_single_iterate_apply hq]
    · rw [abs_le]; push_cast; constructor <;> omega
    · rw [abs_le]; push_cast; constructor <;> omega

end ECA

/-- info: 'ECA.FiniteConfiguration.oneParity_single' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.oneParity_single

/-- info: 'ECA.FiniteConfiguration.OneParity.observedRationalRay_eq_f90' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.OneParity.observedRationalRay_eq_f90

/-- info: 'ECA.LocalRule.AgreesOffAdjacent.not_eventuallyPeriodic_observedRationalRay_single'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.not_eventuallyPeriodic_observedRationalRay_single

/-- info: 'ECA.LocalRule.AgreesOffAdjacent.single_apply_zeroLine' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.single_apply_zeroLine

/-- info: 'ECA.LocalRule.AgreesOffAdjacent.card_ones_observedRationalRay_single_le_fib' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.card_ones_observedRationalRay_single_le_fib

/-- info: 'ECA.LocalRule.AgreesOffAdjacent.exists_late_one_single_onLine_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.exists_late_one_single_onLine_iff

/-- info:
'ECA.LocalRule.AgreesOffAdjacent.not_eventuallyPeriodic_observedRationalRay_single_nonvacuous'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ECA.LocalRule.AgreesOffAdjacent.not_eventuallyPeriodic_observedRationalRay_single_nonvacuous

/-- info: 'ECA.eventuallyPeriodic_observedRationalRay_wolfram254_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedRationalRay_wolfram254_single
