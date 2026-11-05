module

public import ECA.EmulationTower
public import ECA.PermutiveWidth

/-!
# The first level of rule 90's tower sees exactly its residue
([RuleSpace] §5 Proposition 5.10)

A hit at cell `c` on a finitely supported state `s` is `s + Finsupp.single c 1`. The level reading
at level step `k` is `decim M r` of the `k * 2 ^ M`-th iterate. At rule `90` the reading of a hit
differs from the reading of the state exactly when the hit lies on the sampled residue
(`decim_iterate_f90_add_single_eq_iff`), whatever the state and the level step; the same holds on
the one-parity class of every rule agreeing with rule `90` off adjacent cells
(`LocalRule.AgreesOffAdjacent.decim_iterate_add_single_eq_iff`) and on the coset class at rule `22`
(`decim_iterate_f22_add_single_eq_iff`). At the eleven reproducing rules that are not linear a hit
off the class and off the residue is nevertheless seen at the first level
(`decim_iterate_add_single_ne_oneParityHosts`, `decim_iterate_add_single_ne_doubledHosts`,
`decim_iterate_f22_add_single_ne`), while rule `18` does not see a gap-filling hit at any iterate
from one step on (`finRule_f18_iterate_add_gapFill`).

## Main results

* `decim_iterate_f90_add_single_eq_iff` — rule `90`: the reading is unchanged iff the hit is off
  the residue.
* `LocalRule.AgreesOffAdjacent.decim_iterate_add_single_eq_iff` /
  `decim_iterate_f22_add_single_eq_iff` — the same on the one-parity class and on the coset class
  at rule `22`, each with a `_nonvacuous` witness.
* `decim_iterate_add_single_ne_oneParityHosts` / `decim_iterate_add_single_ne_doubledHosts` /
  `decim_iterate_f22_add_single_ne` — a hit off the class and off the residue is seen.
* `finRule_f18_iterate_add_gapFill` — rule `18` erases a gap-filling hit at every iterate from one
  step on.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## Rule 90 -/

/-- Decimation is additive. -/
theorem decim_add (M : ℕ) (r : ℤ) (a b : FiniteConfiguration) :
    decim M r (a + b) = decim M r a + decim M r b := by
  ext i
  simp only [decim_apply, Finsupp.add_apply]

/-- The decimation of a single-cell state: the cell `(c - r) / 2 ^ M` when `c` is on the
residue, and zero otherwise. -/
theorem decim_single (M : ℕ) (r c : ℤ) :
    decim M r (Finsupp.single c (1 : ZMod 2))
      = if (2 : ℤ) ^ M ∣ c - r then Finsupp.single ((c - r) / 2 ^ M) 1 else 0 := by
  have hp : (2 : ℤ) ^ M ≠ 0 := pow_ne_zero M (by norm_num)
  ext i
  rw [decim_apply, Finsupp.single_apply]
  split_ifs with h1 h2 h2
  · have : (c - r) / 2 ^ M = i := by
      rw [Int.ediv_eq_iff_eq_mul_right hp h2]; linarith
    simp [this]
  · exfalso; apply h2; exact ⟨i, by linarith⟩
  · have : (c - r) / 2 ^ M ≠ i := by
      intro h; apply h1
      have := Int.ediv_mul_cancel h2
      rw [h] at this; linarith
    simp [this]
  · simp

private theorem finRule_f90_eq_rule90 : finRule f90 hq90 = rule90 := by
  ext s i
  rw [finRule_apply, rule90_apply, f90]

private theorem decim_iterate_f90_mul (M : ℕ) (r : ℤ) (k : ℕ) (y : FiniteConfiguration) :
    decim M r ((finRule f90 hq90)^[k * 2 ^ M] y) = (finRule f90 hq90)^[k] (decim M r y) := by
  rw [Nat.mul_comm, Function.iterate_mul]
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', decim_iterate_f90, ih]

private theorem iterate_f90_add (k : ℕ) (a b : FiniteConfiguration) :
    (finRule f90 hq90)^[k] (a + b) = (finRule f90 hq90)^[k] a + (finRule f90 hq90)^[k] b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, finRule_f90_eq_rule90, rule90_add]

private theorem iterate_f90_eq_zero_iff (k : ℕ) (a : FiniteConfiguration) :
    (finRule f90 hq90)^[k] a = 0 ↔ a = 0 := by
  have h0 : (finRule f90 hq90)^[k] 0 = 0 := by
    apply Function.iterate_fixed
    rw [finRule_f90_eq_rule90]; exact rule90_eq_zero_iff.mpr rfl
  have hinj : Function.Injective ((finRule f90 hq90)^[k]) := by
    rw [finRule_f90_eq_rule90]; exact rule90_injective.iterate k
  constructor
  · intro h; exact hinj (h.trans h0.symm)
  · intro h; rw [h]; exact h0

/-- At rule `90` the level reading of a hit differs from the level reading of the
state exactly when the hit lies on the sampled residue, at every level step and every state. -/
theorem decim_iterate_f90_add_single_eq_iff (M : ℕ) (r c : ℤ) (s : FiniteConfiguration) (k : ℕ) :
    decim M r ((finRule f90 hq90)^[k * 2 ^ M] (s + Finsupp.single c 1))
      = decim M r ((finRule f90 hq90)^[k * 2 ^ M] s) ↔ ¬ (2 : ℤ) ^ M ∣ c - r := by
  rw [iterate_f90_add, decim_add]
  have key : decim M r ((finRule f90 hq90)^[k * 2 ^ M] (Finsupp.single c 1)) = 0 ↔
      ¬ (2 : ℤ) ^ M ∣ c - r := by
    rw [decim_iterate_f90_mul, iterate_f90_eq_zero_iff, decim_single]
    split_ifs with h
    · simp [h]
    · simp [h]
  rw [← key]
  constructor
  · intro h; exact left_eq_add.mp h.symm
  · intro h; rw [h, add_zero]

/-! ## The one-parity class -/

/-- The level reading of a hit on the one-parity class of a rule agreeing with rule `90` off
adjacent cells differs from the reading of the state exactly when the hit lies on the residue. -/
theorem LocalRule.AgreesOffAdjacent.decim_iterate_add_single_eq_iff (f : LocalRule)
    (h : AgreesOffAdjacent f) (M : ℕ) (r c : ℤ) (s : FiniteConfiguration) (hs : OneParity s)
    (hs' : OneParity (s + Finsupp.single c 1)) (k : ℕ) :
    decim M r ((finRule f h.1)^[k * 2 ^ M] (s + Finsupp.single c 1))
      = decim M r ((finRule f h.1)^[k * 2 ^ M] s) ↔ ¬ (2 : ℤ) ^ M ∣ c - r := by
  rw [FiniteConfiguration.OneParity.iterate_eq_f90 f h _ hs',
    FiniteConfiguration.OneParity.iterate_eq_f90 f h _ hs]
  exact decim_iterate_f90_add_single_eq_iff M r c s k

/-- The hypotheses of the one-parity statement hold together, at rule `18`, the state with the
single cell at `0` and the hit at `2`. -/
theorem LocalRule.AgreesOffAdjacent.decim_iterate_add_single_eq_iff_nonvacuous :
    ∃ f : LocalRule, AgreesOffAdjacent f ∧ ∃ (s : FiniteConfiguration) (c : ℤ),
      OneParity s ∧ OneParity (s + Finsupp.single c 1) ∧ s = Finsupp.single 0 1 ∧ c = 2 := by
  refine ⟨f18, agreesOffAdjacent_f18, Finsupp.single 0 1, 2, ?_, ?_, rfl, rfl⟩
  · intro i j hi hj
    simp only [Finsupp.single_apply] at hi hj
    rw [even_iff_two_dvd]
    split_ifs at hi hj <;> first | omega | simp_all
  · intro i j hi hj
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
    rw [even_iff_two_dvd]
    split_ifs at hi hj <;> first | omega | simp_all

/-! ## The coset class at rule 22 -/

/-- The level reading of a hit on the coset class at rule `22` differs from the reading of the
state exactly when the hit lies on the residue. -/
theorem decim_iterate_f22_add_single_eq_iff (M : ℕ) (r c : ℤ) (s : FiniteConfiguration)
    (hs : Rule22Sparse.SupportInCoset 4 ⇑s)
    (hs' : Rule22Sparse.SupportInCoset 4 ⇑(s + (Finsupp.single c 1 : FiniteConfiguration)))
    (k : ℕ) :
    decim (M + 1) r ((finRule f22 hq22)^[k * 2 ^ (M + 1)] (s + Finsupp.single c 1))
      = decim (M + 1) r ((finRule f22 hq22)^[k * 2 ^ (M + 1)] s) ↔
        ¬ (2 : ℤ) ^ (M + 1) ∣ c - r := by
  have e : k * 2 ^ (M + 1) = 2 * (k * 2 ^ M) := by ring
  rw [e, finRule_f22_iterate_two_mul_eq_f90 _ hs', finRule_f22_iterate_two_mul_eq_f90 _ hs, ← e]
  exact decim_iterate_f90_add_single_eq_iff (M + 1) r c s k

/-- The hypotheses of the coset statement hold together, at the single cell `0` and the hit
at `4`. -/
theorem decim_iterate_f22_add_single_eq_iff_nonvacuous :
    ∃ (s : FiniteConfiguration) (c : ℤ), Rule22Sparse.SupportInCoset 4 ⇑s ∧
      Rule22Sparse.SupportInCoset 4 ⇑(s + (Finsupp.single c 1 : FiniteConfiguration)) ∧
      s = Finsupp.single 0 1 ∧ c = 4 := by
  refine ⟨Finsupp.single 0 1, 4, ?_, ?_, rfl, rfl⟩
  · intro i j hi hj
    simp only [Finsupp.single_apply] at hi hj
    split_ifs at hi hj <;> first | omega | simp_all
  · intro i j hi hj
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at hi hj
    split_ifs at hi hj <;> first | omega | simp_all

/-! ## The non-linear reproducing rules: a hit off the class is seen -/

/-- Each of the seven rules `18`, `82`, `146`, `210`, `218`, `26`, `154` sees, after two steps and
at the first level (`decim 1 0`), the hit at the cell written (at `-1` for rules `18`, `82`, `146`,
`210` and `218`, at `1` for `26` and `154`), off the class and off the residue, from the single cell
at `0`. -/
theorem decim_iterate_add_single_ne_oneParityHosts :
    decim 1 0 ((finRule f18 hq18)^[2] (Finsupp.single 0 1 + Finsupp.single (-1) 1))
        ≠ decim 1 0 ((finRule f18 hq18)^[2] (Finsupp.single 0 1)) ∧
    decim 1 0 ((finRule f82 hq82)^[2] (Finsupp.single 0 1 + Finsupp.single (-1) 1))
        ≠ decim 1 0 ((finRule f82 hq82)^[2] (Finsupp.single 0 1)) ∧
    decim 1 0 ((finRule f146 hq146)^[2] (Finsupp.single 0 1 + Finsupp.single (-1) 1))
        ≠ decim 1 0 ((finRule f146 hq146)^[2] (Finsupp.single 0 1)) ∧
    decim 1 0 ((finRule f210 hq210)^[2] (Finsupp.single 0 1 + Finsupp.single (-1) 1))
        ≠ decim 1 0 ((finRule f210 hq210)^[2] (Finsupp.single 0 1)) ∧
    decim 1 0 ((finRule f218 hq218)^[2] (Finsupp.single 0 1 + Finsupp.single (-1) 1))
        ≠ decim 1 0 ((finRule f218 hq218)^[2] (Finsupp.single 0 1)) ∧
    decim 1 0 ((finRule f26 hq26)^[2] (Finsupp.single 0 1 + Finsupp.single 1 1))
        ≠ decim 1 0 ((finRule f26 hq26)^[2] (Finsupp.single 0 1)) ∧
    decim 1 0 ((finRule f154 hq154)^[2] (Finsupp.single 0 1 + Finsupp.single 1 1))
        ≠ decim 1 0 ((finRule f154 hq154)^[2] (Finsupp.single 0 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  · have h := congrFun (congrArg (⇑) h) (-1)
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply, f18, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert
  · have h := congrFun (congrArg (⇑) h) (-1)
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply, f82, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert
  · have h := congrFun (congrArg (⇑) h) (-1)
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply, f146, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert
  · have h := congrFun (congrArg (⇑) h) (-1)
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply, f210, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert
  · have h := congrFun (congrArg (⇑) h) (0)
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply, f218, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert
  · have h := congrFun (congrArg (⇑) h) (1)
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply, f26, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert
  · have h := congrFun (congrArg (⇑) h) (1)
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply, f154, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert

/-- At the first level at scale four (`decim 2 0`), four steps, from the two cells `0` and `1`, the
hit at `-3` is seen at rules `94`, `122` and `126`. -/
theorem decim_iterate_add_single_ne_doubledHosts :
    decim 2 0 ((finRule f94 hq94)^[4] (Finsupp.single 0 1 + Finsupp.single 1 1
        + Finsupp.single (-3) 1))
        ≠ decim 2 0 ((finRule f94 hq94)^[4] (Finsupp.single 0 1 + Finsupp.single 1 1)) ∧
    decim 2 0 ((finRule f122 hq122)^[4] (Finsupp.single 0 1 + Finsupp.single 1 1
        + Finsupp.single (-3) 1))
        ≠ decim 2 0 ((finRule f122 hq122)^[4] (Finsupp.single 0 1 + Finsupp.single 1 1)) ∧
    decim 2 0 ((finRule f126 hq126)^[4] (Finsupp.single 0 1 + Finsupp.single 1 1
        + Finsupp.single (-3) 1))
        ≠ decim 2 0 ((finRule f126 hq126)^[4] (Finsupp.single 0 1 + Finsupp.single 1 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · have h := congrFun (congrArg (⇑) h) 0
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply] at h
    simp only [f94, wolframRule, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert
  · have h := congrFun (congrArg (⇑) h) 0
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply] at h
    simp only [f122, wolframRule, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert
  · have h := congrFun (congrArg (⇑) h) 0
    simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, finRule_apply] at h
    simp only [f126, wolframRule, Finsupp.add_apply, Finsupp.single_apply] at h
    revert h
    norm_num
    decide +revert

/-- At rule `22`, four steps, at `decim 2 0`, from the single cell `0`, the hit at `2` is seen. -/
theorem decim_iterate_f22_add_single_ne :
    decim 2 0 ((finRule f22 hq22)^[4] (Finsupp.single 0 1 + Finsupp.single 2 1))
      ≠ decim 2 0 ((finRule f22 hq22)^[4] (Finsupp.single 0 1)) := by
  intro h
  have h := congrFun (congrArg (⇑) h) 0
  simp only [decim_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, finRule_apply] at h
  simp only [f22, wolframRule, Finsupp.add_apply, Finsupp.single_apply] at h
  revert h
  norm_num
  decide +revert

/-! ## Rule 18 -/

/-- **Rule `18` does not see a gap-filling hit at any iterate from one step on.** -/
theorem finRule_f18_iterate_add_gapFill (s : FiniteConfiguration) (H : Finset ℤ)
    (hH : ∀ h ∈ H, s h = 0 ∧ s (h - 1) = 1 ∧ s (h + 1) = 1) (n : ℕ) :
    (finRule f18 hq18)^[n + 1] (s + Finsupp.indicator H (fun _ _ => 1))
      = (finRule f18 hq18)^[n + 1] s := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, finRule_f18_add_gapFill s H hH]

end ECA

/-- info: 'ECA.decim_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_add

/-- info: 'ECA.decim_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_single

/-- info: 'ECA.decim_iterate_f90_add_single_eq_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_iterate_f90_add_single_eq_iff

/-- info: 'ECA.LocalRule.AgreesOffAdjacent.decim_iterate_add_single_eq_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.decim_iterate_add_single_eq_iff

/-- info: 'ECA.LocalRule.AgreesOffAdjacent.decim_iterate_add_single_eq_iff_nonvacuous' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.decim_iterate_add_single_eq_iff_nonvacuous

/-- info: 'ECA.decim_iterate_f22_add_single_eq_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_iterate_f22_add_single_eq_iff

/-- info: 'ECA.decim_iterate_f22_add_single_eq_iff_nonvacuous' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_iterate_f22_add_single_eq_iff_nonvacuous

/-- info: 'ECA.decim_iterate_add_single_ne_oneParityHosts' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_iterate_add_single_ne_oneParityHosts

/-- info: 'ECA.decim_iterate_add_single_ne_doubledHosts' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_iterate_add_single_ne_doubledHosts

/-- info: 'ECA.decim_iterate_f22_add_single_ne' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.decim_iterate_f22_add_single_ne

/-- info: 'ECA.finRule_f18_iterate_add_gapFill' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.finRule_f18_iterate_add_gapFill
