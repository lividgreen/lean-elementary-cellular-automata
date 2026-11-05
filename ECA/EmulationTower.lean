module

public import ECA.Decimation
public import ECA.ReproductionBracket

/-!
# Rule 90's tower hosted at the reproducing rules that are not linear
([RuleSpace] §5 Proposition 5.7 and Proposition 5.9)

Decimation reads the `2 ^ M`-th iterate of rule `90` as one step of rule `90`
(`decim_iterate_f90`). Three classes of states carry the same reading at a host that is not
linear, the iterate being the rule's own: the one-parity states of a rule agreeing with rule `90`
off adjacent cells (`LocalRule.AgreesOffAdjacent`), the doubled states of a rule agreeing with
rule `90` at equal adjacent cells (`LocalRule.DoubledAgree`), and the configurations supported in
one coset of `4ℤ` at rule `22` (`Rule22Sparse.SupportInCoset`). On each class the rule's
`2 ^ M`-th (respectively `2 ^ (M + 1)`-th) iterate keeps the class and decimation is a
semiconjugacy of it onto rule `90` in the sense of `Nonautonomous.Semiconj`, so the next level of
each such rule is rule `90` and every level above is the tower of `decim_decim`.

## Main results

* `LocalRule.AgreesOffAdjacent.positivelyInvariant_oneParity` /
  `LocalRule.AgreesOffAdjacent.semiconj_decim` — the one-parity class.
* `LocalRule.DoubledAgree.positivelyInvariant_range_dbl` /
  `LocalRule.DoubledAgree.semiconj_decim` — the doubled states;
  `LocalRule.DoubledAgree.semiconj_decim_nonvacuous` holds the hypotheses together.
* `positivelyInvariant_supportInCoset_f22` / `semiconj_decim_f22` — the coset class at rule `22`.
* `not_semiconj_decim_f22_oneParity` — **the guard**: at rule `22` the one-parity class is too
  big.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule Nonautonomous

/-! ## The one-parity class -/

/-- The one-parity class is positively invariant under every iterate of a rule agreeing with
rule `90` off adjacent cells. -/
theorem LocalRule.AgreesOffAdjacent.positivelyInvariant_oneParity (f : LocalRule)
    (h : AgreesOffAdjacent f) (n : ℕ) :
    PositivelyInvariant ((finRule f h.1)^[n]) (fun _ => {s | OneParity s}) := by
  intro t s hs
  change OneParity _
  rw [FiniteConfiguration.OneParity.iterate_eq_f90 f h s hs n]
  exact oneParity_iterate_finRule_f90 s hs n

/-- Decimation at scale `2 ^ M` is a semiconjugacy of the `2 ^ M`-th iterate of a rule agreeing
with rule `90` off adjacent cells, on the one-parity class, onto rule `90`
([RuleSpace] §5 Proposition 5.7). -/
theorem LocalRule.AgreesOffAdjacent.semiconj_decim (f : LocalRule) (h : AgreesOffAdjacent f)
    (M : ℕ) (r : ℤ) :
    Semiconj ((finRule f h.1)^[2 ^ M]) (finRule f90 hq90) (fun _ => decim M r)
      (fun _ => {s | OneParity s}) := by
  intro t s hs
  rw [FiniteConfiguration.OneParity.iterate_eq_f90 f h s hs]
  exact decim_iterate_f90 M r s

/-! ## The doubled states -/

/-- The doubled states are positively invariant under the `2 ^ (M + 1)`-th iterate of a rule
agreeing with rule `90` at equal adjacent cells. -/
theorem LocalRule.DoubledAgree.positivelyInvariant_range_dbl (f : LocalRule) (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (M : ℕ) :
    PositivelyInvariant ((finRule f hq)^[2 ^ (M + 1)]) (fun _ => Set.range dbl) := by
  rintro t _ ⟨x, rfl⟩
  exact ⟨_, (finRule_iterate_dbl f hq hA M x).symm⟩

private theorem decim_succ_dbl (M : ℕ) (y : FiniteConfiguration) :
    decim (M + 1) 0 (dbl y) = decim M 0 y := by
  ext i
  rw [decim_apply, decim_apply, dbl_apply]
  congr 1
  rw [show (0 : ℤ) + 2 ^ (M + 1) * i = 2 * (2 ^ M * i) by ring,
    Int.mul_ediv_cancel_left _ two_ne_zero]
  ring

/-- Decimation at scale `2 ^ (M + 1)` and residue `0` is a semiconjugacy of that iterate, on the
doubled states, onto rule `90` ([RuleSpace] §5 Proposition 5.7). -/
theorem LocalRule.DoubledAgree.semiconj_decim (f : LocalRule) (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (M : ℕ) :
    Semiconj ((finRule f hq)^[2 ^ (M + 1)]) (finRule f90 hq90) (fun _ => decim (M + 1) 0)
      (fun _ => Set.range dbl) := by
  rintro t _ ⟨x, rfl⟩
  beta_reduce
  rw [finRule_iterate_dbl f hq hA M x, decim_succ_dbl, decim_succ_dbl]
  exact decim_iterate_f90 M 0 x

/-- The hypotheses of the doubled semiconjugacy hold together, at rule `94` and scale two. -/
theorem LocalRule.DoubledAgree.semiconj_decim_nonvacuous :
    ∃ (f : LocalRule) (hq : f 0 0 0 = 0), DoubledAgree f ∧
      Semiconj ((finRule f hq)^[2 ^ 1]) (finRule f90 hq90) (fun _ => decim 1 0)
        (fun _ => Set.range dbl) := by
  have hq : f94 0 0 0 = 0 := by decide
  exact ⟨f94, hq, doubledAgree_f94, DoubledAgree.semiconj_decim f94 hq doubledAgree_f94 0⟩

/-! ## The coset class at rule `22` -/

/-- The configurations supported in one coset of `4ℤ` are positively invariant under the
`2 ^ (M + 1)`-th iterate of rule `22`. -/
theorem positivelyInvariant_supportInCoset_f22 (M : ℕ) :
    PositivelyInvariant ((finRule f22 hq22)^[2 ^ (M + 1)])
      (fun _ => {s | Rule22Sparse.SupportInCoset 4 ⇑s}) := by
  intro t s hs
  change Rule22Sparse.SupportInCoset 4 _
  rw [coe_finRule_iterate, f22_eq_rule22, pow_succ']
  exact Rule22Sparse.supportInCoset_iterate_step_rule22_two_mul hs _

/-- Decimation at scale `2 ^ (M + 1)` is a semiconjugacy of that iterate of rule `22`, on the
coset class, onto rule `90` ([RuleSpace] §5 Proposition 5.9). -/
theorem semiconj_decim_f22 (M : ℕ) (r : ℤ) :
    Semiconj ((finRule f22 hq22)^[2 ^ (M + 1)]) (finRule f90 hq90) (fun _ => decim (M + 1) r)
      (fun _ => {s | Rule22Sparse.SupportInCoset 4 ⇑s}) := by
  intro t s hs
  rw [pow_succ', finRule_f22_iterate_two_mul_eq_f90 s hs, ← pow_succ']
  exact decim_iterate_f90 (M + 1) r s

/-- **The guard**: at rule `22` the one-parity class does not do, the two cells `0` and `2`
breaking the semiconjugacy at scale two. -/
theorem not_semiconj_decim_f22_oneParity :
    ¬ Semiconj ((finRule f22 hq22)^[2 ^ 1]) (finRule f90 hq90) (fun _ => decim 1 0)
      (fun _ => {s | OneParity s}) := by
  intro H
  have hs : OneParity (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1) := by
    intro i j hi hj
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
    rw [even_iff_two_dvd]
    split_ifs at hi hj <;> first | omega | simp_all
  have h := congrFun (congrArg (⇑) (H 0 _ hs)) 0
  simp only [pow_one, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    finRule_apply, decim_apply] at h
  simp only [f22, f90, Finsupp.add_apply, Finsupp.single_apply] at h
  revert h
  norm_num
  decide +revert

end ECA

/-- info: 'ECA.LocalRule.AgreesOffAdjacent.positivelyInvariant_oneParity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.positivelyInvariant_oneParity

/-- info: 'ECA.LocalRule.AgreesOffAdjacent.semiconj_decim' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.AgreesOffAdjacent.semiconj_decim

/-- info: 'ECA.LocalRule.DoubledAgree.positivelyInvariant_range_dbl' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.DoubledAgree.positivelyInvariant_range_dbl

/-- info: 'ECA.LocalRule.DoubledAgree.semiconj_decim' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.DoubledAgree.semiconj_decim

/-- info: 'ECA.LocalRule.DoubledAgree.semiconj_decim_nonvacuous' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.DoubledAgree.semiconj_decim_nonvacuous

/-- info: 'ECA.positivelyInvariant_supportInCoset_f22' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.positivelyInvariant_supportInCoset_f22

/-- info: 'ECA.semiconj_decim_f22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.semiconj_decim_f22

/-- info: 'ECA.not_semiconj_decim_f22_oneParity' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_semiconj_decim_f22_oneParity
