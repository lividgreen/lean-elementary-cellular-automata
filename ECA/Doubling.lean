module

public import ECA.ObservedRays
public import ECA.EndpointClasses
public import Mathlib.Tactic.LinearCombination

/-!
# Doubling: the doubled sub-system of a quiescent rule
([RuleSpace] §5 Proposition 5.8, row RS-28; [RuleSpace] §2 for the setting, [RuleSpace] §4
Proposition 4.2(iv) for rule 90's doubling identity, [RuleSpace] §5 Proposition 5.7 for the
decimation tower)

The doubled state `FiniteConfiguration.dbl x` of a state `x` of the line carries `x i` on both cells
`2 i` and `2 i + 1`. A radius-one rule `f` with `f 0 0 0 = 0` that agrees with rule 90 wherever two
adjacent cells are equal (`LocalRule.DoubledAgree f`: `f a a b = a + b` and `f a b b = a + b`) takes
doubled states to doubled states in two steps, and those two steps are one step of rule 90 on the
undoubled state (`LocalRule.finRule_two_dbl`); iterated, `2 ^ (M + 1)` steps of `f` on
`FiniteConfiguration.dbl x` are `FiniteConfiguration.dbl` of `2 ^ M` steps of rule 90 on `x`
(`LocalRule.finRule_iterate_dbl`). Exactly four quiescent rules meet the condition: rules `90`,
`94`, `122` and `126` (`card_doubledAgree`, `LocalRule.doubledAgree_cases`). Rule `22` does not, and
two steps of it do not preserve doubled states (`not_doubled_f22`). Grouping the doubled state in
blocks of two cells, with two steps as one, is a blocking transformation in Wolfram's (1986) sense.

## Main results

* `FiniteConfiguration.dbl` / `FiniteConfiguration.dbl_apply` — the doubled state `j ↦ x (j / 2)`.
* `LocalRule.DoubledAgree` — the agreement condition on a rule.
* `f94`, `f122`, `f126`, `f22` — the rules, by Wolfram's bit convention (`wolframRule`).
* `LocalRule.finRule_two_dbl` — two steps of a doubled-agreeing rule on `FiniteConfiguration.dbl x`
  are `FiniteConfiguration.dbl` of one step of rule 90.
* `LocalRule.finRule_iterate_dbl` — `2 ^ (M + 1)` steps on `FiniteConfiguration.dbl x` are
  `FiniteConfiguration.dbl` of `2 ^ M` steps of rule 90.
* `card_doubledAgree` / `LocalRule.doubledAgree_cases` — exactly four quiescent rules meet the
  condition.
* `not_doubled_f22` / `not_doubledAgree_f22` — **the guard**: rule `22` fails the condition and
  its second iterate leaves the doubled states (`doubledWitness`).
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- **The doubled state**: `FiniteConfiguration.dbl x` carries `x i` on the cells `2 i` and
`2 i + 1` ([RuleSpace] §2's line, with Euclidean division). -/
noncomputable def FiniteConfiguration.dbl (x : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.onFinset (x.support.image (fun i : ℤ => 2 * i) ∪ x.support.image (fun i : ℤ => 2 * i + 1))
    (fun j => x (j / 2))
    (fun j hj => by
      have hx : x (j / 2) ≠ 0 := hj
      have hm : j / 2 ∈ x.support := Finsupp.mem_support_iff.mpr hx
      rcases Int.emod_two_eq_zero_or_one j with h | h
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j / 2, hm, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j / 2, hm, by omega⟩))

/-- The value of the doubled state at a cell. -/
theorem FiniteConfiguration.dbl_apply (x : FiniteConfiguration) (j : ℤ) : dbl x j = x (j / 2) :=
  Finsupp.onFinset_apply

/-- **Agreement with rule 90 where two adjacent cells are equal**: `f a a b = a + b` and
`f a b b = a + b` ([RuleSpace] §4 Proposition 4.2(iv) is the rule-90 identity this feeds). -/
def LocalRule.DoubledAgree (f : LocalRule) : Prop :=
  ∀ a b, f a a b = a + b ∧ f a b b = a + b

namespace LocalRule
instance (f : LocalRule) : Decidable (DoubledAgree f) := by
  unfold DoubledAgree; infer_instance
end LocalRule

/-- **Wolfram's numbering** ([RuleSpace] §2): bit `4 a + 2 b + c` of `n` is `f a b c`. -/
def wolframRule (n : ℕ) : LocalRule := fun a b c =>
  ((n / 2 ^ (4 * a.val + 2 * b.val + c.val) % 2 : ℕ) : ZMod 2)

/-- Rule `94`. -/
def f94 : LocalRule := wolframRule 94

/-- Rule `122`. -/
def f122 : LocalRule := wolframRule 122

/-- Rule `126`. -/
def f126 : LocalRule := wolframRule 126

/-- Rule `22`. -/
def f22 : LocalRule := wolframRule 22

theorem hq94 : f94 0 0 0 = 0 := by decide
theorem hq122 : f122 0 0 0 = 0 := by decide
theorem hq126 : f126 0 0 0 = 0 := by decide
theorem hq22 : f22 0 0 0 = 0 := by decide

/-- Rule `94`, its eight values `f 0 0 0 … f 1 1 1` in Wolfram's bit order. -/
theorem f94_values :
    f94 0 0 0 = 0 ∧ f94 0 0 1 = 1 ∧ f94 0 1 0 = 1 ∧ f94 0 1 1 = 1 ∧
      f94 1 0 0 = 1 ∧ f94 1 0 1 = 0 ∧ f94 1 1 0 = 1 ∧ f94 1 1 1 = 0 := by decide

/-- Rule `122`, its eight values in Wolfram's bit order. -/
theorem f122_values :
    f122 0 0 0 = 0 ∧ f122 0 0 1 = 1 ∧ f122 0 1 0 = 0 ∧ f122 0 1 1 = 1 ∧
      f122 1 0 0 = 1 ∧ f122 1 0 1 = 1 ∧ f122 1 1 0 = 1 ∧ f122 1 1 1 = 0 := by decide

/-- Rule `126`, its eight values in Wolfram's bit order. -/
theorem f126_values :
    f126 0 0 0 = 0 ∧ f126 0 0 1 = 1 ∧ f126 0 1 0 = 1 ∧ f126 0 1 1 = 1 ∧
      f126 1 0 0 = 1 ∧ f126 1 0 1 = 1 ∧ f126 1 1 0 = 1 ∧ f126 1 1 1 = 0 := by decide

/-- Rule `22`, its eight values in Wolfram's bit order. -/
theorem f22_values :
    f22 0 0 0 = 0 ∧ f22 0 0 1 = 1 ∧ f22 0 1 0 = 1 ∧ f22 0 1 1 = 0 ∧
      f22 1 0 0 = 1 ∧ f22 1 0 1 = 0 ∧ f22 1 1 0 = 0 ∧ f22 1 1 1 = 0 := by decide

private theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

/-- One step of a doubled-agreeing rule on a doubled state: the values at the even and the odd
cell of each pair. -/
private theorem step_dbl {f : LocalRule} (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (x : FiniteConfiguration) (i : ℤ) :
    finRule f hq (dbl x) (2 * i) = x (i - 1) + x i ∧
      finRule f hq (dbl x) (2 * i + 1) = x i + x (i + 1) := by
  rw [finRule_apply, finRule_apply]
  simp only [dbl_apply]
  have e1 : (2 * i - 1) / 2 = i - 1 := by omega
  have e2 : 2 * i / 2 = i := by omega
  have e3 : (2 * i + 1) / 2 = i := by omega
  have e4 : (2 * i + 1 - 1) / 2 = i := by omega
  have e5 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  exact ⟨(hA _ _).2, (hA _ _).1⟩

/-- **Two steps of a doubled-agreeing rule on a doubled state are `FiniteConfiguration.dbl` of one
step of rule 90** ([RuleSpace] §4 Proposition 4.2(iv); the setting is [RuleSpace] §2). -/
theorem LocalRule.finRule_two_dbl (f : LocalRule) (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (x : FiniteConfiguration) :
    (finRule f hq)^[2] (dbl x) = dbl (finRule f90 hq90 x) := by
  ext j
  rw [dbl_apply, finRule_apply]
  change finRule f hq (finRule f hq (dbl x)) j = _
  rw [finRule_apply]
  rcases Int.even_or_odd' j with ⟨i, rfl | rfl⟩
  · have e : 2 * i / 2 = i := by omega
    have h1 : 2 * i - 1 = 2 * (i - 1) + 1 := by omega
    have a1 := (step_dbl hq hA x (i - 1)).2
    rw [show i - 1 + 1 = i by omega] at a1
    rw [e, h1, a1, (step_dbl hq hA x i).1, (step_dbl hq hA x i).2, (hA _ _).1, f90]
    linear_combination (x i) * two_eq_zero
  · have e : (2 * i + 1) / 2 = i := by omega
    have h1 : 2 * i + 1 - 1 = 2 * i := by omega
    have h2 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    have a1 := (step_dbl hq hA x (i + 1)).1
    rw [show i + 1 - 1 = i by omega] at a1
    rw [e, h1, h2, (step_dbl hq hA x i).1, (step_dbl hq hA x i).2, a1, (hA _ _).2, f90]
    linear_combination (x i) * two_eq_zero

/-- **`2 ^ (M + 1)` steps of a doubled-agreeing rule on `FiniteConfiguration.dbl x` are
`FiniteConfiguration.dbl` of `2 ^ M` steps of rule 90** ([RuleSpace] §4 Proposition 4.2(iv);
[RuleSpace] §5 Proposition 5.7 for the tower this sits beside). -/
theorem LocalRule.finRule_iterate_dbl (f : LocalRule) (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (M : ℕ) (x : FiniteConfiguration) :
    (finRule f hq)^[2 ^ (M + 1)] (dbl x) = dbl ((finRule f90 hq90)^[2 ^ M] x) := by
  have key : ∀ k : ℕ, ((finRule f hq)^[2])^[k] (dbl x) = dbl ((finRule f90 hq90)^[k] x) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply' ((finRule f hq)^[2]) k, ih,
          Function.iterate_succ_apply' (finRule f90 hq90) k, finRule_two_dbl f hq hA]
  rw [pow_succ, mul_comm, Function.iterate_mul]
  exact key _

theorem doubledAgree_f90 : DoubledAgree f90 := by decide
theorem doubledAgree_f94 : DoubledAgree f94 := by decide
theorem doubledAgree_f122 : DoubledAgree f122 := by decide
theorem doubledAgree_f126 : DoubledAgree f126 := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- the ambient type has 256 members, as in `card_quiescent`.
/-- **Exactly four quiescent rules meet `LocalRule.DoubledAgree`** (the instances
`doubledAgree_f90`, `doubledAgree_f94`, `doubledAgree_f122`, `doubledAgree_f126` are its witnesses).
-/
theorem card_doubledAgree :
    Fintype.card {f : LocalRule // f 0 0 0 = 0 ∧ DoubledAgree f} = 4 := by
  decide

set_option maxRecDepth 8000 in
set_option synthInstance.maxHeartbeats 400000 in
-- the `Decidable` instance for a universal over 256 rules and four disjuncts needs the larger
-- synthesis limits.
set_option synthInstance.maxSize 2000 in
set_option maxHeartbeats 4000000 in
-- the decision is over 256 rules and four disjuncts; the `Decidable` instance needs the larger
-- synthesis limits and the kernel reduction the larger recursion and heartbeat limits.
/-- **The four are all of them**: a quiescent rule agreeing with rule 90 at equal adjacent cells
is rule `90`, `94`, `122` or `126`. -/
theorem LocalRule.doubledAgree_cases (f : LocalRule) :
    DoubledAgree f ∧ f 0 0 0 = 0 → f = f90 ∨ f = f94 ∨ f = f122 ∨ f = f126 := by
  intro h
  have key : ∀ g : LocalRule,
      (DoubledAgree g ∧ g 0 0 0 = 0 →
        (∀ a b c, g a b c = f90 a b c) ∨ (∀ a b c, g a b c = f94 a b c) ∨
        (∀ a b c, g a b c = f122 a b c) ∨ (∀ a b c, g a b c = f126 a b c)) := by
    decide
  rcases key f h with h | h | h | h
  · exact Or.inl (funext fun a => funext fun b => funext fun c => h a b c)
  · exact Or.inr (Or.inl (funext fun a => funext fun b => funext fun c => h a b c))
  · exact Or.inr (Or.inr (Or.inl (funext fun a => funext fun b => funext fun c => h a b c)))
  · exact Or.inr (Or.inr (Or.inr (funext fun a => funext fun b => funext fun c => h a b c)))

/-- **The guard's state**: the two adjacent cells `0` and `1` of the line, whose double is
four adjacent ones. -/
noncomputable def doubledWitness : FiniteConfiguration := Finsupp.single 0 1 + Finsupp.single 1 1

theorem not_doubledAgree_f22 : ¬ DoubledAgree f22 := by decide

/-- **The guard**: two steps of rule `22` do not take every doubled state to a doubled state;
`doubledWitness` is one that escapes. -/
theorem not_doubled_f22 :
    ¬ ∀ x, ∃ y, (finRule f22 hq22)^[2] (dbl x) = dbl y := by
  intro h
  obtain ⟨y, hy⟩ := h doubledWitness
  have h0 := congrArg (fun s => s 0) hy
  have h1 := congrArg (fun s => s 1) hy
  simp only [dbl_apply] at h0 h1
  have e : (1 : ℤ) / 2 = 0 := by omega
  rw [e] at h1
  have hh : (finRule f22 hq22)^[2] (dbl doubledWitness) 0 =
      (finRule f22 hq22)^[2] (dbl doubledWitness) 1 := by
    rw [h0, h1]
    simp
  change finRule f22 hq22 (finRule f22 hq22 (dbl doubledWitness)) 0 =
      finRule f22 hq22 (finRule f22 hq22 (dbl doubledWitness)) 1 at hh
  simp only [finRule_apply, dbl_apply, doubledWitness, Finsupp.add_apply,
    Finsupp.single_apply] at hh
  revert hh
  norm_num [f22, wolframRule]
  decide

end ECA

/-- info: 'ECA.LocalRule.finRule_two_dbl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.finRule_two_dbl

/-- info: 'ECA.LocalRule.finRule_iterate_dbl' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.finRule_iterate_dbl

/-- info: 'ECA.card_doubledAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.card_doubledAgree

/-- info: 'ECA.LocalRule.doubledAgree_cases' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.doubledAgree_cases

/-- info: 'ECA.not_doubled_f22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_doubled_f22

/-- info: 'ECA.not_doubledAgree_f22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_doubledAgree_f22

/-- info: 'ECA.doubledAgree_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.doubledAgree_f90

/-- info: 'ECA.doubledAgree_f94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.doubledAgree_f94

/-- info: 'ECA.doubledAgree_f122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.doubledAgree_f122

/-- info: 'ECA.doubledAgree_f126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.doubledAgree_f126
