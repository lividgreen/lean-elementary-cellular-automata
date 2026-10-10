/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.ObservedRays
public import CellularAutomata.EndpointClasses
public import Mathlib.Tactic.LinearCombination

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Doubling: the doubled sub-world of a quiescent table
([RuleSpace] §5 Proposition 5.8, row RS-28; [RuleSpace] §2 for the setting, [RuleSpace] §4
Proposition 4.2(iv) for table 90's doubling identity, [RuleSpace] §5 Proposition 5.7 for the
decimation tower)

The doubled state `dbl x` of a state `x` of the line carries `x i` on both cells `2 i` and
`2 i + 1`. A radius-one table `f` with `f 0 0 0 = 0` that agrees with table 90 wherever two
adjacent cells are equal (`DoubledAgree f`: `f a a b = a + b` and `f a b b = a + b`) takes doubled
states to doubled states in two steps, and those two steps are one step of table 90 on the
undoubled state (`tableRule_two_dbl`); iterated, `2 ^ (M + 1)` steps of `f` on `dbl x` are `dbl` of
`2 ^ M` steps of table 90 on `x` (`tableRule_iterate_dbl`). Exactly four quiescent tables meet the
condition: tables `90`, `94`, `122` and `126` (`card_doubledAgree`, `doubledAgree_cases`).
Table `22` does not, and two steps of it do not preserve doubled states (`not_doubled_f22`).

## Main results

* `dbl` / `dbl_apply` — the doubled state `j ↦ x (j / 2)`.
* `DoubledAgree` — the agreement condition on a table.
* `f94`, `f122`, `f126`, `f22` — the tables, by Wolfram's bit convention (`wolframTable`).
* `tableRule_two_dbl` — two steps of a doubled-agreeing table on `dbl x` are `dbl` of one step of
  table 90.
* `tableRule_iterate_dbl` — `2 ^ (M + 1)` steps on `dbl x` are `dbl` of `2 ^ M` steps of table 90.
* `card_doubledAgree` / `doubledAgree_cases` — exactly four quiescent tables meet the condition.
* `not_doubled_f22` / `not_doubledAgree_f22` — **the guard**: table `22` fails the condition and
  its second iterate leaves the doubled states (`doubledWitness`).
-/

@[expose] public section

namespace Doubling

open ExtremeTapWidth EndpointClasses
open ObservedColumn (hq90)

/-- **The doubled state**: `dbl x` carries `x i` on the cells `2 i` and `2 i + 1`
([RuleSpace] §2's line, with Euclidean division). -/
noncomputable def dbl (x : ℤ →₀ ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.onFinset (x.support.image (fun i : ℤ => 2 * i) ∪ x.support.image (fun i : ℤ => 2 * i + 1))
    (fun j => x (j / 2))
    (fun j hj => by
      have hx : x (j / 2) ≠ 0 := hj
      have hm : j / 2 ∈ x.support := Finsupp.mem_support_iff.mpr hx
      rcases Int.emod_two_eq_zero_or_one j with h | h
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j / 2, hm, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j / 2, hm, by omega⟩))

/-- The value of the doubled state at a cell. -/
theorem dbl_apply (x : ℤ →₀ ZMod 2) (j : ℤ) : dbl x j = x (j / 2) :=
  Finsupp.onFinset_apply

/-- **Agreement with table 90 where two adjacent cells are equal**: `f a a b = a + b` and
`f a b b = a + b` ([RuleSpace] §4 Proposition 4.2(iv) is the table-90 identity this feeds). -/
def DoubledAgree (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  ∀ a b, f a a b = a + b ∧ f a b b = a + b

instance (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Decidable (DoubledAgree f) := by
  unfold DoubledAgree; infer_instance

/-- **Wolfram's numbering** ([RuleSpace] §2): bit `4 a + 2 b + c` of `n` is `f a b c`. -/
def wolframTable (n : ℕ) (a b c : ZMod 2) : ZMod 2 :=
  ((n / 2 ^ (4 * a.val + 2 * b.val + c.val) % 2 : ℕ) : ZMod 2)

/-- Table `94`. -/
def f94 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := wolframTable 94

/-- Table `122`. -/
def f122 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := wolframTable 122

/-- Table `126`. -/
def f126 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := wolframTable 126

/-- Table `22`. -/
def f22 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := wolframTable 22

theorem hq94 : f94 0 0 0 = 0 := by decide
theorem hq122 : f122 0 0 0 = 0 := by decide
theorem hq126 : f126 0 0 0 = 0 := by decide
theorem hq22 : f22 0 0 0 = 0 := by decide

/-- Table `94`, its eight values `f 0 0 0 … f 1 1 1` in Wolfram's bit order. -/
theorem f94_values :
    f94 0 0 0 = 0 ∧ f94 0 0 1 = 1 ∧ f94 0 1 0 = 1 ∧ f94 0 1 1 = 1 ∧
      f94 1 0 0 = 1 ∧ f94 1 0 1 = 0 ∧ f94 1 1 0 = 1 ∧ f94 1 1 1 = 0 := by decide

/-- Table `122`, its eight values in Wolfram's bit order. -/
theorem f122_values :
    f122 0 0 0 = 0 ∧ f122 0 0 1 = 1 ∧ f122 0 1 0 = 0 ∧ f122 0 1 1 = 1 ∧
      f122 1 0 0 = 1 ∧ f122 1 0 1 = 1 ∧ f122 1 1 0 = 1 ∧ f122 1 1 1 = 0 := by decide

/-- Table `126`, its eight values in Wolfram's bit order. -/
theorem f126_values :
    f126 0 0 0 = 0 ∧ f126 0 0 1 = 1 ∧ f126 0 1 0 = 1 ∧ f126 0 1 1 = 1 ∧
      f126 1 0 0 = 1 ∧ f126 1 0 1 = 1 ∧ f126 1 1 0 = 1 ∧ f126 1 1 1 = 0 := by decide

/-- Table `22`, its eight values in Wolfram's bit order. -/
theorem f22_values :
    f22 0 0 0 = 0 ∧ f22 0 0 1 = 1 ∧ f22 0 1 0 = 1 ∧ f22 0 1 1 = 0 ∧
      f22 1 0 0 = 1 ∧ f22 1 0 1 = 0 ∧ f22 1 1 0 = 0 ∧ f22 1 1 1 = 0 := by decide

private theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

/-- One step of a doubled-agreeing table on a doubled state: the values at the even and the odd
cell of each pair. -/
private theorem step_dbl {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (x : ℤ →₀ ZMod 2) (i : ℤ) :
    tableRule f hq (dbl x) (2 * i) = x (i - 1) + x i ∧
      tableRule f hq (dbl x) (2 * i + 1) = x i + x (i + 1) := by
  rw [tableRule_apply, tableRule_apply]
  simp only [dbl_apply]
  have e1 : (2 * i - 1) / 2 = i - 1 := by omega
  have e2 : 2 * i / 2 = i := by omega
  have e3 : (2 * i + 1) / 2 = i := by omega
  have e4 : (2 * i + 1 - 1) / 2 = i := by omega
  have e5 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  exact ⟨(hA _ _).2, (hA _ _).1⟩

/-- **Two steps of a doubled-agreeing table on a doubled state are `dbl` of one step of table 90**
([RuleSpace] §4 Proposition 4.2(iv); the setting is [RuleSpace] §2). -/
theorem tableRule_two_dbl (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (x : ℤ →₀ ZMod 2) :
    (tableRule f hq)^[2] (dbl x) = dbl (tableRule f90 hq90 x) := by
  ext j
  rw [dbl_apply, tableRule_apply]
  change tableRule f hq (tableRule f hq (dbl x)) j = _
  rw [tableRule_apply]
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

/-- **`2 ^ (M + 1)` steps of a doubled-agreeing table on `dbl x` are `dbl` of `2 ^ M` steps of
table 90** ([RuleSpace] §4 Proposition 4.2(iv); [RuleSpace] §5 Proposition 5.7 for the tower this
sits beside). -/
theorem tableRule_iterate_dbl (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (hA : DoubledAgree f) (M : ℕ) (x : ℤ →₀ ZMod 2) :
    (tableRule f hq)^[2 ^ (M + 1)] (dbl x) = dbl ((tableRule f90 hq90)^[2 ^ M] x) := by
  have key : ∀ k : ℕ, ((tableRule f hq)^[2])^[k] (dbl x) = dbl ((tableRule f90 hq90)^[k] x) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply' ((tableRule f hq)^[2]) k, ih,
          Function.iterate_succ_apply' (tableRule f90 hq90) k, tableRule_two_dbl f hq hA]
  rw [pow_succ, mul_comm, Function.iterate_mul]
  exact key _

theorem doubledAgree_f90 : DoubledAgree f90 := by decide
theorem doubledAgree_f94 : DoubledAgree f94 := by decide
theorem doubledAgree_f122 : DoubledAgree f122 := by decide
theorem doubledAgree_f126 : DoubledAgree f126 := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- the ambient type has 256 members, as in `EndpointClasses.card_quiescent`.
/-- **Exactly four quiescent tables meet `DoubledAgree`** (the instances `doubledAgree_f90`,
`doubledAgree_f94`, `doubledAgree_f122`, `doubledAgree_f126` are its witnesses). -/
theorem card_doubledAgree :
    Fintype.card {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 // f 0 0 0 = 0 ∧ DoubledAgree f} = 4 := by
  decide

set_option maxRecDepth 8000 in
set_option synthInstance.maxHeartbeats 400000 in
-- the `Decidable` instance for a universal over 256 tables and four disjuncts needs the larger
-- synthesis limits.
set_option synthInstance.maxSize 2000 in
set_option maxHeartbeats 4000000 in
-- the decision is over 256 tables and four disjuncts; the `Decidable` instance needs the larger
-- synthesis limits and the kernel reduction the larger recursion and heartbeat limits.
/-- **The four are all of them**: a quiescent table agreeing with table 90 at equal adjacent cells
is table `90`, `94`, `122` or `126`. -/
theorem doubledAgree_cases (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) :
    DoubledAgree f ∧ f 0 0 0 = 0 → f = f90 ∨ f = f94 ∨ f = f122 ∨ f = f126 := by
  intro h
  have key : ∀ g : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2,
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
noncomputable def doubledWitness : ℤ →₀ ZMod 2 := Finsupp.single 0 1 + Finsupp.single 1 1

theorem not_doubledAgree_f22 : ¬ DoubledAgree f22 := by decide

/-- **The guard**: two steps of table `22` do not take every doubled state to a doubled state;
`doubledWitness` is one that escapes. -/
theorem not_doubled_f22 :
    ¬ ∀ x, ∃ y, (tableRule f22 hq22)^[2] (dbl x) = dbl y := by
  intro h
  obtain ⟨y, hy⟩ := h doubledWitness
  have h0 := congrArg (fun s => s 0) hy
  have h1 := congrArg (fun s => s 1) hy
  simp only [dbl_apply] at h0 h1
  have e : (1 : ℤ) / 2 = 0 := by omega
  rw [e] at h1
  have hh : (tableRule f22 hq22)^[2] (dbl doubledWitness) 0 =
      (tableRule f22 hq22)^[2] (dbl doubledWitness) 1 := by
    rw [h0, h1]
    simp
  change tableRule f22 hq22 (tableRule f22 hq22 (dbl doubledWitness)) 0 =
      tableRule f22 hq22 (tableRule f22 hq22 (dbl doubledWitness)) 1 at hh
  simp only [tableRule_apply, dbl_apply, doubledWitness, Finsupp.add_apply,
    Finsupp.single_apply] at hh
  revert hh
  norm_num [f22, wolframTable]
  decide

end Doubling

/-- info: 'Doubling.tableRule_two_dbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.tableRule_two_dbl

/-- info: 'Doubling.tableRule_iterate_dbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.tableRule_iterate_dbl

/-- info: 'Doubling.card_doubledAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.card_doubledAgree

/-- info: 'Doubling.doubledAgree_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.doubledAgree_cases

/-- info: 'Doubling.not_doubled_f22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.not_doubled_f22

/-- info: 'Doubling.not_doubledAgree_f22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.not_doubledAgree_f22

/-- info: 'Doubling.doubledAgree_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.doubledAgree_f90

/-- info: 'Doubling.doubledAgree_f94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.doubledAgree_f94

/-- info: 'Doubling.doubledAgree_f122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.doubledAgree_f122

/-- info: 'Doubling.doubledAgree_f126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Doubling.doubledAgree_f126
