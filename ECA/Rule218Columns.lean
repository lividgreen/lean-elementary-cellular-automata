module

public import ECA.EdgeColumns
public import ECA.ReproducedPatterns
import all ECA.EdgeColumns
import all ECA.EdgeWindow

/-!
# Rule `218` reproduces exactly the nonzero one-parity patterns
([RuleSpace] §5)

A rule agreeing with rule `90` off adjacent cells reproduces every nonzero one-parity pattern.
Rule `218`, `f 0 1 1 = 1` and `f 1 1 1 = 0` beside the rule `90` bits, is such a rule, and the
question is whether it reproduces anything else. At a quiescent rule with `f 0 0 1 = 1` the window
read from the leftmost set cell of a reproduced pattern `p` is purely periodic in time at every
gap, so the window of width `diam p + 1` of the orbit of `p` is a family of purely periodic
columns obeying the window recurrence, with its first cell set and its last cell clear. The
statement that at rule `218` such a family has every odd cell clear at time `0` is stated here as a
proposition, `PeriodicColumnsOddClear218`, and proved by a column induction. From it, the odd
cells of the window of `p` are clear, so every set cell of `p` lies at an even distance from its
leftmost and `p` is of one parity.

## Main results

* `PeriodicColumnsOddClear218` — the column statement, as a proposition: a family of purely
  periodic columns obeying rule `218`'s window recurrence below a width, with its first cell set
  and its cells from `d` on clear at time `0`, has every odd cell clear at time `0`.
* `periodicColumnsOddClear218` / `periodicColumnsOddClear218_nonvacuous` /
  `not_periodicColumnsOddClear218_without_clear` — that proposition is true, its hypotheses meet
  at width `3`, and without the clear cells it fails at width `2`.
* `reproduces_iff_oneParity_f218_of` — from that proposition, rule `218` reproduces a pattern
  exactly when it is nonzero and of one parity.
* `reproduces_iff_oneParity_f218` — rule `218` reproduces a pattern exactly when it is nonzero and
  of one parity, with no hypothesis.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- **A family of purely periodic columns at rule `218` has its odd cells clear**: a family
`e n j` obeying the window recurrence of rule `218` below the width `W`, with `e 0 0 = 1`, clear
cells from `d < W` on at time `0`, and every column of period `t`, has `e 0 j = 0` at every odd
`j < W`. -/
def PeriodicColumnsOddClear218 : Prop :=
  ∀ (e : ℕ → ℕ → ZMod 2) (W d t : ℕ),
    (∀ n j, j < W → e (n + 1) j =
      f218 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) →
    e 0 0 = 1 → d < W → (∀ j, d ≤ j → j < W → e 0 j = 0) → 0 < t →
    (∀ n j, j < W → e (n + t) j = e n j) →
    ∀ j, j < W → j % 2 = 1 → e 0 j = 0

/-- Rule `218` meets the agreement with rule `90` off adjacent cells. -/
private theorem agreesOffAdjacent_f218 : AgreesOffAdjacent f218 := by
  unfold AgreesOffAdjacent f218; decide

/-- Every set cell of a nonzero state sits at the leftmost set cell plus an offset below the
diameter. -/
private theorem exists_offset {p : FiniteConfiguration} (hp : p ≠ 0) {i : ℤ} (hi : p i ≠ 0) :
    ∃ a : ℕ, a < p.diam ∧ i = p.leftEnd + a := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmem : i ∈ p.support := Finsupp.mem_support_iff.mpr hi
  have h1 : p.support.min' hne ≤ i := Finset.min'_le _ _ hmem
  have h2 : i ≤ p.support.max' hne := Finset.le_max' _ _ hmem
  rw [FiniteConfiguration.leftEnd_eq hne]
  rw [FiniteConfiguration.diam_eq' hne]
  refine ⟨(i - p.support.min' hne).toNat, by omega, by omega⟩

/-- **A family of purely periodic columns at rule `218` has its odd cells clear.** A column
induction: the first column is set at every time, no two adjacent columns are set at every time
below the width, and in the odd column after an even column that is not clear at every time, the
column is constant and so clear. -/
theorem periodicColumnsOddClear218 : PeriodicColumnsOddClear218 := by
  intro e W d t hrec he0 hdW hclear ht hper j hjW hjodd
  have hW : 0 < W := by omega
  have hcz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hr : ∀ n j, j + 2 < W → e (n + 1) (j + 2) = f218 (e n j) (e n (j + 1)) (e n (j + 2)) := by
    intro n j hj
    have := hrec n (j + 2) hj
    simpa using this
  -- a column constant from some time on is constant
  have hlift : ∀ j, j < W → ∀ (n₀ : ℕ) (c : ZMod 2), (∀ n, n₀ ≤ n → e n j = c) →
      ∀ n, e n j = c := by
    intro j hj n₀ c h n
    have hk : ∀ k, e (n + k * t) j = e n j := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.succ_mul, ← add_assoc, hper _ _ hj, ih]
    rw [← hk n₀]
    have := Nat.mul_le_mul_left n₀ ht
    exact h _ (by omega)
  -- the first column is set at every time
  have hA0 : ∀ n, e n 0 = 1 := by
    intro n
    induction n with
    | zero => exact he0
    | succ n ih =>
      have := hrec n 0 hW
      simp only [f218] at this
      simpa [ih] using this
  -- two adjacent set columns fill the window to the right
  have hfill : ∀ j, j + 2 < W → (∀ n, e n j = 1) → (∀ n, e n (j + 1) = 1) →
      ∀ n, e n (j + 2) = 1 := by
    intro j hj h1 h2
    refine hlift (j + 2) hj 1 1 fun n hn => ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hr m j hj, h1 m, h2 m]
    generalize e m (j + 2) = x
    revert x
    decide
  have hno2 : ∀ j, j + 1 < W → (∀ n, e n j = 1) → (∀ n, e n (j + 1) = 1) → False := by
    intro j hj h1 h2
    have key : ∀ k, j + k + 1 < W → (∀ n, e n (j + k) = 1) ∧ (∀ n, e n (j + k + 1) = 1) := by
      intro k
      induction k with
      | zero => intro _; exact ⟨h1, h2⟩
      | succ k ih =>
        intro hk
        obtain ⟨a, b⟩ := ih (by omega)
        exact ⟨b, hfill (j + k) (by omega) a b⟩
    obtain ⟨_, h⟩ := key (W - 2 - j) (by omega)
    have h0 := h 0
    rw [show j + (W - 2 - j) + 1 = W - 1 by omega, hclear (W - 1) (by omega) (by omega)] at h0
    exact absurd h0 (by decide)
  -- the odd column after an even column that is not always clear is clear
  have stepA : ∀ i, 2 * i + 1 < W → (∀ k, k < i → ∀ n, e n (2 * k + 1) = 0) →
      (∃ m, e m (2 * i) = 1) → ∀ n, e n (2 * i + 1) = 0 := by
    intro i hi hlow hex
    have hconst : ∀ n, e (n + 1) (2 * i + 1) = e n (2 * i + 1) := by
      intro n
      have h := hrec n (2 * i + 1) hi
      have hA : (if 2 ≤ 2 * i + 1 then e n (2 * i + 1 - 2) else 0) = 0 := by
        split_ifs with h2
        · have := hlow (i - 1) (by omega) n
          rwa [show 2 * (i - 1) + 1 = 2 * i + 1 - 2 by omega] at this
        · rfl
      rw [hA] at h
      rw [h]
      simp [f218]
    have hall : ∀ n, e n (2 * i + 1) = e 0 (2 * i + 1) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [hconst, ih]
    rcases hcz (e 0 (2 * i + 1)) with h0 | h1
    · intro n; rw [hall, h0]
    · exfalso
      have hAlw : ∀ n, e n (2 * i + 1) = 1 := fun n => by rw [hall, h1]
      by_cases hlast : 2 * i + 2 < W
      · obtain ⟨m, hm⟩ := hex
        have hstay : ∀ n, m + 1 ≤ n → e n (2 * i + 2) = 1 := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base =>
            rw [hr m (2 * i) hlast, hm, hAlw m]
            generalize e m (2 * i + 2) = x
            revert x
            decide
          | succ n hn ih =>
            rw [hr n (2 * i) hlast, hAlw n, ih]
            generalize e n (2 * i) = a
            revert a
            decide
        exact hno2 (2 * i + 1) hlast hAlw (hlift (2 * i + 2) hlast (m + 1) 1 hstay)
      · have h0 := hAlw 0
        rw [hclear (2 * i + 1) (by omega) hi] at h0
        exact absurd h0 (by decide)
  have hC : ∀ i, 2 * i < W → (∀ k, k < i → ∀ n, e n (2 * k + 1) = 0) ∧
      ∃ m, e m (2 * i) = 1 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨fun k hk => absurd hk (by omega), 0, he0⟩
    | succ i ih =>
      intro hi
      obtain ⟨hlow, m, hm⟩ := ih (by omega)
      have A := stepA i (by omega) hlow ⟨m, hm⟩
      refine ⟨fun k hk n => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
        · exact hlow k h n
        · exact A n
      · by_contra hno
        have hz : ∀ n, e n (2 * (i + 1)) = 0 := by
          intro n
          rcases hcz (e n (2 * (i + 1))) with h | h
          · exact h
          · exact absurd ⟨n, h⟩ hno
        have h2 : 2 * (i + 1) = 2 * i + 2 := by ring
        have := hr m (2 * i) (by omega)
        rw [← h2, hz, hm, A m, hz m] at this
        exact absurd this (by decide)
  obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + 1 := ⟨j / 2, by omega⟩
  obtain ⟨hlow, hex⟩ := hC i (by omega)
  exact stepA i hjW hlow hex 0

/-- **The hypotheses of the odd-cells statement meet**: at width `3`, `d = 2`, `t = 2`, the family
that is `1` in column `0`, `0` in column `1` and alternates in column `2` obeys the window
recurrence of rule `218`, with its first cell set, its cell `2` clear at time `0` and every column
of period `2`. -/
theorem periodicColumnsOddClear218_nonvacuous (e : ℕ → ℕ → ZMod 2)
    (he : ∀ n j, e n j = if j = 0 then 1 else if j = 2 then ((n % 2 : ℕ) : ZMod 2) else 0) :
    (∀ n j, j < 3 → e (n + 1) j =
      f218 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) ∧
    e 0 0 = 1 ∧ 2 < 3 ∧ (∀ j, 2 ≤ j → j < 3 → e 0 j = 0) ∧ 0 < 2 ∧
    (∀ n j, j < 3 → e (n + 2) j = e n j) := by
  refine ⟨?_, by simp [he], by decide, ?_, by decide, ?_⟩
  · intro n j hj
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
    · have h' : (n + 1) % 2 = 0 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
  · intro j h1 h2
    interval_cases j
    simp [he]
  · intro n j hj
    have h' : (n + 2) % 2 = n % 2 := by omega
    simp only [he, h']

/-- **The clear cell is needed**: at width `2` the family that is `1` everywhere obeys the window
recurrence of rule `218` below `2` and has its first cell set and every column of period `1`, yet
its odd cell `1` is set at time `0`. -/
theorem not_periodicColumnsOddClear218_without_clear (e : ℕ → ℕ → ZMod 2)
    (he : ∀ n j, e n j = 1) :
    (∀ n j, j < 2 → e (n + 1) j =
      f218 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) ∧
    e 0 0 = 1 ∧ 0 < 1 ∧ (∀ n j, j < 2 → e (n + 1) j = e n j) ∧ 1 < 2 ∧ 1 % 2 = 1 ∧
    e 0 1 ≠ 0 := by
  refine ⟨?_, he 0 0, by decide, fun n j _ => by simp only [he], by decide, by decide, ?_⟩
  · intro n j hj
    interval_cases j <;> (simp only [he]; decide)
  · rw [he]; decide

/-- **Rule `218` reproduces exactly the nonzero one-parity patterns**, from the statement that
purely periodic window columns have their odd cells clear as a hypothesis: the pattern's window of
width `diam p + 1` is such a family along the orbit, so its odd cells are clear. -/
theorem reproduces_iff_oneParity_f218_of (h : PeriodicColumnsOddClear218)
    (p : FiniteConfiguration) :
    Reproduces (finRule f218 hq218) p ↔ p ≠ 0 ∧ OneParity p := by
  constructor
  · intro hrep
    have hp : p ≠ 0 := hrep.1
    have h001 : f218 0 0 1 = 1 := by decide
    obtain ⟨t, ht, htp⟩ := leftWindowPeriodic f218 hq218 h001 p hrep 1
    have key := h (fun n j => ((finRule f218 hq218)^[n] p).leftWindow (p.diam + 1) j)
      (p.diam + 1) p.diam t
      (by
        intro n j hj
        rw [Function.iterate_succ_apply']
        exact FiniteConfiguration.leftWindow_finRule h001 (iterate_ne_zero hq218 h001 hp n) hj)
      (leftWindow_zero_ne hp (by omega)) (by omega)
      (by
        intro j hj1 hj2
        exact FiniteConfiguration.leftWindow_eq_zero_of_diam_le hp hj1 hj2)
      ht (fun n j _ => congrFun (htp n) j)
    have hev : ∀ i, p i ≠ 0 → ∃ a : ℕ, a < p.diam ∧ a % 2 = 0 ∧ i = p.leftEnd + a := by
      intro i hi
      obtain ⟨a, ha, rfl⟩ := exists_offset hp hi
      refine ⟨a, ha, ?_, rfl⟩
      by_contra hodd
      have := key a (by omega) (by omega)
      simp only [FiniteConfiguration.leftWindow, show a < p.diam + 1 by omega, ite_true,
        Function.iterate_zero, id] at this
      exact hi this
    refine ⟨hp, fun i j hi hj => ?_⟩
    obtain ⟨a, _, ha, rfl⟩ := hev i hi
    obtain ⟨b, _, hb, rfl⟩ := hev j hj
    exact ⟨((a / 2 : ℕ) : ℤ) - ((b / 2 : ℕ) : ℤ), by omega⟩
  · rintro ⟨hp, hs⟩
    exact LocalRule.AgreesOffAdjacent.reproduces_of_oneParity f218 agreesOffAdjacent_f218 hs hp

/-- **Rule `218` reproduces exactly the nonzero one-parity patterns.** -/
theorem reproduces_iff_oneParity_f218 (p : FiniteConfiguration) :
    Reproduces (finRule f218 hq218) p ↔ p ≠ 0 ∧ OneParity p :=
  reproduces_iff_oneParity_f218_of periodicColumnsOddClear218 p

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_oneParity_f218_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_oneParity_f218_of

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsOddClear218' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsOddClear218

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsOddClear218_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsOddClear218_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_periodicColumnsOddClear218_without_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_periodicColumnsOddClear218_without_clear

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_oneParity_f218' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_oneParity_f218
