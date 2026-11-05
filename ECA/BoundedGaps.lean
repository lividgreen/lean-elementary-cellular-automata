module

public import ECA.ReproductionBracket

/-!
# Bounded internal gaps exclude reproduction
([RuleSpace] §5 Proposition 5.9)

The *internal gap* of a finitely supported state of the line is a run of clear cells lying between
two set cells of the state (a term of this package, with no classical name).
`FiniteConfiguration.GapLe` bounds every internal gap by `m`, and `FiniteConfiguration.OnesLe`
bounds every run of set cells by `m`. Both hold at `m` the support diameter
(`FiniteConfiguration.gapLe_diam` and `FiniteConfiguration.onesLe_diam`).

A map along whose orbit from `p` the internal gaps stay bounded does not reproduce `p`: some
iterate would be more copies than the bound at a gap past it, and two neighbouring copies of a
nonzero pattern are separated by an internal gap of that size. This is the statement
`NotReproducesOfGapLe`, proved here as `not_reproduces_of_gapLe`.

The growing quiescent rules that the reproduction bracket does not decide are split by two
lists of Wolfram numbers: `gapClassA`, the rules whose zero-image graph has the zero loop as its
only cycle, and `gapClassB`, seven rules sending `111` to `0`. The statements `GapStepClassA` and
`GapStepClassB` say that one step of such a rule keeps the internal gaps bounded, by `max m 2` in
the first class and, together with the runs of set cells, by `max m 3` in the second.

## Main results

* `FiniteConfiguration.GapLe` / `FiniteConfiguration.OnesLe` — the two bounds.
* `gapClassA` / `gapClassB` — the two lists of rules.
* `NotReproducesOfGapLe` / `GapStepClassA` / `GapStepClassB` — the three statements that are the
  hypotheses of the main statement; all three are proved (`not_reproduces_of_gapLe`,
  `gapStepClassA`, `gapStepClassB`).
* `FiniteConfiguration.gapLe_diam` / `FiniteConfiguration.onesLe_diam` — both bounds hold at the
  support diameter.
* `not_reproduces_gapClasses` — **the main result**, unconditional: no rule of either list
  reproduces a pattern.
* `not_reproduces_of_gapStep` — the main statement from the three statements above as hypotheses:
  no rule of either list reproduces a pattern.
* `not_reproduces_of_gapLe` — the first statement proved: bounded internal gaps along an orbit
  exclude reproduction.
* `not_reproduces_of_gapStep_of_classes` — the main statement with that first hypothesis
  discharged, from `GapStepClassA` and `GapStepClassB` alone.
* `LocalRule.ThreeZerosClear` / `LocalRule.ThreeZerosClear.gapLe_finRule` — a local condition on a
  rule's zero images, and the one-step gap bound it gives.
* `gapLe_finRule_wolfram234` / `gapLe_finRule_wolfram248` — the same bound at the two rules of
  `gapClassA` outside that condition.
* `gapStepClassA` — the second statement proved, case by case over `gapClassA`.
* `not_reproduces_of_gapStepClassB` — the main statement from `GapStepClassB` alone.
* `LocalRule.FourOnesFree` / `LocalRule.FourOnesFree.onesLe_finRule` — a local condition on a
  rule's images, and the one-step bound on the runs of set cells it gives.
* `LocalRule.FourZerosConst` / `LocalRule.FourZerosConst.gapLe_finRule` — a local condition on a
  rule's zero images, and the one-step gap bound it gives from bounded gaps and runs.
* `gapLe_finRule_wolfram28` / `gapLe_finRule_wolfram70` — the same gap bound at the two rules of
  `gapClassB` outside that condition.
* `gapStepClassB` — the third statement proved, case by case over `gapClassB`.
* `LocalRule.SevenConstLift` / `LocalRule.SevenConstLift.twoStep` — a decidable local condition on
  two steps of a rule, and the bound on the internal gaps and runs of set cells after two steps
  that it gives.
* `gapClassC` / `not_reproduces_gapClassC` — the rules `62` and `118`, which meet that condition,
  reproduce no pattern.
* `FiniteConfiguration.PairFreeLe` / `FiniteConfiguration.Avoids` — a bound on the set-flanked
  stretches holding no two adjacent set cells, and the absence of a window of four cells;
  `FiniteConfiguration.PairFreeLe.gapLe` and `FiniteConfiguration.pairFreeLe_diam` — the first
  bounds the internal gaps, and the bound holds at the support diameter.
* `avoids_finRule_wolfram202` / `pairFreeLe_finRule_wolfram202` — the image of rule `202` never
  reads `0101`, and one step of it keeps the pair-free bound on a state that does not read `0101`;
  `avoids_finRule_wolfram216` / `pairFreeLe_finRule_wolfram216` — the same at the mirror rule
  `216` and the window `1010`.
* `gapClassD` / `not_reproduces_gapClassD` — the rules `202` and `216` reproduce no pattern;
  `pairFreeLe_finRule_wolfram202_nonvacuous` — the pair-free bound of one step is attained.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The two bounds -/

/-- Every run of clear cells lying between two set cells of `s` has at most `m` cells. -/
def FiniteConfiguration.GapLe (s : FiniteConfiguration) (m : ℕ) : Prop :=
  ∀ i j : ℤ, i < j → s i ≠ 0 → s j ≠ 0 → (∀ k, i < k → k < j → s k = 0) → j - i ≤ m + 1

/-- Every run of set cells of `s` has at most `m` cells. -/
def FiniteConfiguration.OnesLe (s : FiniteConfiguration) (m : ℕ) : Prop :=
  ∀ i j : ℤ, i ≤ j → (∀ k, i ≤ k → k ≤ j → s k ≠ 0) → j - i + 1 ≤ m

/-- The rules whose zero-image graph has the zero loop as its only cycle, among the growing
rules not shown to reproduce. -/
def gapClassA : List ℕ :=
  [156, 158, 178, 182, 186, 188, 190, 198, 206, 214, 220, 222, 230, 234, 238, 242, 246, 248,
    250, 252, 254]

/-- Seven rules sending `111` to `0`, among the growing rules not shown to reproduce. -/
def gapClassB : List ℕ := [28, 50, 58, 70, 78, 92, 114]

/-! ## The three statements the main statement consumes -/

/-- **Bounded internal gaps along an orbit forbid reproduction** (proved as
`not_reproduces_of_gapLe`). -/
def NotReproducesOfGapLe : Prop :=
  ∀ (U : FiniteConfiguration → FiniteConfiguration) (p : FiniteConfiguration) (B : ℕ),
    (∀ t, (U^[t] p).GapLe B) → ¬ Reproduces U p

/-- **Hypothesis: one step of a rule of `gapClassA` keeps the internal gaps at most `max m 2`.** -/
def GapStepClassA : Prop :=
  ∀ n ∈ gapClassA, ∀ (hq : wolframRule n 0 0 0 = 0) (s : FiniteConfiguration) (m : ℕ),
    s.GapLe m → (finRule (wolframRule n) hq s).GapLe (max m 2)

/-- **Hypothesis: one step of a rule of `gapClassB` keeps the internal gaps and the runs of set
cells at most `max m 3`.** -/
def GapStepClassB : Prop :=
  ∀ n ∈ gapClassB, ∀ (hq : wolframRule n 0 0 0 = 0) (s : FiniteConfiguration) (m : ℕ),
    s.GapLe m → s.OnesLe m →
      (finRule (wolframRule n) hq s).GapLe (max m 3) ∧
        (finRule (wolframRule n) hq s).OnesLe (max m 3)

/-! ## Both bounds hold at the support diameter -/

/-- Two set cells of `s` lie within the support diameter of each other. -/
private theorem span_le_diam_of_cells {s : FiniteConfiguration} {a b : ℤ} (ha : s a ≠ 0)
    (hb : s b ≠ 0) : (b - a).toNat + 1 ≤ diam s := by
  have hne : s.support.Nonempty := ⟨a, Finsupp.mem_support_iff.mpr ha⟩
  have h1 := Finset.min'_le s.support a (Finsupp.mem_support_iff.mpr ha)
  have h2 := Finset.le_max' s.support b (Finsupp.mem_support_iff.mpr hb)
  unfold diam
  rw [dite_eq_left hne]
  omega

/-- A bound on the internal gaps weakens. -/
private theorem FiniteConfiguration.GapLe.mono {s : FiniteConfiguration} {m m' : ℕ}
    (h : s.GapLe m) (hm : m ≤ m') : s.GapLe m' :=
  fun i j hij hi hj hk => by have := h i j hij hi hj hk; omega

/-- A bound on the runs of set cells weakens. -/
private theorem FiniteConfiguration.OnesLe.mono {s : FiniteConfiguration} {m m' : ℕ}
    (h : s.OnesLe m) (hm : m ≤ m') : s.OnesLe m' :=
  fun i j hij hk => by have := h i j hij hk; omega

/-- **Every internal gap of a state is shorter than its support diameter.** -/
theorem FiniteConfiguration.gapLe_diam (s : FiniteConfiguration) : s.GapLe (diam s) := by
  intro i j hij hi hj _
  have := span_le_diam_of_cells hi hj
  omega

/-- **Every run of set cells of a state is at most its support diameter.** -/
theorem FiniteConfiguration.onesLe_diam (s : FiniteConfiguration) : s.OnesLe (diam s) := by
  intro i j hij hk
  have := span_le_diam_of_cells (hk i le_rfl hij) (hk j hij le_rfl)
  omega

/-! ## The main statement -/

/-- **Bounded internal gaps exclude reproduction at the rules of both lists**: from the three
hypotheses, no rule of `gapClassA` or `gapClassB` reproduces any pattern. The internal gaps along
the orbit of `p` stay at most `max (diam p) 2` at the first class and, with the runs of set cells,
at most `max (diam p) 3` at the second, by induction on the time from
`FiniteConfiguration.gapLe_diam` and `FiniteConfiguration.onesLe_diam`. -/
theorem not_reproduces_of_gapStep (h1 : NotReproducesOfGapLe) (h2 : GapStepClassA)
    (h3 : GapStepClassB) :
    ∀ n ∈ gapClassA ++ gapClassB, ∀ (hq : wolframRule n 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule n) hq) p := by
  intro n hn hq p
  rcases List.mem_append.mp hn with hA | hB
  · refine h1 _ p (max (diam p) 2) fun t => ?_
    induction t with
    | zero => exact (gapLe_diam p).mono (le_max_left _ _)
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      have := h2 n hA hq _ _ ih
      rwa [max_assoc, max_self] at this
  · refine h1 _ p (max (diam p) 3) fun t => ?_
    have key : ∀ t, (((finRule (wolframRule n) hq)^[t] p).GapLe (max (diam p) 3)) ∧
        (((finRule (wolframRule n) hq)^[t] p).OnesLe (max (diam p) 3)) := by
      intro t
      induction t with
      | zero =>
        exact ⟨(gapLe_diam p).mono (le_max_left _ _), (onesLe_diam p).mono (le_max_left _ _)⟩
      | succ t ih =>
        rw [Function.iterate_succ_apply']
        have := h3 n hB hq _ _ ih.1 ih.2
        rwa [max_assoc, max_self] at this
    exact (key t).1

/-! ## Bounded internal gaps exclude reproduction -/

private theorem translate_apply_gap (i : ℤ) (p : FiniteConfiguration) (x : ℤ) :
    translate i p x = p (x - i) := by
  have h := Finsupp.mapDomain_apply_of_injective (add_left_injective i) p (x - i)
  rw [sub_add_cancel] at h
  exact h

/-- A nonzero state has a least and a greatest set cell, and its diameter is their distance plus
one. -/
private theorem exists_ends_gap {p : FiniteConfiguration} (hp : p ≠ 0) :
    ∃ a b : ℤ, p a ≠ 0 ∧ p b ≠ 0 ∧ (∀ y, y < a → p y = 0) ∧ (∀ y, b < y → p y = 0) ∧
      (diam p : ℤ) = b - a + 1 := by
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmM := Finset.min'_le_max' p.support hpne
  refine ⟨p.support.min' hpne, p.support.max' hpne,
    Finsupp.mem_support_iff.mp (Finset.min'_mem _ _),
    Finsupp.mem_support_iff.mp (Finset.max'_mem _ _), fun y hy => ?_, fun y hy => ?_, ?_⟩
  · by_contra hne
    have := Finset.min'_le p.support y (Finsupp.mem_support_iff.mpr hne)
    omega
  · by_contra hne
    have := Finset.le_max' p.support y (Finsupp.mem_support_iff.mpr hne)
    omega
  · unfold diam
    rw [dite_eq_left hpne]
    have : (0 : ℤ) ≤ p.support.max' hpne - p.support.min' hpne := by omega
    omega

/-- The offsets of copies are ordered, a diameter apart. -/
private theorem offsets_ordered_gap {c : ℕ → ℤ} {k d G : ℕ}
    (hc : ∀ j, j + 1 < k → c j + d + G ≤ c (j + 1)) :
    ∀ i j, i < j → j < k → c i + d ≤ c j := by
  intro i j hij
  induction j with
  | zero => omega
  | succ j ih =>
    intro hj
    have h1 := hc j hj
    rcases Nat.lt_or_ge i j with h | h
    · have := ih h (by omega)
      omega
    · have : i = j := by omega
      subst this
      omega

/-- **Bounded internal gaps along an orbit exclude reproduction**: two neighbouring copies of a
nonzero pattern at gap `B + 1` are separated by an internal gap longer than `B`. -/
theorem not_reproduces_of_gapLe : NotReproducesOfGapLe := by
  intro U p B hB hrep
  obtain ⟨hp, hr⟩ := hrep
  obtain ⟨t, k, hk, c, hc, hs⟩ := hr 2 (B + 1)
  obtain ⟨a, b, ha, hb, hlow, hhigh, hdiam⟩ := exists_ends_gap hp
  have hab : a ≤ b := by
    by_contra h
    exact hb (hlow b (by omega))
  have hord := offsets_ordered_gap hc
  have hev : ∀ x, (U^[t] p) x = (Finset.range k).sum fun j => p (x - c j) := by
    intro x
    rw [hs, Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun j _ => translate_apply_gap _ _ _
  have hc01 : c 0 + diam p + (B + 1) ≤ c 1 := hc 0 (by omega)
  have hs0 : (U^[t] p) (b + c 0) ≠ 0 := by
    rw [hev, Finset.sum_eq_single 0]
    · simpa using hb
    · intro j hj hj0
      apply hlow
      have := hord 0 j (by omega) (by simp at hj; omega)
      omega
    · intro h0; simp at h0; omega
  have hs1 : (U^[t] p) (a + c 1) ≠ 0 := by
    rw [hev, Finset.sum_eq_single 1]
    · simpa using ha
    · intro j hj hj1
      rcases Nat.lt_or_ge j 1 with h | h
      · have : j = 0 := by omega
        subst this
        apply hhigh
        omega
      · apply hlow
        have := hord 1 j (by omega) (by simp at hj; omega)
        omega
    · intro h0; simp at h0; omega
  have hgap := hB t (b + c 0) (a + c 1) (by omega) hs0 hs1 (fun x hx0 hx1 => by
    rw [hev]
    refine Finset.sum_eq_zero fun j hj => ?_
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this
      exact hhigh _ (by omega)
    · apply hlow
      rcases Nat.eq_or_lt_of_le h with h1 | h1
      · subst h1; omega
      · have := hord 1 j h1 (by simp at hj; omega)
        omega)
  omega

/-- **The two lists of rules reproduce no pattern, with the first statement proved**: the main
statement with `NotReproducesOfGapLe` discharged by `not_reproduces_of_gapLe`. -/
theorem not_reproduces_of_gapStep_of_classes (h2 : GapStepClassA) (h3 : GapStepClassB) :
    ∀ n ∈ gapClassA ++ gapClassB, ∀ (hq : wolframRule n 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule n) hq) p :=
  not_reproduces_of_gapStep not_reproduces_of_gapLe h2 h3

/-! ## One step of a rule of the first class -/

/-- **Three consecutive triples sent to `0` force the middle three cells of the word clear**: the
rule's zero-image graph, whose vertices are the pairs of cells, has no path of three edges
through a set cell other than the zero loop. -/
def LocalRule.ThreeZerosClear (f : LocalRule) : Prop :=
  ∀ a b c d e : ZMod 2, f a b c = 0 → f b c d = 0 → f c d e = 0 → b = 0 ∧ c = 0 ∧ d = 0

instance (f : LocalRule) : Decidable (LocalRule.ThreeZerosClear f) := by
  unfold LocalRule.ThreeZerosClear; infer_instance

/-- At a quiescent rule, a set cell of the image has a set cell of the state among the three cells
feeding it. -/
private theorem exists_set_of_finRule_ne {f : LocalRule} (hq : f 0 0 0 = 0)
    (s : FiniteConfiguration) {x : ℤ} (hx : finRule f hq s x ≠ 0) :
    s (x - 1) ≠ 0 ∨ s x ≠ 0 ∨ s (x + 1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hx
  rw [finRule_apply, hcon.1, hcon.2.1, hcon.2.2]
  exact hq

/-- **One step of a rule with `ThreeZerosClear` keeps every internal gap at most `max m 2`**:
every window of three clear cells of the image between two set cells has its five feeding cells
of the state around it, whose middle three are clear. -/
theorem LocalRule.ThreeZerosClear.gapLe_finRule {f : LocalRule} (h : f.ThreeZerosClear)
    (hq : f 0 0 0 = 0) (s : FiniteConfiguration) (m : ℕ) (hs : s.GapLe m) :
    (finRule f hq s).GapLe (max m 2) := by
  intro i j hij hi hj hk
  have hm := le_max_left m 2
  have hm2 := le_max_right m 2
  by_cases hsm : j - i ≤ 3
  · omega
  have hw : ∀ k, i + 2 ≤ k → k + 2 ≤ j → s (k - 1) = 0 ∧ s k = 0 ∧ s (k + 1) = 0 := by
    intro k hk1 hk2
    have e1 := hk (k - 1) (by omega) (by omega)
    have e2 := hk k (by omega) (by omega)
    have e3 := hk (k + 1) (by omega) (by omega)
    rw [finRule_apply] at e1 e2 e3
    rw [show k - 1 + 1 = k by ring] at e1
    rw [show k + 1 - 1 = k by ring] at e3
    exact h _ _ _ _ _ e1 e2 e3
  have hclear : ∀ x, i < x → x < j → s x = 0 := by
    intro x h1 h2
    by_cases hx1 : x = i + 1
    · have := (hw (i + 2) (by omega) (by omega)).1
      rwa [show i + 2 - 1 = x by omega] at this
    by_cases hx2 : x = j - 1
    · have := (hw (j - 2) (by omega) (by omega)).2.2
      rwa [show j - 2 + 1 = x by omega] at this
    exact (hw x (by omega) (by omega)).2.1
  obtain ⟨p, hp1, hp2, hp3⟩ : ∃ p, p ≤ i ∧ s p ≠ 0 ∧ ∀ x, p < x → x < j → s x = 0 := by
    by_cases hsi : s i = 0
    · have hi' := exists_set_of_finRule_ne hq s hi
      rw [hsi, hclear (i + 1) (by omega) (by omega)] at hi'
      refine ⟨i - 1, by omega, by tauto, fun x hx1 hx2 => ?_⟩
      by_cases hxi : x = i
      · rwa [hxi]
      · exact hclear x (by omega) hx2
    · exact ⟨i, le_rfl, hsi, fun x hx1 hx2 => hclear x hx1 hx2⟩
  obtain ⟨q, hq1, hq2, hq3⟩ : ∃ q, j ≤ q ∧ s q ≠ 0 ∧ ∀ x, i < x → x < q → s x = 0 := by
    by_cases hsj : s j = 0
    · have hj' := exists_set_of_finRule_ne hq s hj
      rw [hsj, hclear (j - 1) (by omega) (by omega)] at hj'
      refine ⟨j + 1, by omega, by tauto, fun x hx1 hx2 => ?_⟩
      by_cases hxj : x = j
      · rwa [hxj]
      · exact hclear x hx1 (by omega)
    · exact ⟨j, le_rfl, hsj, fun x hx1 hx2 => hclear x hx1 hx2⟩
  have := hs p q (by omega) hp2 hq2 fun x hx1 hx2 => by
    by_cases hxj : x < j
    · exact hp3 x hx1 hxj
    · exact hq3 x (by omega) hx2
  omega

/-- **Joint satisfiability**: rule `254` is quiescent and meets `ThreeZerosClear`, and the state of
two set cells at distance three has internal gap bound `2`. -/
theorem LocalRule.ThreeZerosClear.gapLe_finRule_nonvacuous :
    (wolframRule 254).ThreeZerosClear ∧ wolframRule 254 0 0 0 = 0 ∧
      (Finsupp.single 0 1 + Finsupp.single 3 1 : FiniteConfiguration).GapLe 2 := by
  have key : ∀ k : ℤ, (Finsupp.single 0 1 + Finsupp.single 3 1 : FiniteConfiguration) k ≠ 0 →
      k = 0 ∨ k = 3 := by
    intro k hk
    by_contra hc
    push Not at hc
    apply hk
    simp [Ne.symm hc.1, Ne.symm hc.2]
  refine ⟨by decide, by decide, ?_⟩
  intro i j hij hi hj _
  rcases key i hi with rfl | rfl <;> rcases key j hj with rfl | rfl <;> omega

/-- Rule `234` sends to `0` exactly the triples `000`, `100` and `010`. -/
private theorem wolfram234_zero (a b c : ZMod 2) (h : wolframRule 234 a b c = 0) :
    c = 0 ∧ (a = 0 ∨ b = 0) := by
  revert a b c; decide

/-- Rule `234` sends every triple other than `000`, `100` and `010` to `1`. -/
private theorem wolfram234_ne (a b c : ZMod 2) (h : wolframRule 234 a b c ≠ 0) :
    c ≠ 0 ∨ (a ≠ 0 ∧ b ≠ 0) := by
  revert a b c; decide

/-- **One step of rule `234` keeps every internal gap at most `max m 2`**: a clear run of the image
between two set cells ends, on the right, one cell before a set cell of the state, and begins, on
the left, at most one cell after one. -/
theorem gapLe_finRule_wolfram234 (hq : wolframRule 234 0 0 0 = 0) (s : FiniteConfiguration)
    (m : ℕ) (hs : s.GapLe m) : (finRule (wolframRule 234) hq s).GapLe (max m 2) := by
  intro i j hij hi hj hk
  have hm := le_max_left m 2
  have hm2 := le_max_right m 2
  by_cases hsm : j - i ≤ 3
  · omega
  have hr : ∀ x, i + 2 ≤ x → x ≤ j → s x = 0 := by
    intro x h1 h2
    have e := hk (x - 1) (by omega) (by omega)
    rw [finRule_apply, show x - 1 + 1 = x by ring] at e
    exact (wolfram234_zero _ _ _ e).1
  have hq2 : s (j + 1) ≠ 0 := by
    have hj' := wolfram234_ne _ _ _ (by rw [finRule_apply] at hj; exact hj)
    rw [hr j (by omega) le_rfl] at hj'
    tauto
  by_cases hs1 : s (i + 1) = 0
  · have hi' := wolfram234_ne _ _ _ (by rw [finRule_apply] at hi; exact hi)
    have hsi : s i ≠ 0 := by
      rcases hi' with h' | h'
      · exact absurd hs1 h'
      · exact h'.2
    have := hs i (j + 1) (by omega) hsi hq2 fun x hx1 hx2 => by
      by_cases hxi : x = i + 1
      · rwa [hxi]
      · exact hr x (by omega) (by omega)
    omega
  · have := hs (i + 1) (j + 1) (by omega) hs1 hq2 fun x hx1 hx2 => hr x (by omega) (by omega)
    omega

/-- Rule `248` sends to `0` exactly the triples `000`, `001` and `010`. -/
private theorem wolfram248_zero (a b c : ZMod 2) (h : wolframRule 248 a b c = 0) :
    a = 0 ∧ (b = 0 ∨ c = 0) := by
  revert a b c; decide

/-- Rule `248` sends every triple other than `000`, `001` and `010` to `1`. -/
private theorem wolfram248_ne (a b c : ZMod 2) (h : wolframRule 248 a b c ≠ 0) :
    a ≠ 0 ∨ (b ≠ 0 ∧ c ≠ 0) := by
  revert a b c; decide

/-- **One step of rule `248` keeps every internal gap at most `max m 2`**: the mirror image of rule
`234`. -/
theorem gapLe_finRule_wolfram248 (hq : wolframRule 248 0 0 0 = 0) (s : FiniteConfiguration)
    (m : ℕ) (hs : s.GapLe m) : (finRule (wolframRule 248) hq s).GapLe (max m 2) := by
  intro i j hij hi hj hk
  have hm := le_max_left m 2
  have hm2 := le_max_right m 2
  by_cases hsm : j - i ≤ 3
  · omega
  have hl : ∀ x, i ≤ x → x + 2 ≤ j → s x = 0 := by
    intro x h1 h2
    have e := hk (x + 1) (by omega) (by omega)
    rw [finRule_apply, show x + 1 - 1 = x by ring] at e
    exact (wolfram248_zero _ _ _ e).1
  have hp2 : s (i - 1) ≠ 0 := by
    have hi' := wolfram248_ne _ _ _ (by rw [finRule_apply] at hi; exact hi)
    rw [hl i le_rfl (by omega)] at hi'
    tauto
  by_cases hs1 : s (j - 1) = 0
  · have hj' := wolfram248_ne _ _ _ (by rw [finRule_apply] at hj; exact hj)
    have hsj : s j ≠ 0 := by
      rcases hj' with h' | h'
      · exact absurd hs1 h'
      · exact h'.1
    have := hs (i - 1) j (by omega) hp2 hsj fun x hx1 hx2 => by
      by_cases hxj : x = j - 1
      · rwa [hxj]
      · exact hl x (by omega) (by omega)
    omega
  · have := hs (i - 1) (j - 1) (by omega) hp2 hs1 fun x hx1 hx2 => hl x (by omega) (by omega)
    omega

/-- **One step of each rule of `gapClassA` keeps every internal gap at most `max m 2`**: the
statement `GapStepClassA`, from `LocalRule.ThreeZerosClear.gapLe_finRule` at nineteen rules and
from `gapLe_finRule_wolfram234` and `gapLe_finRule_wolfram248` at the other two. -/
theorem gapStepClassA : GapStepClassA := by
  intro n hn hq s m hs
  have key : ∀ n ∈ gapClassA, n ≠ 234 → n ≠ 248 → (wolframRule n).ThreeZerosClear := by
    decide
  by_cases h234 : n = 234
  · subst h234
    exact gapLe_finRule_wolfram234 hq s m hs
  by_cases h248 : n = 248
  · subst h248
    exact gapLe_finRule_wolfram248 hq s m hs
  exact (key n hn h234 h248).gapLe_finRule hq s m hs

/-- **The two lists of rules reproduce no pattern, with only the second class's step bound
assumed**: the main statement with `GapStepClassA` discharged by `gapStepClassA`. -/
theorem not_reproduces_of_gapStepClassB (h3 : GapStepClassB) :
    ∀ n ∈ gapClassA ++ gapClassB, ∀ (hq : wolframRule n 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule n) hq) p :=
  not_reproduces_of_gapStep_of_classes gapStepClassA h3

/-! ## One step of a rule of the second class -/

/-- Induction on the integers from a starting point. -/
private theorem induction_from_int {P : ℤ → Prop} (a : ℤ) (base : P a)
    (step : ∀ x, a ≤ x → P x → P (x + 1)) : ∀ x, a ≤ x → P x := by
  intro x hx
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = a + n := ⟨(x - a).toNat, by omega⟩
  induction n with
  | zero => simpa using base
  | succ n ih =>
    have := step _ (by omega) (ih (by omega))
    rwa [show a + (n : ℤ) + 1 = a + ((n + 1 : ℕ) : ℤ) by push_cast; ring] at this

/-- **No four consecutive triples are sent to `1`**: a rule with this property sends no window of
four consecutive cells of a word to a run of four set cells. -/
def LocalRule.FourOnesFree (f : LocalRule) : Prop :=
  ∀ a b c d e g : ZMod 2, ¬ (f a b c ≠ 0 ∧ f b c d ≠ 0 ∧ f c d e ≠ 0 ∧ f d e g ≠ 0)

instance (f : LocalRule) : Decidable (LocalRule.FourOnesFree f) := by
  unfold LocalRule.FourOnesFree; infer_instance

/-- **Four consecutive triples sent to `0` force the middle four cells of the word equal**: the
rule's zero-image graph, whose vertices are the pairs of cells, has no path of four edges that
changes a cell. -/
def LocalRule.FourZerosConst (f : LocalRule) : Prop :=
  ∀ a b c d e g : ZMod 2, f a b c = 0 → f b c d = 0 → f c d e = 0 → f d e g = 0 →
    b = c ∧ c = d ∧ d = e

instance (f : LocalRule) : Decidable (LocalRule.FourZerosConst f) := by
  unfold LocalRule.FourZerosConst; infer_instance

/-- **One step of a rule with `FourOnesFree` keeps every run of set cells at most `3`**: four
consecutive set cells of the image are four consecutive triples of the state sent to `1`. -/
theorem LocalRule.FourOnesFree.onesLe_finRule {f : LocalRule} (h : f.FourOnesFree)
    (hq : f 0 0 0 = 0) (s : FiniteConfiguration) : (finRule f hq s).OnesLe 3 := by
  intro i j hij hk
  by_contra hc
  have e0 := hk i le_rfl hij
  have e1 := hk (i + 1) (by omega) (by omega)
  have e2 := hk (i + 2) (by omega) (by omega)
  have e3 := hk (i + 3) (by omega) (by omega)
  rw [finRule_apply] at e0 e1 e2 e3
  rw [show i + 1 - 1 = i by ring, show i + 1 + 1 = i + 2 by ring] at e1
  rw [show i + 2 - 1 = i + 1 by ring, show i + 2 + 1 = i + 3 by ring] at e2
  rw [show i + 3 - 1 = i + 2 by ring, show i + 3 + 1 = i + 4 by ring] at e3
  exact h _ _ _ _ _ _ ⟨e0, e1, e2, e3⟩

/-- **One step of a rule with `FourZerosConst` keeps every internal gap at most `max m 3`**, given
the runs of set cells at most `m` as well: a clear run of the image longer than four cells makes
the state constant between its ends, clear — and then set cells of the state just outside bound the
gap — or set — and then those cells are a run. -/
theorem LocalRule.FourZerosConst.gapLe_finRule {f : LocalRule} (h : f.FourZerosConst)
    (hq : f 0 0 0 = 0) (s : FiniteConfiguration) (m : ℕ) (hs : s.GapLe m) (ho : s.OnesLe m) :
    (finRule f hq s).GapLe (max m 3) := by
  intro i j hij hi hj hk
  have hm := le_max_left m 3
  have hm2 := le_max_right m 3
  by_cases hsm : j - i ≤ 4
  · omega
  have hw : ∀ x, i + 1 ≤ x → x + 3 ≤ j - 1 →
      s x = s (x + 1) ∧ s (x + 1) = s (x + 2) ∧ s (x + 2) = s (x + 3) := by
    intro x h1 h2
    have c0 := hk x (by omega) (by omega)
    have c1 := hk (x + 1) (by omega) (by omega)
    have c2 := hk (x + 2) (by omega) (by omega)
    have c3 := hk (x + 3) (by omega) (by omega)
    rw [finRule_apply] at c0 c1 c2 c3
    rw [show x + 1 - 1 = x by ring, show x + 1 + 1 = x + 2 by ring] at c1
    rw [show x + 2 - 1 = x + 1 by ring, show x + 2 + 1 = x + 3 by ring] at c2
    rw [show x + 3 - 1 = x + 2 by ring, show x + 3 + 1 = x + 4 by ring] at c3
    exact h _ _ _ _ _ _ c0 c1 c2 c3
  have hstep : ∀ x, i + 1 ≤ x → x + 1 ≤ j - 1 → s x = s (x + 1) := by
    intro x h1 h2
    by_cases hx : x + 3 ≤ j - 1
    · exact (hw x h1 hx).1
    · obtain ⟨a, b, c⟩ := hw (j - 4) (by omega) (by omega)
      rw [show j - 4 + 1 = j - 3 by ring] at a b
      rw [show j - 4 + 2 = j - 2 by ring] at b c
      rw [show j - 4 + 3 = j - 1 by ring] at c
      rcases (by omega : x = j - 3 ∨ x = j - 2) with hx3 | hx3
      · subst hx3
        rw [show j - 3 + 1 = j - 2 by ring]
        exact b
      · subst hx3
        rw [show j - 2 + 1 = j - 1 by ring]
        exact c
  have hconst : ∀ x, i + 1 ≤ x → x ≤ j - 1 → s x = s (i + 1) := by
    refine fun x h1 => induction_from_int (P := fun x => x ≤ j - 1 → s x = s (i + 1)) (i + 1)
      (fun _ => rfl) (fun x hx ih h2 => ?_) x h1
    exact (hstep x hx (by omega)).symm.trans (ih (by omega))
  by_cases hc : s (i + 1) = 0
  · have hclear : ∀ x, i < x → x < j → s x = 0 := fun x h1 h2 =>
      (hconst x (by omega) (by omega)).trans hc
    obtain ⟨p, hp1, hp2, hp3⟩ : ∃ p, p ≤ i ∧ s p ≠ 0 ∧ ∀ x, p < x → x < j → s x = 0 := by
      by_cases hsi : s i = 0
      · have hi' := exists_set_of_finRule_ne hq s hi
        rw [hsi, hclear (i + 1) (by omega) (by omega)] at hi'
        refine ⟨i - 1, by omega, by tauto, fun x hx1 hx2 => ?_⟩
        by_cases hxi : x = i
        · rwa [hxi]
        · exact hclear x (by omega) hx2
      · exact ⟨i, le_rfl, hsi, fun x hx1 hx2 => hclear x hx1 hx2⟩
    obtain ⟨q, hq1, hq2, hq3⟩ : ∃ q, j ≤ q ∧ s q ≠ 0 ∧ ∀ x, i < x → x < q → s x = 0 := by
      by_cases hsj : s j = 0
      · have hj' := exists_set_of_finRule_ne hq s hj
        rw [hsj, hclear (j - 1) (by omega) (by omega)] at hj'
        refine ⟨j + 1, by omega, by tauto, fun x hx1 hx2 => ?_⟩
        by_cases hxj : x = j
        · rwa [hxj]
        · exact hclear x hx1 (by omega)
      · exact ⟨j, le_rfl, hsj, fun x hx1 hx2 => hclear x hx1 hx2⟩
    have := hs p q (by omega) hp2 hq2 fun x hx1 hx2 => by
      by_cases hxj : x < j
      · exact hp3 x hx1 hxj
      · exact hq3 x (by omega) hx2
    omega
  · have := ho (i + 1) (j - 1) (by omega) fun k hk1 hk2 => by
      rw [hconst k hk1 hk2]
      exact hc
    omega

/-- **Joint satisfiability**: rule `50` is quiescent and meets `FourZerosConst`, and the state of
two set cells at distance four has internal gaps and runs of set cells bounded by `3`. -/
theorem LocalRule.FourZerosConst.gapLe_finRule_nonvacuous :
    (wolframRule 50).FourZerosConst ∧ wolframRule 50 0 0 0 = 0 ∧
      (Finsupp.single 0 1 + Finsupp.single 4 1 : FiniteConfiguration).GapLe 3 ∧
      (Finsupp.single 0 1 + Finsupp.single 4 1 : FiniteConfiguration).OnesLe 3 := by
  have key : ∀ k : ℤ, (Finsupp.single 0 1 + Finsupp.single 4 1 : FiniteConfiguration) k ≠ 0 →
      k = 0 ∨ k = 4 := by
    intro k hk
    by_contra hc
    push Not at hc
    apply hk
    simp [Ne.symm hc.1, Ne.symm hc.2]
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro i j hij hi hj _
    rcases key i hi with rfl | rfl <;> rcases key j hj with rfl | rfl <;> omega
  · intro i j hij hk
    by_contra hc
    have h1 := key (i + 1) (hk (i + 1) (by omega) (by omega))
    rcases key i (hk i le_rfl hij) with rfl | rfl <;> rcases key j (hk j hij le_rfl) with rfl | rfl
      <;> omega

/-- Rule `28` sends to `0` exactly the triples `000`, `001`, `101`, `110` and `111`. -/
private theorem wolfram28_zero (a b c : ZMod 2) (h : wolframRule 28 a b c = 0) :
    (a ≠ 0 ∨ b = 0) ∧ (a ≠ 0 → b = 0 → c ≠ 0) := by
  revert a b c; decide

/-- Rule `28` sends every triple other than those to `1`. -/
private theorem wolfram28_ne (a b c : ZMod 2) (h : wolframRule 28 a b c ≠ 0) :
    (a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0 ∧ c = 0) := by
  revert a b c; decide

/-- **One step of rule `28` keeps every internal gap at most `max m 3`**, given the runs of set
cells at most `m` as well: read as a walk on pairs of cells, a clear run of the image has the loops
at `00` and `11` and a dead end at `01`, so the state is constant over the run apart from its last
two cells. -/
theorem gapLe_finRule_wolfram28 (hq : wolframRule 28 0 0 0 = 0) (s : FiniteConfiguration)
    (m : ℕ) (hs : s.GapLe m) (ho : s.OnesLe m) :
    (finRule (wolframRule 28) hq s).GapLe (max m 3) := by
  intro i j hij hi hj hk
  have hm := le_max_left m 3
  have hm2 := le_max_right m 3
  by_cases hsm : j - i ≤ 4
  · omega
  have hz : ∀ x, i < x → x < j → wolframRule 28 (s (x - 1)) (s x) (s (x + 1)) = 0 :=
    fun x h1 h2 => by
      have := hk x h1 h2
      rwa [finRule_apply] at this
  have z1 : ∀ x, i < x → x < j → (s (x - 1) ≠ 0 ∨ s x = 0) := fun x h1 h2 =>
    (wolfram28_zero _ _ _ (hz x h1 h2)).1
  have z2 : ∀ x, i < x → x < j → s (x - 1) ≠ 0 → s x = 0 → s (x + 1) ≠ 0 := fun x h1 h2 =>
    (wolfram28_zero _ _ _ (hz x h1 h2)).2
  by_cases hsi : s i = 0
  · have hclear : ∀ x, i ≤ x → x ≤ j - 1 → s x = 0 := by
      refine fun x h1 => induction_from_int (P := fun x => x ≤ j - 1 → s x = 0) i
        (fun _ => hsi) (fun x hx ih h2 => ?_) x h1
      rcases z1 (x + 1) (by omega) (by omega) with h' | h'
      · rw [add_sub_cancel_right, ih (by omega)] at h'
        exact absurd rfl h'
      · exact h'
    have hp : s (i - 1) ≠ 0 := by
      rcases wolfram28_ne _ _ _ (by rw [finRule_apply] at hi; exact hi) with h' | h'
      · exact absurd hsi h'.2
      · exact h'.1
    have hq2 : s j ≠ 0 := by
      rcases wolfram28_ne _ _ _ (by rw [finRule_apply] at hj; exact hj) with h' | h'
      · exact h'.2
      · exact absurd (hclear (j - 1) (by omega) le_rfl) h'.1
    have := hs (i - 1) j (by omega) hp hq2 fun x hx1 hx2 => hclear x (by omega) (by omega)
    omega
  · have hones : ∀ x, i ≤ x → x ≤ j - 2 → s x ≠ 0 := by
      refine fun x h1 => induction_from_int (P := fun x => x ≤ j - 2 → s x ≠ 0) i
        (fun _ => hsi) (fun x hx ih h2 h0 => ?_) x h1
      have h3 := z2 (x + 1) (by omega) (by omega)
        (by rw [add_sub_cancel_right]; exact ih (by omega)) h0
      rcases z1 (x + 2) (by omega) (by omega) with h' | h'
      · rw [show x + 2 - 1 = x + 1 by ring] at h'
        exact h' h0
      · rw [show x + 1 + 1 = x + 2 by ring] at h3
        exact h3 h'
    have := ho i (j - 2) (by omega) fun k hk1 hk2 => hones k hk1 hk2
    omega

/-- Rule `70` sends to `0` exactly the triples `000`, `011`, `100`, `101` and `111`. -/
private theorem wolfram70_zero (a b c : ZMod 2) (h : wolframRule 70 a b c = 0) :
    (c ≠ 0 ∨ b = 0) ∧ (c ≠ 0 → b = 0 → a ≠ 0) := by
  revert a b c; decide

/-- Rule `70` sends every triple other than those to `1`. -/
private theorem wolfram70_ne (a b c : ZMod 2) (h : wolframRule 70 a b c ≠ 0) :
    (c = 0 ∧ b ≠ 0) ∨ (c ≠ 0 ∧ b = 0 ∧ a = 0) := by
  revert a b c; decide

/-- **One step of rule `70` keeps every internal gap at most `max m 3`**, given the runs of set
cells at most `m` as well: the mirror image of rule `28`. -/
theorem gapLe_finRule_wolfram70 (hq : wolframRule 70 0 0 0 = 0) (s : FiniteConfiguration)
    (m : ℕ) (hs : s.GapLe m) (ho : s.OnesLe m) :
    (finRule (wolframRule 70) hq s).GapLe (max m 3) := by
  intro i j hij hi hj hk
  have hm := le_max_left m 3
  have hm2 := le_max_right m 3
  by_cases hsm : j - i ≤ 4
  · omega
  have hz : ∀ x, i < x → x < j → wolframRule 70 (s (x - 1)) (s x) (s (x + 1)) = 0 :=
    fun x h1 h2 => by
      have := hk x h1 h2
      rwa [finRule_apply] at this
  have z1 : ∀ x, i < x → x < j → (s (x + 1) ≠ 0 ∨ s x = 0) := fun x h1 h2 =>
    (wolfram70_zero _ _ _ (hz x h1 h2)).1
  have z2 : ∀ x, i < x → x < j → s (x + 1) ≠ 0 → s x = 0 → s (x - 1) ≠ 0 := fun x h1 h2 =>
    (wolfram70_zero _ _ _ (hz x h1 h2)).2
  by_cases hsj : s j = 0
  · have hclear : ∀ d : ℤ, 0 ≤ d → d ≤ j - i - 1 → s (j - d) = 0 := by
      refine fun d h1 => induction_from_int (P := fun d => d ≤ j - i - 1 → s (j - d) = 0) 0
        (fun _ => by simpa using hsj) (fun d hd ih h2 => ?_) d h1
      rcases z1 (j - (d + 1)) (by omega) (by omega) with h' | h'
      · rw [show j - (d + 1) + 1 = j - d by ring, ih (by omega)] at h'
        exact absurd rfl h'
      · exact h'
    have hq2 : s (j + 1) ≠ 0 := by
      rcases wolfram70_ne _ _ _ (by rw [finRule_apply] at hj; exact hj) with h' | h'
      · exact absurd hsj h'.2
      · exact h'.1
    have hp : s i ≠ 0 := by
      rcases wolfram70_ne _ _ _ (by rw [finRule_apply] at hi; exact hi) with h' | h'
      · exact h'.2
      · have := hclear (j - (i + 1)) (by omega) (by omega)
        rw [show j - (j - (i + 1)) = i + 1 by ring] at this
        exact absurd this h'.1
    have := hs i (j + 1) (by omega) hp hq2 fun x hx1 hx2 => by
      have := hclear (j - x) (by omega) (by omega)
      rwa [show j - (j - x) = x by ring] at this
    omega
  · have hones : ∀ d : ℤ, 0 ≤ d → d ≤ j - i - 2 → s (j - d) ≠ 0 := by
      refine fun d h1 => induction_from_int (P := fun d => d ≤ j - i - 2 → s (j - d) ≠ 0) 0
        (fun _ => by simpa using hsj) (fun d hd ih h2 h0 => ?_) d h1
      have h3 := z2 (j - (d + 1)) (by omega) (by omega)
        (by rw [show j - (d + 1) + 1 = j - d by ring]; exact ih (by omega)) h0
      rcases z1 (j - (d + 1) - 1) (by omega) (by omega) with h' | h'
      · rw [show j - (d + 1) - 1 + 1 = j - (d + 1) by ring] at h'
        exact h' h0
      · exact h3 h'
    have := ho (i + 2) j (by omega) fun k hk1 hk2 => by
      have := hones (j - k) (by omega) (by omega)
      rwa [show j - (j - k) = k by ring] at this
    omega

/-- **One step of each rule of `gapClassB` keeps every internal gap and every run of set cells at
most `max m 3`**: the statement `GapStepClassB`, from `LocalRule.FourOnesFree.onesLe_finRule` at
all seven rules, from `LocalRule.FourZerosConst.gapLe_finRule` at the five whose zero-image graph
meets `FourZerosConst`, and from `gapLe_finRule_wolfram28` and `gapLe_finRule_wolfram70` at the
other two. -/
theorem gapStepClassB : GapStepClassB := by
  intro n hn hq s m hs ho
  have hones : ∀ n ∈ gapClassB, (wolframRule n).FourOnesFree := by decide
  have key : ∀ n ∈ gapClassB, n ≠ 28 → n ≠ 70 → (wolframRule n).FourZerosConst := by decide
  refine ⟨?_, ((hones n hn).onesLe_finRule hq s).mono (le_max_right m 3)⟩
  by_cases h28 : n = 28
  · subst h28
    exact gapLe_finRule_wolfram28 hq s m hs ho
  by_cases h70 : n = 70
  · subst h70
    exact gapLe_finRule_wolfram70 hq s m hs ho
  exact (key n hn h28 h70).gapLe_finRule hq s m hs ho

/-- **The two lists of rules reproduce no pattern**: no rule of `gapClassA` or `gapClassB`
reproduces a nonzero pattern. -/
theorem not_reproduces_gapClasses :
    ∀ n ∈ gapClassA ++ gapClassB, ∀ (hq : wolframRule n 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule n) hq) p :=
  not_reproduces_of_gapStepClassB gapStepClassB

/-! ## Two steps of a rule of the third class -/

/-- **Seven constant cells of the second image force the seven cells of the first image beneath
them constant**: for every word `x0, …, x10`, with the first image `f x_k x_{k+1} x_{k+2}` and the
second image taken of it, seven consecutive equal cells of the second image have the seven cells
of the first image beneath them equal. -/
def LocalRule.SevenConstLift (f : LocalRule) : Prop :=
  ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ZMod 2,
    (f (f x0 x1 x2) (f x1 x2 x3) (f x2 x3 x4) =
        f (f x1 x2 x3) (f x2 x3 x4) (f x3 x4 x5) ∧
      f (f x1 x2 x3) (f x2 x3 x4) (f x3 x4 x5) =
        f (f x2 x3 x4) (f x3 x4 x5) (f x4 x5 x6) ∧
      f (f x2 x3 x4) (f x3 x4 x5) (f x4 x5 x6) =
        f (f x3 x4 x5) (f x4 x5 x6) (f x5 x6 x7) ∧
      f (f x3 x4 x5) (f x4 x5 x6) (f x5 x6 x7) =
        f (f x4 x5 x6) (f x5 x6 x7) (f x6 x7 x8) ∧
      f (f x4 x5 x6) (f x5 x6 x7) (f x6 x7 x8) =
        f (f x5 x6 x7) (f x6 x7 x8) (f x7 x8 x9) ∧
      f (f x5 x6 x7) (f x6 x7 x8) (f x7 x8 x9) =
        f (f x6 x7 x8) (f x7 x8 x9) (f x8 x9 x10)) →
      ((f x1 x2 x3) = (f x2 x3 x4) ∧
      (f x2 x3 x4) = (f x3 x4 x5) ∧
      (f x3 x4 x5) = (f x4 x5 x6) ∧
      (f x4 x5 x6) = (f x5 x6 x7) ∧
      (f x5 x6 x7) = (f x6 x7 x8) ∧
      (f x6 x7 x8) = (f x7 x8 x9))

set_option synthInstance.maxSize 2000 in
instance (f : LocalRule) : Decidable (LocalRule.SevenConstLift f) := by
  unfold LocalRule.SevenConstLift; infer_instance

/-- The lifting of a window of seven constant cells, with the images given by their values. -/
private theorem sevenConst_window {f : LocalRule} (h : f.SevenConstLift)
    {s y z : ℤ → ZMod 2} (hy : ∀ x, y x = f (s (x - 1)) (s x) (s (x + 1)))
    (hz : ∀ x, z x = f (y (x - 1)) (y x) (y (x + 1))) (a : ℤ)
    (hc : z a = z (a + 1) ∧
      z (a + 1) = z (a + 2) ∧
      z (a + 2) = z (a + 3) ∧
      z (a + 3) = z (a + 4) ∧
      z (a + 4) = z (a + 5) ∧
      z (a + 5) = z (a + 6)) :
    y a = y (a + 1) ∧
      y (a + 1) = y (a + 2) ∧
      y (a + 2) = y (a + 3) ∧
      y (a + 3) = y (a + 4) ∧
      y (a + 4) = y (a + 5) ∧
      y (a + 5) = y (a + 6) := by
  have hy' : ∀ x u v w : ℤ, u = x - 1 → v = x → w = x + 1 →
      y x = f (s u) (s v) (s w) := by
    intro x u v w hu hv hw
    subst hu hv hw
    exact hy _
  have hz' : ∀ x u v w : ℤ, u = x - 1 → v = x → w = x + 1 →
      z x = f (y u) (y v) (y w) := by
    intro x u v w hu hv hw
    subst hu hv hw
    exact hz _
  have ey0 : y (a - 1) = f (s (a - 2)) (s (a - 1)) (s a) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ey1 : y a = f (s (a - 1)) (s a) (s (a + 1)) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ey2 : y (a + 1) = f (s a) (s (a + 1)) (s (a + 2)) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ey3 : y (a + 2) = f (s (a + 1)) (s (a + 2)) (s (a + 3)) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ey4 : y (a + 3) = f (s (a + 2)) (s (a + 3)) (s (a + 4)) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ey5 : y (a + 4) = f (s (a + 3)) (s (a + 4)) (s (a + 5)) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ey6 : y (a + 5) = f (s (a + 4)) (s (a + 5)) (s (a + 6)) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ey7 : y (a + 6) = f (s (a + 5)) (s (a + 6)) (s (a + 7)) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ey8 : y (a + 7) = f (s (a + 6)) (s (a + 7)) (s (a + 8)) :=
    hy' _ _ _ _ (by ring) (by ring) (by ring)
  have ez0 : z a = f (y (a - 1)) (y a) (y (a + 1)) :=
    hz' _ _ _ _ (by ring) (by ring) (by ring)
  have ez1 : z (a + 1) = f (y a) (y (a + 1)) (y (a + 2)) :=
    hz' _ _ _ _ (by ring) (by ring) (by ring)
  have ez2 : z (a + 2) = f (y (a + 1)) (y (a + 2)) (y (a + 3)) :=
    hz' _ _ _ _ (by ring) (by ring) (by ring)
  have ez3 : z (a + 3) = f (y (a + 2)) (y (a + 3)) (y (a + 4)) :=
    hz' _ _ _ _ (by ring) (by ring) (by ring)
  have ez4 : z (a + 4) = f (y (a + 3)) (y (a + 4)) (y (a + 5)) :=
    hz' _ _ _ _ (by ring) (by ring) (by ring)
  have ez5 : z (a + 5) = f (y (a + 4)) (y (a + 5)) (y (a + 6)) :=
    hz' _ _ _ _ (by ring) (by ring) (by ring)
  have ez6 : z (a + 6) = f (y (a + 5)) (y (a + 6)) (y (a + 7)) :=
    hz' _ _ _ _ (by ring) (by ring) (by ring)
  have H := h (s (a - 2)) (s (a - 1)) (s a) (s (a + 1)) (s (a + 2)) (s (a + 3))
    (s (a + 4)) (s (a + 5)) (s (a + 6)) (s (a + 7)) (s (a + 8))
  rw [← ey0, ← ey1, ← ey2, ← ey3, ← ey4, ← ey5, ← ey6, ← ey7, ← ey8] at H
  rw [← ez0, ← ez1, ← ez2, ← ez3, ← ez4, ← ez5, ← ez6] at H
  exact H hc

/-- If the window of seven cells of the second image starting at `a` is constant, so is the window
of seven cells of the first image starting at `a`. -/
private theorem sevenConst_const {f : LocalRule} (h : f.SevenConstLift) {s y z : ℤ → ZMod 2}
    (hy : ∀ x, y x = f (s (x - 1)) (s x) (s (x + 1)))
    (hz : ∀ x, z x = f (y (x - 1)) (y x) (y (x + 1))) (a : ℤ)
    (hc : ∀ x, a ≤ x → x ≤ a + 6 → z x = z a) : ∀ x, a ≤ x → x ≤ a + 6 → y x = y a := by
  obtain ⟨d0, d1, d2, d3, d4, d5⟩ := sevenConst_window h hy hz a
    ⟨(hc a le_rfl (by omega)).trans (hc (a + 1) (by omega) (by omega)).symm,
      (hc (a + 1) (by omega) (by omega)).trans (hc (a + 2) (by omega) (by omega)).symm,
      (hc (a + 2) (by omega) (by omega)).trans (hc (a + 3) (by omega) (by omega)).symm,
      (hc (a + 3) (by omega) (by omega)).trans (hc (a + 4) (by omega) (by omega)).symm,
      (hc (a + 4) (by omega) (by omega)).trans (hc (a + 5) (by omega) (by omega)).symm,
      (hc (a + 5) (by omega) (by omega)).trans (hc (a + 6) (by omega) (by omega)).symm⟩
  intro x h1 h2
  rcases (by omega : x = a ∨ x = a + 1 ∨ x = a + 2 ∨ x = a + 3 ∨ x = a + 4 ∨ x = a + 5 ∨
    x = a + 6) with hx | hx | hx | hx | hx | hx | hx <;> subst hx
  · rfl
  · exact d0.symm
  · exact d1.symm.trans d0.symm
  · exact d2.symm.trans (d1.symm.trans d0.symm)
  · exact d3.symm.trans (d2.symm.trans (d1.symm.trans d0.symm))
  · exact d4.symm.trans (d3.symm.trans (d2.symm.trans (d1.symm.trans d0.symm)))
  · exact d5.symm.trans (d4.symm.trans (d3.symm.trans (d2.symm.trans (d1.symm.trans d0.symm))))

/-- A nonzero cell of `ZMod 2` is `1`. -/
private theorem eq_one_of_ne_zero_zmod2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

/-- A constant stretch of at least seven cells of the second image makes the first image constant
over the same stretch. -/
private theorem y_const_of_z_const {f : LocalRule} (hq : f 0 0 0 = 0) (y : FiniteConfiguration)
    (hwin : ∀ a : ℤ, (∀ x, a ≤ x → x ≤ a + 6 → finRule f hq y x = finRule f hq y a) →
      ∀ x, a ≤ x → x ≤ a + 6 → y x = y a)
    {i j : ℤ} {c : ZMod 2} (hZ : ∀ x, i ≤ x → x ≤ j → finRule f hq y x = c) (hij : i + 6 ≤ j) :
    ∀ x, i ≤ x → x ≤ j → y x = y i := by
  have hW : ∀ a, i ≤ a → a + 6 ≤ j → ∀ x, a ≤ x → x ≤ a + 6 → y x = y a :=
    fun a h1 h2 => hwin a fun x hx1 hx2 =>
      (hZ x (by omega) (by omega)).trans (hZ a h1 (by omega)).symm
  have hstep : ∀ x, i ≤ x → x + 1 ≤ j → y x = y (x + 1) := by
    intro x h1 h2
    by_cases hx : x + 6 ≤ j
    · exact (hW x h1 hx (x + 1) (by omega) (by omega)).symm
    · exact (hW (j - 6) (by omega) (by omega) x (by omega) (by omega)).trans
        (hW (j - 6) (by omega) (by omega) (x + 1) (by omega) (by omega)).symm
  refine fun x h1 => induction_from_int (P := fun x => x ≤ j → y x = y i) i
    (fun _ => rfl) (fun x hx ih h2 => ?_) x h1
  exact (hstep x hx (by omega)).symm.trans (ih (by omega))

/-- The two-step bound from the lifting of constant windows: the statement of
`LocalRule.SevenConstLift.twoStep` with the lifting as a hypothesis. -/
private theorem twoStep_aux {f : LocalRule} (hq : f 0 0 0 = 0) (y : FiniteConfiguration) (m : ℕ)
    (hg : y.GapLe m) (ho : y.OnesLe m)
    (hwin : ∀ a : ℤ, (∀ x, a ≤ x → x ≤ a + 6 → finRule f hq y x = finRule f hq y a) →
      ∀ x, a ≤ x → x ≤ a + 6 → y x = y a) :
    (finRule f hq y).GapLe (max m 6) ∧ (finRule f hq y).OnesLe (max m 6) := by
  have hm := le_max_left m 6
  have hm2 := le_max_right m 6
  refine ⟨?_, ?_⟩
  · intro i j hij hi hj hk
    by_cases hsm : j - i ≤ 7
    · omega
    have hconst := y_const_of_z_const hq y hwin (i := i + 1) (j := j - 1) (c := 0)
      (fun x h1 h2 => hk x (by omega) (by omega)) (by omega)
    by_cases hc : y (i + 1) = 0
    · have hclear : ∀ x, i < x → x < j → y x = 0 := fun x h1 h2 =>
        (hconst x (by omega) (by omega)).trans hc
      obtain ⟨p, hp1, hp2, hp3⟩ : ∃ p, p ≤ i ∧ y p ≠ 0 ∧ ∀ x, p < x → x < j → y x = 0 := by
        by_cases hsi : y i = 0
        · have hi' := exists_set_of_finRule_ne hq y hi
          rw [hsi, hclear (i + 1) (by omega) (by omega)] at hi'
          refine ⟨i - 1, by omega, by tauto, fun x hx1 hx2 => ?_⟩
          by_cases hxi : x = i
          · rwa [hxi]
          · exact hclear x (by omega) hx2
        · exact ⟨i, le_rfl, hsi, fun x hx1 hx2 => hclear x hx1 hx2⟩
      obtain ⟨q, hq1, hq2, hq3⟩ : ∃ q, j ≤ q ∧ y q ≠ 0 ∧ ∀ x, i < x → x < q → y x = 0 := by
        by_cases hsj : y j = 0
        · have hj' := exists_set_of_finRule_ne hq y hj
          rw [hsj, hclear (j - 1) (by omega) (by omega)] at hj'
          refine ⟨j + 1, by omega, by tauto, fun x hx1 hx2 => ?_⟩
          by_cases hxj : x = j
          · rwa [hxj]
          · exact hclear x hx1 (by omega)
        · exact ⟨j, le_rfl, hsj, fun x hx1 hx2 => hclear x hx1 hx2⟩
      have := hg p q (by omega) hp2 hq2 fun x hx1 hx2 => by
        by_cases hxj : x < j
        · exact hp3 x hx1 hxj
        · exact hq3 x (by omega) hx2
      omega
    · have := ho (i + 1) (j - 1) (by omega) fun k hk1 hk2 => by
        rw [hconst k hk1 hk2]
        exact hc
      omega
  · intro i j hij hk
    by_cases hsm : j - i + 1 ≤ 6
    · omega
    have hconst := y_const_of_z_const hq y hwin (i := i) (j := j) (c := 1)
      (fun x h1 h2 => eq_one_of_ne_zero_zmod2 _ (hk x h1 h2)) (by omega)
    by_cases hc : y i = 0
    · exfalso
      have e := finRule_apply f hq y (i + 1)
      rw [show i + 1 - 1 = i by ring, show i + 1 + 1 = i + 2 by ring,
        (hconst (i + 1) (by omega) (by omega)).trans hc, hconst (i + 2) (by omega) (by omega),
        hc] at e
      exact hk (i + 1) (by omega) (by omega) (e.trans hq)
    · have := ho i j hij fun k hk1 hk2 => by
        rw [hconst k hk1 hk2]
        exact hc
      omega

/-- **Two steps of a rule with `SevenConstLift` keep every internal gap and every run of set cells
at most `max m 6`**, given both at most `m` for the first image: a stretch of seven constant cells
of the second image is lifted to a constant stretch of the first, which is a run of set cells or
lies inside an internal gap of the first image. -/
theorem LocalRule.SevenConstLift.twoStep {f : LocalRule} (h : f.SevenConstLift)
    (hq : f 0 0 0 = 0) (s : FiniteConfiguration) (m : ℕ)
    (hg : (finRule f hq s).GapLe m) (ho : (finRule f hq s).OnesLe m) :
    (finRule f hq (finRule f hq s)).GapLe (max m 6) ∧
      (finRule f hq (finRule f hq s)).OnesLe (max m 6) :=
  twoStep_aux hq (finRule f hq s) m hg ho fun a hc =>
    sevenConst_const h (s := s) (y := finRule f hq s) (z := finRule f hq (finRule f hq s))
      (fun x => finRule_apply f hq s x) (fun x => finRule_apply f hq (finRule f hq s) x) a hc

/-- **Joint satisfiability**: rule `62` is quiescent and meets `SevenConstLift`, and the image of a
single set cell has internal gaps and runs of set cells bounded by `3`. -/
theorem LocalRule.SevenConstLift.twoStep_nonvacuous :
    (wolframRule 62).SevenConstLift ∧ wolframRule 62 0 0 0 = 0 ∧
      (finRule (wolframRule 62) (by decide) (Finsupp.single 0 1)).GapLe 3 ∧
      (finRule (wolframRule 62) (by decide) (Finsupp.single 0 1)).OnesLe 3 := by
  have key : ∀ k : ℤ, finRule (wolframRule 62) (by decide) (Finsupp.single 0 1) k ≠ 0 →
      k = -1 ∨ k = 0 ∨ k = 1 := by
    intro k hk
    by_contra hc
    push Not at hc
    apply hk
    rw [finRule_apply]
    have h1 : (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (k - 1) = 0 :=
      Finsupp.single_eq_of_ne (by omega)
    have h2 : (Finsupp.single (0 : ℤ) (1 : ZMod 2)) k = 0 := Finsupp.single_eq_of_ne (by omega)
    have h3 : (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (k + 1) = 0 :=
      Finsupp.single_eq_of_ne (by omega)
    rw [h1, h2, h3]
    decide
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro i j hij hi hj _
    rcases key i hi with rfl | rfl | rfl <;> rcases key j hj with rfl | rfl | rfl <;> omega
  · intro i j hij hk
    rcases key i (hk i le_rfl hij) with rfl | rfl | rfl <;>
      rcases key j (hk j hij le_rfl) with rfl | rfl | rfl <;> omega

/-- The rules `62` and `118`, among the growing rules not shown to reproduce. -/
def gapClassC : List ℕ := [62, 118]

/-- **The two rules of `gapClassC` reproduce no pattern**: `SevenConstLift` holds at both, and along
the orbit of a pattern `p` the internal gaps and runs of set cells stay at most
`max (max (diam p) (diam (F p))) 6`, by induction on the time from
`LocalRule.SevenConstLift.twoStep`, where `F` is the rule's action. -/
theorem not_reproduces_gapClassC :
    ∀ n ∈ gapClassC, ∀ (hq : wolframRule n 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule n) hq) p := by
  intro n hn hq p
  have h : (wolframRule n).SevenConstLift := by
    have key : ∀ n ∈ gapClassC, (wolframRule n).SevenConstLift := by decide
    exact key n hn
  have hB := le_max_right (max (diam p) (diam (finRule (wolframRule n) hq p))) 6
  refine not_reproduces_of_gapLe _ p
    (max (max (diam p) (diam (finRule (wolframRule n) hq p))) 6) fun t => ?_
  have key : ∀ t, (((finRule (wolframRule n) hq)^[t + 1] p).GapLe
      (max (max (diam p) (diam (finRule (wolframRule n) hq p))) 6)) ∧
      (((finRule (wolframRule n) hq)^[t + 1] p).OnesLe
      (max (max (diam p) (diam (finRule (wolframRule n) hq p))) 6)) := by
    intro t
    induction t with
    | zero =>
      rw [zero_add, Function.iterate_one]
      exact ⟨(gapLe_diam _).mono ((le_max_right _ _).trans (le_max_left _ _)),
        (onesLe_diam _).mono ((le_max_right _ _).trans (le_max_left _ _))⟩
    | succ t ih =>
      have e1 : (finRule (wolframRule n) hq)^[t + 1] p =
          finRule (wolframRule n) hq ((finRule (wolframRule n) hq)^[t] p) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : (finRule (wolframRule n) hq)^[t + 1 + 1] p = finRule (wolframRule n) hq
          (finRule (wolframRule n) hq ((finRule (wolframRule n) hq)^[t] p)) := by
        rw [Function.iterate_succ_apply', e1]
      rw [e1] at ih
      rw [e2]
      have := h.twoStep hq _ _ ih.1 ih.2
      rwa [max_eq_left hB] at this
  cases t with
  | zero => exact (gapLe_diam p).mono ((le_max_left _ _).trans (le_max_left _ _))
  | succ t => exact (key t).1

/-! ## Stretches with no two adjacent set cells -/

/-- Every set-flanked stretch of `s` holding no two adjacent set cells has at most `m` cells. -/
def FiniteConfiguration.PairFreeLe (s : FiniteConfiguration) (m : ℕ) : Prop :=
  ∀ i j : ℤ, i ≤ j → s i ≠ 0 → s j ≠ 0 →
    (∀ k, i ≤ k → k < j → s k = 0 ∨ s (k + 1) = 0) → j - i + 1 ≤ m

/-- No four consecutive cells of `s` read `a b c d`, left to right. -/
def FiniteConfiguration.Avoids (s : FiniteConfiguration) (a b c d : ZMod 2) : Prop :=
  ∀ k : ℤ, ¬ (s k = a ∧ s (k + 1) = b ∧ s (k + 2) = c ∧ s (k + 3) = d)

/-- **A bound on the pair-free stretches bounds the internal gaps**: an internal gap between two
set cells is a stretch with no two adjacent set cells. -/
theorem FiniteConfiguration.PairFreeLe.gapLe {s : FiniteConfiguration} {m : ℕ}
    (h : s.PairFreeLe m) : s.GapLe m := by
  intro i j hij hi hj hk
  by_cases hsm : j - i ≤ 1
  · omega
  have := h i j hij.le hi hj fun k h1 h2 => by
    by_cases hki : k = i
    · exact Or.inr (hk (k + 1) (by omega) (by omega))
    · exact Or.inl (hk k (by omega) h2)
  omega

/-- **Every pair-free stretch of a state is at most its support diameter.** -/
theorem FiniteConfiguration.pairFreeLe_diam (s : FiniteConfiguration) :
    s.PairFreeLe (diam s) := by
  intro i j hij hi hj _
  have := span_le_diam_of_cells hi hj
  omega

/-- The value of the image at a cell, with the neighbours named by equations. -/
private theorem finRule_at {f : LocalRule} (hq : f 0 0 0 = 0) (s : FiniteConfiguration)
    (x u w : ℤ) (hu : u = x - 1) (hw : w = x + 1) :
    finRule f hq s x = f (s u) (s x) (s w) := by
  subst hu hw
  exact finRule_apply f hq s x

/-! ### Rule 202 -/

/-- At rule `202`, two adjacent set cells give two adjacent set cells of the image. -/
private theorem wolfram202_pair (a b c d : ZMod 2) (hb : b ≠ 0) (hc : c ≠ 0) :
    wolframRule 202 a b c ≠ 0 ∧ wolframRule 202 b c d ≠ 0 := by
  revert a b c d; decide

/-- At rule `202`, a set cell of the image has a set cell at itself or at its right neighbour. -/
private theorem wolfram202_right (a b c : ZMod 2) (h : wolframRule 202 a b c ≠ 0) :
    b ≠ 0 ∨ c ≠ 0 := by
  revert a b c; decide

/-- At rule `202`, a zero image of a set cell preceded by a clear cell has a clear right
neighbour. -/
private theorem wolfram202_clear (b c : ZMod 2) (hb : b ≠ 0) (h : wolframRule 202 0 b c = 0) :
    c = 0 := by
  revert b c; decide

/-- At rule `202`, a zero image of a set cell flanked by a clear cell and a set cell has a set left
neighbour. -/
private theorem wolfram202_left (a c : ZMod 2) (hc : c ≠ 0) (h : wolframRule 202 a 0 c = 0) :
    a ≠ 0 := by
  revert a c; decide

/-- The image of rule `202` never reads `0101`. -/
private theorem wolfram202_avoid (x0 x1 x2 x3 x4 x5 : ZMod 2) :
    ¬ (wolframRule 202 x0 x1 x2 = 0 ∧ wolframRule 202 x1 x2 x3 = 1 ∧
      wolframRule 202 x2 x3 x4 = 0 ∧ wolframRule 202 x3 x4 x5 = 1) := by
  revert x0 x1 x2 x3 x4 x5; decide

/-- **The image of a state under rule `202` never reads `0101`**: a clear cell of the image beside a
set cell needs the set cell of the state at once on its right. -/
theorem avoids_finRule_wolfram202 (hq : wolframRule 202 0 0 0 = 0) (s : FiniteConfiguration) :
    (finRule (wolframRule 202) hq s).Avoids 0 1 0 1 := by
  intro k ⟨h0, h1, h2, h3⟩
  rw [finRule_at hq s k (k - 1) (k + 1) (by ring) (by ring)] at h0
  rw [finRule_at hq s (k + 1) k (k + 2) (by ring) (by ring)] at h1
  rw [finRule_at hq s (k + 2) (k + 1) (k + 3) (by ring) (by ring)] at h2
  rw [finRule_at hq s (k + 3) (k + 2) (k + 4) (by ring) (by ring)] at h3
  exact wolfram202_avoid _ _ _ _ _ _ ⟨h0, h1, h2, h3⟩

/-- **One step of rule `202` keeps the pair-free stretches at most `m`** on a state that does not
read `0101`: a stretch of the image between two set cells is carried by a stretch of the state
between set cells beside its ends, and only a stretch starting on a clear cell of the state and
ending on a set one could lose a cell, which would put `0101` into the state. -/
theorem pairFreeLe_finRule_wolfram202 (hq : wolframRule 202 0 0 0 = 0)
    (s : FiniteConfiguration) (m : ℕ) (hw : s.Avoids 0 1 0 1) (h : s.PairFreeLe m) :
    (finRule (wolframRule 202) hq s).PairFreeLe m := by
  intro i j hij hi hj hk
  have hb : ∀ x, finRule (wolframRule 202) hq s x ≠ 0 → s x ≠ 0 ∨ s (x + 1) ≠ 0 := by
    intro x hx
    rw [finRule_at hq s x (x - 1) (x + 1) (by ring) (by ring)] at hx
    exact wolfram202_right _ _ _ hx
  have ha : ∀ x, s x ≠ 0 → s (x + 1) ≠ 0 → finRule (wolframRule 202) hq s x ≠ 0 ∧
      finRule (wolframRule 202) hq s (x + 1) ≠ 0 := by
    intro x h1 h2
    rw [finRule_at hq s x (x - 1) (x + 1) (by ring) (by ring),
      finRule_at hq s (x + 1) x (x + 2) (by ring) (by ring)]
    exact wolfram202_pair _ _ _ _ h1 h2
  have core : ∀ i' j' : ℤ, i ≤ i' → j' ≤ j + 1 → i' ≤ j' → s i' ≠ 0 → s j' ≠ 0 →
      (j' = j + 1 → s j = 0) → j' - i' + 1 ≤ m := by
    intro i' j' h1 h2 h3 h4 h5 h6
    refine h i' j' h3 h4 h5 fun k hk1 hk2 => ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2⟩ := ha k hcon.1 hcon.2
    rcases lt_or_ge k j with hkj | hkj
    · rcases hk k (by omega) hkj with e | e
      · exact c1 e
      · exact c2 e
    · have hkj' : k = j := by omega
      rw [hkj'] at hcon
      exact hcon.1 (h6 (by omega))
  by_cases hsi : s i = 0 <;> by_cases hsj : s j = 0
  · have hi1 : s (i + 1) ≠ 0 := (hb i hi).resolve_left (fun hh => hh hsi)
    have hj1 : s (j + 1) ≠ 0 := (hb j hj).resolve_left (fun hh => hh hsj)
    have := core (i + 1) (j + 1) (by omega) (by omega) (by omega) hi1 hj1 (fun _ => hsj)
    omega
  · have hi1 : s (i + 1) ≠ 0 := (hb i hi).resolve_left (fun hh => hh hsi)
    have hij' : i < j := by
      rcases hij.lt_or_eq with h' | h'
      · exact h'
      · rw [h'] at hsi
        exact absurd hsi hsj
    exfalso
    have h2 : finRule (wolframRule 202) hq s (i + 1) = 0 :=
      (hk i le_rfl hij').resolve_left hi
    have h2' := (finRule_at hq s (i + 1) i (i + 2) (by ring) (by ring)).symm.trans h2
    rw [hsi] at h2'
    have h3 : s (i + 2) = 0 := wolfram202_clear _ _ hi1 h2'
    have hj3 : i + 3 ≤ j := by
      rcases (by omega : j = i + 1 ∨ j = i + 2 ∨ i + 3 ≤ j) with e | e | e
      · rw [e] at hj
        exact absurd h2 hj
      · rw [e] at hsj
        exact (hsj h3).elim
      · exact e
    have h4 : s (j - 1) = 0 := by
      by_contra hne
      obtain ⟨c1, c2⟩ := ha (j - 1) hne (by rw [sub_add_cancel]; exact hsj)
      rcases hk (j - 1) (by omega) (by omega) with e | e
      · exact c1 e
      · exact c2 e
    have h5 : finRule (wolframRule 202) hq s (j - 1) = 0 := by
      rcases hk (j - 1) (by omega) (by omega) with e | e
      · exact e
      · rw [sub_add_cancel] at e
        exact absurd e hj
    have h5' := (finRule_at hq s (j - 1) (j - 2) j (by ring) (by ring)).symm.trans h5
    rw [h4] at h5'
    have h6 : s (j - 2) ≠ 0 := wolfram202_left _ _ hsj h5'
    have h7 : s (j - 3) = 0 := by
      by_cases hji : j - 3 = i
      · rw [hji]
        exact hsi
      · by_contra hne
        obtain ⟨c1, c2⟩ := ha (j - 3) hne (by rw [show j - 3 + 1 = j - 2 by ring]; exact h6)
        rcases hk (j - 3) (by omega) (by omega) with e | e
        · exact c1 e
        · exact c2 e
    refine hw (j - 3) ⟨h7, ?_, ?_, ?_⟩
    · rw [show j - 3 + 1 = j - 2 by ring]
      exact eq_one_of_ne_zero_zmod2 _ h6
    · rw [show j - 3 + 2 = j - 1 by ring]
      exact h4
    · rw [show j - 3 + 3 = j by ring]
      exact eq_one_of_ne_zero_zmod2 _ hsj
  · have hj1 : s (j + 1) ≠ 0 := (hb j hj).resolve_left (fun hh => hh hsj)
    have := core i (j + 1) le_rfl (by omega) (by omega) hsi hj1 (fun _ => hsj)
    omega
  · have := core i j le_rfl (by omega) hij hsi hsj (fun h' => absurd h' (by omega))
    omega

/-! ### Rule 216 -/

/-- At rule `216`, two adjacent set cells give two adjacent set cells of the image. -/
private theorem wolfram216_pair (a b c d : ZMod 2) (hb : b ≠ 0) (hc : c ≠ 0) :
    wolframRule 216 a b c ≠ 0 ∧ wolframRule 216 b c d ≠ 0 := by
  revert a b c d; decide

/-- At rule `216`, a set cell of the image has a set cell at itself or at its left neighbour. -/
private theorem wolfram216_left (a b c : ZMod 2) (h : wolframRule 216 a b c ≠ 0) :
    a ≠ 0 ∨ b ≠ 0 := by
  revert a b c; decide

/-- At rule `216`, a zero image of a set cell followed by a clear cell has a clear left
neighbour. -/
private theorem wolfram216_clear (a b : ZMod 2) (hb : b ≠ 0) (h : wolframRule 216 a b 0 = 0) :
    a = 0 := by
  revert a b; decide

/-- At rule `216`, a zero image of a set cell flanked by a set cell and a clear cell has a set
right neighbour. -/
private theorem wolfram216_right (a c : ZMod 2) (ha : a ≠ 0) (h : wolframRule 216 a 0 c = 0) :
    c ≠ 0 := by
  revert a c; decide

/-- The image of rule `216` never reads `1010`. -/
private theorem wolfram216_avoid (x0 x1 x2 x3 x4 x5 : ZMod 2) :
    ¬ (wolframRule 216 x0 x1 x2 = 1 ∧ wolframRule 216 x1 x2 x3 = 0 ∧
      wolframRule 216 x2 x3 x4 = 1 ∧ wolframRule 216 x3 x4 x5 = 0) := by
  revert x0 x1 x2 x3 x4 x5; decide

/-- **The image of a state under rule `216` never reads `1010`**: the mirror image of rule `202`. -/
theorem avoids_finRule_wolfram216 (hq : wolframRule 216 0 0 0 = 0) (s : FiniteConfiguration) :
    (finRule (wolframRule 216) hq s).Avoids 1 0 1 0 := by
  intro k ⟨h0, h1, h2, h3⟩
  rw [finRule_at hq s k (k - 1) (k + 1) (by ring) (by ring)] at h0
  rw [finRule_at hq s (k + 1) k (k + 2) (by ring) (by ring)] at h1
  rw [finRule_at hq s (k + 2) (k + 1) (k + 3) (by ring) (by ring)] at h2
  rw [finRule_at hq s (k + 3) (k + 2) (k + 4) (by ring) (by ring)] at h3
  exact wolfram216_avoid _ _ _ _ _ _ ⟨h0, h1, h2, h3⟩

/-- **One step of rule `216` keeps the pair-free stretches at most `m`** on a state that does not
read `1010`: the mirror image of rule `202`. -/
theorem pairFreeLe_finRule_wolfram216 (hq : wolframRule 216 0 0 0 = 0)
    (s : FiniteConfiguration) (m : ℕ) (hw : s.Avoids 1 0 1 0) (h : s.PairFreeLe m) :
    (finRule (wolframRule 216) hq s).PairFreeLe m := by
  intro i j hij hi hj hk
  have hb : ∀ x, finRule (wolframRule 216) hq s x ≠ 0 → s (x - 1) ≠ 0 ∨ s x ≠ 0 := by
    intro x hx
    rw [finRule_at hq s x (x - 1) (x + 1) (by ring) (by ring)] at hx
    exact wolfram216_left _ _ _ hx
  have ha : ∀ x, s x ≠ 0 → s (x + 1) ≠ 0 → finRule (wolframRule 216) hq s x ≠ 0 ∧
      finRule (wolframRule 216) hq s (x + 1) ≠ 0 := by
    intro x h1 h2
    rw [finRule_at hq s x (x - 1) (x + 1) (by ring) (by ring),
      finRule_at hq s (x + 1) x (x + 2) (by ring) (by ring)]
    exact wolfram216_pair _ _ _ _ h1 h2
  have core : ∀ i' j' : ℤ, i - 1 ≤ i' → j' ≤ j → i' ≤ j' → s i' ≠ 0 → s j' ≠ 0 →
      (i' = i - 1 → s i = 0) → j' - i' + 1 ≤ m := by
    intro i' j' h1 h2 h3 h4 h5 h6
    refine h i' j' h3 h4 h5 fun k hk1 hk2 => ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2⟩ := ha k hcon.1 hcon.2
    rcases le_or_gt i k with hik | hik
    · rcases hk k hik (by omega) with e | e
      · exact c1 e
      · exact c2 e
    · have hs0 := h6 (by omega)
      rw [show k + 1 = i by omega] at hcon
      exact hcon.2 hs0
  by_cases hsi : s i = 0 <;> by_cases hsj : s j = 0
  · have hi1 : s (i - 1) ≠ 0 := (hb i hi).resolve_right (fun hh => hh hsi)
    have hj1 : s (j - 1) ≠ 0 := (hb j hj).resolve_right (fun hh => hh hsj)
    have := core (i - 1) (j - 1) le_rfl (by omega) (by omega) hi1 hj1 (fun _ => hsi)
    omega
  · have hi1 : s (i - 1) ≠ 0 := (hb i hi).resolve_right (fun hh => hh hsi)
    have := core (i - 1) j le_rfl (by omega) (by omega) hi1 hsj (fun _ => hsi)
    omega
  · have hij' : i < j := by
      rcases hij.lt_or_eq with h' | h'
      · exact h'
      · rw [h'] at hsi
        exact absurd hsj hsi
    exfalso
    have hj1 : s (j - 1) ≠ 0 := (hb j hj).resolve_right (fun hh => hh hsj)
    have h5 : finRule (wolframRule 216) hq s (j - 1) = 0 :=
      (hk (j - 1) (by omega) (by omega)).resolve_right (by rw [sub_add_cancel]; exact hj)
    have h5' := (finRule_at hq s (j - 1) (j - 2) j (by ring) (by ring)).symm.trans h5
    rw [hsj] at h5'
    have h6 : s (j - 2) = 0 := wolfram216_clear _ _ hj1 h5'
    have hj3 : i + 3 ≤ j := by
      rcases (by omega : j = i + 1 ∨ j = i + 2 ∨ i + 3 ≤ j) with e | e | e
      · rw [show j - 1 = i by omega] at h5
        exact (hi h5).elim
      · rw [show j - 2 = i by omega] at h6
        exact (hsi h6).elim
      · exact e
    have h2 : s (i + 1) = 0 := by
      by_contra hne
      obtain ⟨c1, c2⟩ := ha i hsi hne
      rcases hk i le_rfl hij' with e | e
      · exact c1 e
      · exact c2 e
    have h3 : finRule (wolframRule 216) hq s (i + 1) = 0 :=
      (hk i le_rfl hij').resolve_left hi
    have h3' := (finRule_at hq s (i + 1) i (i + 2) (by ring) (by ring)).symm.trans h3
    rw [h2] at h3'
    have h4 : s (i + 2) ≠ 0 := wolfram216_right _ _ hsi h3'
    have h7 : s (i + 3) = 0 := by
      by_cases hji : i + 3 = j
      · rw [hji]
        exact hsj
      · by_contra hne
        obtain ⟨c1, c2⟩ := ha (i + 2) h4 (by rw [show i + 2 + 1 = i + 3 by ring]; exact hne)
        rcases hk (i + 2) (by omega) (by omega) with e | e
        · exact c1 e
        · exact c2 e
    exact hw i ⟨eq_one_of_ne_zero_zmod2 _ hsi, h2, eq_one_of_ne_zero_zmod2 _ h4, h7⟩
  · have := core i j (by omega) le_rfl hij hsi hsj (fun h' => absurd h' (by omega))
    omega

/-! ### The rules `202` and `216` -/

/-- The rules `202` and `216`, among the growing rules not shown to reproduce. -/
def gapClassD : List ℕ := [202, 216]

/-- A map whose images avoid a window, and carry a pair-free bound from a state avoiding it to its
image, reproduces no pattern. -/
private theorem not_reproduces_of_pairFree {F : FiniteConfiguration → FiniteConfiguration}
    (A : FiniteConfiguration → Prop) (hA : ∀ s, A (F s))
    (hS : ∀ (s : FiniteConfiguration) (m : ℕ), A s → s.PairFreeLe m → (F s).PairFreeLe m)
    (p : FiniteConfiguration) : ¬ Reproduces F p := by
  refine not_reproduces_of_gapLe F p (max (diam p) (diam (F p))) fun t => ?_
  have key : ∀ t, (F^[t + 1] p).PairFreeLe (diam (F p)) := by
    intro t
    induction t with
    | zero =>
      rw [zero_add, Function.iterate_one]
      exact pairFreeLe_diam _
    | succ t ih =>
      have hAt : A (F^[t + 1] p) := by
        rw [Function.iterate_succ_apply']
        exact hA _
      rw [Function.iterate_succ_apply']
      exact hS _ _ hAt ih
  cases t with
  | zero => exact (gapLe_diam p).mono (le_max_left _ _)
  | succ t => exact (key t).gapLe.mono (le_max_right _ _)

/-- **The two rules of `gapClassD` reproduce no pattern**: along the orbit of a pattern `p` the
pair-free stretches stay at most `diam (F p)` from the first step on, by induction on the time from
`FiniteConfiguration.pairFreeLe_diam`, `pairFreeLe_finRule_wolfram202` and
`pairFreeLe_finRule_wolfram216`, each state after the first being an image and so avoiding the
window of its rule; the internal gaps are then bounded by `max (diam p) (diam (F p))`, where `F` is
the rule's action. -/
theorem not_reproduces_gapClassD :
    ∀ n ∈ gapClassD, ∀ (hq : wolframRule n 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule n) hq) p := by
  intro n hn hq p
  have hn' : n = 202 ∨ n = 216 := by simpa [gapClassD] using hn
  rcases hn' with rfl | rfl
  · exact not_reproduces_of_pairFree (fun s => s.Avoids 0 1 0 1) (avoids_finRule_wolfram202 hq)
      (fun s m hw h => pairFreeLe_finRule_wolfram202 hq s m hw h) p
  · exact not_reproduces_of_pairFree (fun s => s.Avoids 1 0 1 0) (avoids_finRule_wolfram216 hq)
      (fun s m hw h => pairFreeLe_finRule_wolfram216 hq s m hw h) p

/-- **Joint satisfiability**: the state `10011` avoids `0101` and has pair-free stretches at most
`4`, and its image under rule `202` has a pair-free stretch of four cells, so the bound `4` is not
improved by one step. -/
theorem pairFreeLe_finRule_wolfram202_nonvacuous :
    (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1 :
        FiniteConfiguration).Avoids 0 1 0 1 ∧
    (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1 :
        FiniteConfiguration).PairFreeLe 4 ∧
    ¬ (finRule (wolframRule 202) (by decide)
        (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1)).PairFreeLe 3 := by
  have hv : ∀ x : ℤ, (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1 :
      FiniteConfiguration) x = if x = 0 ∨ x = 3 ∨ x = 4 then 1 else 0 := by
    intro x
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> first | omega | decide
  have key : ∀ k : ℤ, (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1 :
      FiniteConfiguration) k ≠ 0 → k = 0 ∨ k = 3 ∨ k = 4 := by
    intro k hk
    rw [hv] at hk
    by_contra hc
    exact hk (by simp [hc])
  have hset : ∀ k : ℤ, k = 0 ∨ k = 3 ∨ k = 4 → (Finsupp.single 0 1 + Finsupp.single 3 1 +
      Finsupp.single 4 1 : FiniteConfiguration) k ≠ 0 := by
    intro k hk
    rw [hv]
    simp [hk]
  refine ⟨?_, ?_, ?_⟩
  · intro k ⟨_, h1, _, h3⟩
    have a1 := key (k + 1) (by rw [h1]; decide)
    have a3 := key (k + 3) (by rw [h3]; decide)
    omega
  · intro i j hij hi hj hk
    have hi' := key i hi
    have hj' := key j hj
    by_cases h04 : i = 0 ∧ j = 4
    · obtain ⟨rfl, rfl⟩ := h04
      rcases hk 3 (by omega) (by omega) with e | e
      · exact absurd e (hset 3 (by omega))
      · exact absurd e (hset (3 + 1) (by omega))
    · omega
  · intro hp
    have hy : ∀ x : ℤ, finRule (wolframRule 202) (by decide)
        (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1) x =
        wolframRule 202 (if x - 1 = 0 ∨ x - 1 = 3 ∨ x - 1 = 4 then 1 else 0)
          (if x = 0 ∨ x = 3 ∨ x = 4 then 1 else 0)
          (if x + 1 = 0 ∨ x + 1 = 3 ∨ x + 1 = 4 then 1 else 0) := by
      intro x
      rw [finRule_apply, hv, hv, hv]
    have y1 : finRule (wolframRule 202) (by decide)
        (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1) (-1) ≠ 0 := by
      rw [hy]; decide
    have y2 : finRule (wolframRule 202) (by decide)
        (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1) 2 ≠ 0 := by
      rw [hy]; decide
    have y0 : finRule (wolframRule 202) (by decide)
        (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1) 0 = 0 := by
      rw [hy]; decide
    have y3 : finRule (wolframRule 202) (by decide)
        (Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1) 1 = 0 := by
      rw [hy]; decide
    have := hp (-1) 2 (by omega) y1 y2 fun k hk1 hk2 => by
      rcases (by omega : k = -1 ∨ k = 0 ∨ k = 1) with rfl | rfl | rfl
      · exact Or.inr y0
      · exact Or.inl y0
      · exact Or.inl y3
    omega

end ECA

/-- info: 'ECA.FiniteConfiguration.gapLe_diam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.gapLe_diam

/-- info: 'ECA.FiniteConfiguration.onesLe_diam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.onesLe_diam

/-- info: 'ECA.not_reproduces_of_gapStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_gapStep

/-- info: 'ECA.not_reproduces_of_gapLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_gapLe

/-- info: 'ECA.not_reproduces_of_gapStep_of_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_gapStep_of_classes

/-- info: 'ECA.LocalRule.ThreeZerosClear.gapLe_finRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ThreeZerosClear.gapLe_finRule

/-- info: 'ECA.LocalRule.ThreeZerosClear.gapLe_finRule_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ThreeZerosClear.gapLe_finRule_nonvacuous

/-- info: 'ECA.gapLe_finRule_wolfram234' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.gapLe_finRule_wolfram234

/-- info: 'ECA.gapLe_finRule_wolfram248' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.gapLe_finRule_wolfram248

/-- info: 'ECA.gapStepClassA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.gapStepClassA

/-- info: 'ECA.not_reproduces_of_gapStepClassB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_of_gapStepClassB

/-- info: 'ECA.LocalRule.FourOnesFree.onesLe_finRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.FourOnesFree.onesLe_finRule

/-- info: 'ECA.LocalRule.FourZerosConst.gapLe_finRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.FourZerosConst.gapLe_finRule

/-- info: 'ECA.LocalRule.FourZerosConst.gapLe_finRule_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.FourZerosConst.gapLe_finRule_nonvacuous

/-- info: 'ECA.gapLe_finRule_wolfram28' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.gapLe_finRule_wolfram28

/-- info: 'ECA.gapLe_finRule_wolfram70' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.gapLe_finRule_wolfram70

/-- info: 'ECA.gapStepClassB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.gapStepClassB

/-- info: 'ECA.not_reproduces_gapClasses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_gapClasses

/-- info: 'ECA.LocalRule.SevenConstLift.twoStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.SevenConstLift.twoStep

/-- info: 'ECA.LocalRule.SevenConstLift.twoStep_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.SevenConstLift.twoStep_nonvacuous

/-- info: 'ECA.not_reproduces_gapClassC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_gapClassC

/-- info: 'ECA.FiniteConfiguration.PairFreeLe.gapLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.PairFreeLe.gapLe

/-- info: 'ECA.FiniteConfiguration.pairFreeLe_diam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.pairFreeLe_diam

/-- info: 'ECA.avoids_finRule_wolfram202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.avoids_finRule_wolfram202

/-- info: 'ECA.pairFreeLe_finRule_wolfram202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.pairFreeLe_finRule_wolfram202

/-- info: 'ECA.avoids_finRule_wolfram216' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.avoids_finRule_wolfram216

/-- info: 'ECA.pairFreeLe_finRule_wolfram216' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.pairFreeLe_finRule_wolfram216

/-- info: 'ECA.not_reproduces_gapClassD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_gapClassD

/-- info: 'ECA.pairFreeLe_finRule_wolfram202_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.pairFreeLe_finRule_wolfram202_nonvacuous
