module

public import ECA.BlockCode
public import ECA.Rule146AsRule18

/-!
# Conserved sliding block codes transferred from rule `18` to tables `146` and `126`

A quiescent table **clears windows** when every finite configuration's cells on an interval extend
to a finite configuration whose orbit reads zeros on that interval at some time, and **conserves
no code but zero** when every sliding block code, of any window, that a step leaves unchanged at
every finite configuration has the zero local rule. A table that clears windows conserves no code
but zero, since a conserved code read at a window that the orbit has cleared reads the zero
window. For rule `18` clearing windows is the content of the argument of Sabrié and Törmä (2023)
for their Theorem 15, read for finite configurations; it is taken here as a named hypothesis.

Two other tables reduce to rule `18`. Table `146` differs from rule `18` only at the neighbourhood
`111`, a run of three adjacent set cells needs a run of five in the step before, so a finite
configuration has no three adjacent set cells after as many steps as it has set cells, and from
there table `146` is rule `18`. Table `126` is carried onto rule `18` by taking differences of
neighbouring cells, and a code it conserves takes one value on a window and its complement, so it
is a code of the differences, which rule `18` conserves.

## Main results

* `LocalRule.ClearsWindows` and `LocalRule.ConservesNoCode` — the two predicates.
* `LocalRule.ClearsWindows.conservesNoCode` — a table that clears windows conserves no code but
  zero.
* `conservesNoCode_f146` — rule `18` clearing windows gives table `146` conserving no code but
  zero.
* `conservesNoCode_f126` — rule `18` conserving no code but zero gives the same for table `126`.
* `conservesNoCode_f18_f146_f126` — rule `18` clearing windows gives the three tables conserving
  no code but zero.
* `clearsWindows_wolframRule_zero` and `not_clearsWindows_f206` — the hypothesis is neither empty
  nor universal: the zero table clears every window, and table `206`, which conserves a code that
  is not zero, clears none.
-/

@[expose] public section

namespace ECA

/-- A quiescent table **clears windows** when every finite configuration's cells on an interval
extend to a finite configuration whose orbit reads zeros on that interval at some time. -/
def LocalRule.ClearsWindows (f : LocalRule) (hq : f 0 0 0 = 0) : Prop :=
  ∀ (a b : ℤ) (x : FiniteConfiguration), ∃ z : FiniteConfiguration,
    (∀ i, a ≤ i → i ≤ b → z i = x i) ∧
      ∃ k : ℕ, ∀ i, a ≤ i → i ≤ b → (LocalRule.finRule f hq)^[k] z i = 0

/-- A quiescent table **conserves no code but zero** when every sliding block code, of any window,
that a step leaves unchanged at every finite configuration has the zero local rule. -/
def LocalRule.ConservesNoCode (f : LocalRule) (hq : f 0 0 0 = 0) : Prop :=
  ∀ (L : ℕ) (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0),
    (∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s) → g = 0

/-! ## Windows as finite configurations -/

/-- The finite configuration holding the window `u` on the cells `0` to `n - 1` and zeros
elsewhere. -/
private noncomputable def windowConfig (n : ℕ) (u : Fin n → ZMod 2) : FiniteConfiguration :=
  Finsupp.onFinset (Finset.Ico (0 : ℤ) n)
    (fun i => if h : 0 ≤ i ∧ i < n then u ⟨i.toNat, by omega⟩ else 0) (by
      intro i hi
      by_contra hcon
      apply hi
      rw [Finset.mem_Ico] at hcon
      simp [hcon])

private theorem windowConfig_apply (n : ℕ) (u : Fin n → ZMod 2) (i : ℤ) (j : ℕ) (hj : j < n)
    (h : i = (j : ℤ)) : windowConfig n u i = u ⟨j, hj⟩ := by
  subst h
  have h1 : 0 ≤ (j : ℤ) ∧ (j : ℤ) < n := by omega
  simp [windowConfig, h1]

/-- A sliding block code that one step conserves is conserved by any number of steps. -/
private theorem blockCode_iterate_conserved (f : LocalRule) (hq : f 0 0 0 = 0) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s)
    (t : ℕ) (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode L g hg ((LocalRule.finRule f hq)^[t] s) =
      FiniteConfiguration.blockCode L g hg s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', hcons, ih]

/-- The code of a finite configuration at the cell `0` is `g` of the window of its cells there. -/
private theorem blockCode_zero_apply (L : ℕ) (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode L g hg s 0 = g (fun k : Fin L => s (k : ℕ)) := by
  rw [FiniteConfiguration.blockCode_apply]
  congr 1
  funext k
  rw [zero_add]

/-- A conserved code takes the same value on the step's image of any window of `L + 2` cells and
on its middle `L` cells. -/
private theorem local_of_conserved (f : LocalRule) (hq : f 0 0 0 = 0) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s)
    (u : Fin (L + 2) → ZMod 2) :
    g (fun k : Fin L => f (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩) (u ⟨k + 2, by omega⟩)) =
      g (fun k : Fin L => u ⟨k + 1, by omega⟩) := by
  have h1 := congrArg (fun y : FiniteConfiguration => y 1) (hcons (windowConfig (L + 2) u))
  simp only [FiniteConfiguration.blockCode_apply] at h1
  have e1 : (fun k : Fin L => LocalRule.finRule f hq (windowConfig (L + 2) u) (1 + (k : ℕ))) =
      fun k : Fin L => f (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩) (u ⟨k + 2, by omega⟩) := by
    funext k
    have hk := k.2
    rw [LocalRule.finRule_apply, windowConfig_apply (L + 2) u _ k (by omega) (by ring),
      windowConfig_apply (L + 2) u _ (k + 1) (by omega) (by push_cast; ring),
      windowConfig_apply (L + 2) u _ (k + 2) (by omega) (by push_cast; ring)]
  have e2 : (fun k : Fin L => windowConfig (L + 2) u (1 + (k : ℕ))) =
      fun k : Fin L => u ⟨k + 1, by omega⟩ := by
    funext k
    have hk := k.2
    rw [windowConfig_apply (L + 2) u _ (k + 1) (by omega) (by push_cast; ring)]
  rw [e1, e2] at h1
  exact h1

/-! ## A table that clears windows -/

/-- **A table that clears windows conserves no code but zero**: a conserved code read at the
window the orbit has cleared is the code of the zero window. -/
theorem LocalRule.ClearsWindows.conservesNoCode {f : LocalRule} {hq : f 0 0 0 = 0}
    (h : f.ClearsWindows hq) : f.ConservesNoCode hq := by
  intro L g hg hcons
  funext q
  obtain ⟨z, hz, k, hk⟩ := h 0 ((L : ℤ) - 1) (windowConfig L q)
  have h1 := congrArg (fun y : FiniteConfiguration => y 0)
    (blockCode_iterate_conserved f hq g hg hcons k z)
  simp only [blockCode_zero_apply] at h1
  have e1 : (fun j : Fin L => z (j : ℕ)) = q := by
    funext j
    have hj := j.2
    rw [hz _ (by omega) (by omega), windowConfig_apply L q _ j hj (by simp)]
  have e2 : (fun j : Fin L => (LocalRule.finRule f hq)^[k] z (j : ℕ)) = 0 := by
    funext j
    have hj := j.2
    exact hk _ (by omega) (by omega)
  rw [e1, e2, hg] at h1
  exact h1.symm

/-! ## Table `146` -/

/-- Three adjacent set cells in a step of table `146` need five adjacent set cells before it. -/
private theorem run_of_finRule_f146 (y : FiniteConfiguration) (i : ℤ)
    (h0 : LocalRule.finRule f146 hq146 y i = 1)
    (h1 : LocalRule.finRule f146 hq146 y (i + 1) = 1)
    (h2 : LocalRule.finRule f146 hq146 y (i + 2) = 1) :
    y (i - 1) = 1 ∧ y i = 1 ∧ y (i + 1) = 1 ∧ y (i + 2) = 1 ∧ y (i + 3) = 1 := by
  rw [LocalRule.finRule_apply] at h0 h1 h2
  have e1 : i + 1 - 1 = i := by ring
  have e2 : i + 2 - 1 = i + 1 := by ring
  have e3 : i + 1 + 1 = i + 2 := by ring
  have e4 : i + 2 + 1 = i + 3 := by ring
  rw [e1, e3] at h1
  rw [e2, e4] at h2
  revert h0 h1 h2
  generalize y (i - 1) = a
  generalize y i = b
  generalize y (i + 1) = c
  generalize y (i + 2) = d
  generalize y (i + 3) = e
  revert a b c d e
  simp only [f146]
  decide

/-- Three adjacent set cells after `n` steps of table `146` need `2 * n + 3` adjacent set cells at
the start. -/
private theorem ones_of_iterate_f146 (n : ℕ) : ∀ (s : FiniteConfiguration) (i : ℤ),
    (LocalRule.finRule f146 hq146)^[n] s i = 1 → (LocalRule.finRule f146 hq146)^[n] s (i + 1) = 1 →
      (LocalRule.finRule f146 hq146)^[n] s (i + 2) = 1 →
        ∀ j, i - n ≤ j → j ≤ i + 2 + n → s j = 1 := by
  induction n with
  | zero =>
    intro s i h0 h1 h2 j hj1 hj2
    simp only [Function.iterate_zero, id_eq] at h0 h1 h2
    have : j = i ∨ j = i + 1 ∨ j = i + 2 := by push_cast at hj1 hj2; omega
    rcases this with rfl | rfl | rfl <;> assumption
  | succ n ih =>
    intro s i h0 h1 h2 j hj1 hj2
    rw [Function.iterate_succ_apply'] at h0 h1 h2
    obtain ⟨a, b, c, d, e⟩ := run_of_finRule_f146 _ i h0 h1 h2
    have hL := ih s (i - 1) a (by rwa [show i - 1 + 1 = i by ring])
      (by rwa [show i - 1 + 2 = i + 1 by ring])
    have hR := ih s (i + 1) c (by rwa [show i + 1 + 1 = i + 2 by ring])
      (by rwa [show i + 1 + 2 = i + 3 by ring])
    push_cast at hj1 hj2
    by_cases hc : j ≤ i - 1 + 2 + n
    · exact hL j (by omega) hc
    · exact hR j (by omega) (by omega)

/-- A finite configuration has no three adjacent set cells after as many steps of table `146` as
it has set cells. -/
private theorem noThreeAdjacentOnes_iterate_f146 (x : FiniteConfiguration) :
    NoThreeAdjacentOnes ((LocalRule.finRule f146 hq146)^[x.support.card] x) := by
  intro i
  by_contra hcon
  push Not at hcon
  have one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hrun := ones_of_iterate_f146 x.support.card x (i - 1) (one _ hcon.1)
    (by rw [show i - 1 + 1 = i by ring]; exact one _ hcon.2.1)
    (by rw [show i - 1 + 2 = i + 1 by ring]; exact one _ hcon.2.2)
  have hsub : Finset.Icc (i - 1 - (x.support.card : ℤ)) (i - 1 + 2 + (x.support.card : ℤ)) ⊆
      x.support := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finsupp.mem_support_iff, hrun j hj.1 hj.2]
    exact one_ne_zero
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  omega

/-- **Rule `18` clearing windows gives table `146` conserving no code but zero**: from a window
and a step count past which the orbit of table `146` has no three adjacent set cells, table `146`
is rule `18`. -/
theorem conservesNoCode_f146 (h : LocalRule.ClearsWindows f18 hq18) :
    LocalRule.ConservesNoCode f146 hq146 := by
  intro L g hg hcons
  funext q
  have hx0 : g q = FiniteConfiguration.blockCode L g hg (windowConfig L q) 0 := by
    rw [blockCode_zero_apply]
    congr 1
    funext j
    exact (windowConfig_apply L q _ j j.2 (by simp)).symm
  set y := (LocalRule.finRule f146 hq146)^[(windowConfig L q).support.card] (windowConfig L q)
    with hy
  have hno : NoThreeAdjacentOnes y := noThreeAdjacentOnes_iterate_f146 _
  have hxy : FiniteConfiguration.blockCode L g hg y (0 : ℤ) =
      FiniteConfiguration.blockCode L g hg (windowConfig L q) 0 :=
    congrArg (fun w : FiniteConfiguration => w 0)
      (blockCode_iterate_conserved f146 hq146 g hg hcons _ _)
  obtain ⟨z', hz', k, hk⟩ := h (-1) (L : ℤ) y
  cases k with
  | zero =>
    have e : (fun j : Fin L => y (j : ℕ)) = 0 := by
      funext j
      have hj := j.2
      rw [← hz' _ (by omega) (by omega)]
      exact hk _ (by omega) (by omega)
    rw [hx0, ← hxy, blockCode_zero_apply, e, hg]
    rfl
  | succ k =>
    set z := LocalRule.finRule f18 hq18 z' with hz
    have hA : ∀ i : ℤ, 0 ≤ i → i < L → LocalRule.finRule f146 hq146 y i = z i := by
      intro i hi0 hiL
      rw [finRule_f146_eq_f18_of_noThreeAdjacentOnes y hno, hz, LocalRule.finRule_apply,
        LocalRule.finRule_apply, hz' (i - 1) (by omega) (by omega), hz' i (by omega) (by omega),
        hz' (i + 1) (by omega) (by omega)]
    have hB : NoThreeAdjacentOnes z := noThreeAdjacentOnes_finRule_f18 z'
    have hC := iterate_f146_eq_f18_of_noThreeAdjacentOnes z hB k
    have hD : ∀ j : Fin L, (LocalRule.finRule f146 hq146)^[k] z (j : ℕ) = 0 := by
      intro j
      have hj := j.2
      rw [hC, hz, ← Function.iterate_succ_apply (LocalRule.finRule f18 hq18) k z']
      exact hk _ (by omega) (by omega)
    have hE := congrArg (fun w : FiniteConfiguration => w 0)
      (blockCode_iterate_conserved f146 hq146 g hg hcons k z)
    have hF := congrArg (fun w : FiniteConfiguration => w 0) (hcons y)
    simp only [blockCode_zero_apply] at hE hF
    have e1 : (fun j : Fin L => (LocalRule.finRule f146 hq146)^[k] z (j : ℕ)) = 0 := by
      funext j
      exact hD j
    have e2 : (fun j : Fin L => LocalRule.finRule f146 hq146 y (j : ℕ)) =
        fun j : Fin L => z (j : ℕ) := by
      funext j
      have hj := j.2
      exact hA _ (by omega) (by omega)
    rw [e1, hg] at hE
    rw [e2] at hF
    rw [hx0, ← hxy, blockCode_zero_apply, ← hF, ← hE]
    rfl

/-! ## Table `126` -/

/-- Table `126` takes the same value on a neighbourhood and on its complement. -/
private theorem f126_complement :
    ∀ a b c : ZMod 2, f126 (a + 1) (b + 1) (c + 1) = f126 a b c := by decide

/-- The differences of two neighbouring images of table `126` are rule `18` of the differences. -/
private theorem f126_difference :
    ∀ a b c d : ZMod 2, f126 a b c + f126 b c d = f18 (a + b) (b + c) (c + d) := by decide

private theorem zmod2_self : ∀ a : ZMod 2, a + a = 0 := by decide

/-- A cell of `ZMod 2` added twice is undone. -/
private theorem zmod2_cancel : ∀ a b : ZMod 2, a + (a + b) = b := by decide

/-- The window of `M` differences of a window of `M + 1` cells. -/
private def diffWin {M : ℕ} (v : Fin (M + 1) → ZMod 2) : Fin M → ZMod 2 :=
  fun j => v ⟨j, by omega⟩ + v ⟨j + 1, by omega⟩

/-- The window of `n + 1` cells with first cell `0` and the given differences. -/
private def cumWin {n : ℕ} (w : Fin n → ZMod 2) : Fin (n + 1) → ZMod 2 :=
  fun k => ∑ j ∈ Finset.range k, if h : j < n then w ⟨j, h⟩ else 0

private theorem cumWin_succ {n : ℕ} (w : Fin n → ZMod 2) (j : ℕ) (hj : j < n) :
    cumWin w ⟨j + 1, by omega⟩ = cumWin w ⟨j, by omega⟩ + w ⟨j, hj⟩ := by
  simp only [cumWin, Finset.sum_range_succ, hj, dite_true]

private theorem cumWin_zero {n : ℕ} : cumWin (0 : Fin n → ZMod 2) = 0 := by
  funext k
  simp [cumWin]

private theorem cumWin_diffWin {M : ℕ} (v : Fin (M + 1) → ZMod 2) :
    ∀ (k : ℕ) (hk : k < M + 1), cumWin (diffWin v) ⟨k, hk⟩ = v ⟨0, by omega⟩ + v ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    simp only [cumWin, Finset.range_zero, Finset.sum_empty]
    exact (zmod2_self _).symm
  | succ k ih =>
    intro hk
    rw [cumWin_succ _ k (by omega), ih (by omega)]
    simp only [diffWin]
    generalize v ⟨0, by omega⟩ = a
    generalize v ⟨k, by omega⟩ = b
    generalize v ⟨k + 1, hk⟩ = c
    revert a b c
    decide

private theorem diffWin_cumWin {M : ℕ} (w : Fin M → ZMod 2) : diffWin (cumWin w) = w := by
  funext j
  simp only [diffWin]
  rw [cumWin_succ w j j.2]
  exact zmod2_cancel _ _

/-- **Rule `18` conserving no code but zero gives table `126` conserving no code but zero**: a
code table `126` conserves is a code of the differences, and rule `18` conserves it. -/
theorem conservesNoCode_f126 (h : LocalRule.ConservesNoCode f18 hq18) :
    LocalRule.ConservesNoCode f126 hq126 := by
  intro L g hg hcons
  have hloc := local_of_conserved f126 hq126 g hg hcons
  cases L with
  | zero =>
    funext q
    have : q = 0 := funext fun i => i.elim0
    rw [this]
    exact hg
  | succ M =>
    have zmod2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    -- the code takes one value on a window and on its complement
    have hcomp : ∀ v : Fin (M + 1) → ZMod 2, g (fun k => v k + 1) = g v := by
      intro v
      let u : Fin (M + 1 + 2) → ZMod 2 :=
        fun j => if hj : 1 ≤ j.val ∧ j.val ≤ M + 1 then v ⟨j.val - 1, by omega⟩ else 0
      have hm : ∀ k : Fin (M + 1), u ⟨k + 1, by omega⟩ = v k := by
        intro k
        have hk := k.2
        have h1 : 1 ≤ (k : ℕ) + 1 ∧ (k : ℕ) + 1 ≤ M + 1 := by omega
        simp only [u, h1, and_self, dite_true]
        congr 1
      have h1 := hloc u
      have h2 := hloc (fun j => u j + 1)
      have himg : (fun k : Fin (M + 1) => f126 (u ⟨k, by omega⟩ + 1) (u ⟨k + 1, by omega⟩ + 1)
          (u ⟨k + 2, by omega⟩ + 1)) =
          fun k : Fin (M + 1) => f126 (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩)
            (u ⟨k + 2, by omega⟩) := by
        funext k
        exact f126_complement _ _ _
      have hmid : (fun k : Fin (M + 1) => u ⟨k + 1, by omega⟩) = v := funext hm
      have hmid' : (fun k : Fin (M + 1) => u ⟨k + 1, by omega⟩ + 1) = fun k => v k + 1 := by
        funext k
        rw [hm]
      rw [himg, h1, hmid, hmid'] at h2
      exact h2.symm
    -- the code is a function of the differences
    obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin M → ZMod 2) → ZMod 2, ∀ w, ρ w = g (cumWin w) :=
      ⟨_, fun _ => rfl⟩
    have hdiff : ∀ v : Fin (M + 1) → ZMod 2, g v = ρ (diffWin v) := by
      intro v
      rw [hρ]
      have hc : cumWin (diffWin v) = fun k => v ⟨0, by omega⟩ + v k := by
        funext k
        exact cumWin_diffWin v k k.2
      rcases zmod2 (v ⟨0, by omega⟩) with h0 | h0
      · have : (fun k => v ⟨0, by omega⟩ + v k) = v := by
          funext k
          rw [h0, zero_add]
        rw [hc, this]
      · have : (fun k => v ⟨0, by omega⟩ + v k) = fun k => v k + 1 := by
          funext k
          rw [h0, add_comm]
        rw [hc, this, hcomp]
    have hρ0 : ρ 0 = 0 := by
      rw [hρ, cumWin_zero]
      exact hg
    -- the code of the differences meets rule `18`'s local identity
    have hloc18 : ∀ u' : Fin (M + 2) → ZMod 2,
        ρ (fun k : Fin M => f18 (u' ⟨k, by omega⟩) (u' ⟨k + 1, by omega⟩)
          (u' ⟨k + 2, by omega⟩)) = ρ (fun k : Fin M => u' ⟨k + 1, by omega⟩) := by
      intro u'
      have hd : ∀ (j : ℕ) (hj : j < M + 2),
          cumWin u' ⟨j, by omega⟩ + cumWin u' ⟨j + 1, by omega⟩ = u' ⟨j, hj⟩ := fun j hj =>
        congrFun (diffWin_cumWin u') ⟨j, hj⟩
      have h1 := hloc (cumWin u')
      have hR : diffWin (fun k : Fin (M + 1) => f126 (cumWin u' ⟨k, by omega⟩)
          (cumWin u' ⟨k + 1, by omega⟩) (cumWin u' ⟨k + 2, by omega⟩)) =
          fun k : Fin M => f18 (u' ⟨k, by omega⟩) (u' ⟨k + 1, by omega⟩)
            (u' ⟨k + 2, by omega⟩) := by
        funext k
        refine (f126_difference _ _ _ _).trans ?_
        exact congr (congr (congrArg f18 (hd _ _)) (hd _ _)) (hd _ _)
      have hL : diffWin (fun k : Fin (M + 1) => cumWin u' ⟨k + 1, by omega⟩) =
          fun k : Fin M => u' ⟨k + 1, by omega⟩ := by
        funext k
        exact hd (k + 1) (by omega)
      calc ρ (fun k : Fin M => f18 (u' ⟨k, by omega⟩) (u' ⟨k + 1, by omega⟩)
              (u' ⟨k + 2, by omega⟩))
          = ρ (diffWin (fun k : Fin (M + 1) => f126 (cumWin u' ⟨k, by omega⟩)
              (cumWin u' ⟨k + 1, by omega⟩) (cumWin u' ⟨k + 2, by omega⟩))) := by rw [hR]
        _ = g (fun k : Fin (M + 1) => f126 (cumWin u' ⟨k, by omega⟩)
              (cumWin u' ⟨k + 1, by omega⟩) (cumWin u' ⟨k + 2, by omega⟩)) := (hdiff _).symm
        _ = g (fun k : Fin (M + 1) => cumWin u' ⟨k + 1, by omega⟩) := h1
        _ = ρ (diffWin (fun k : Fin (M + 1) => cumWin u' ⟨k + 1, by omega⟩)) := hdiff _
        _ = ρ (fun k : Fin M => u' ⟨k + 1, by omega⟩) := by rw [hL]
    have hzero : ρ = 0 :=
      h M ρ hρ0 (LocalRule.blockCode_finRule f18 hq18 ρ hρ0 hloc18)
    funext v
    change g v = 0
    rw [hdiff v, hzero]
    rfl

/-! ## The three tables, and the hypothesis -/

/-- **Rule `18` clearing windows gives rule `18`, table `146` and table `126` conserving no code
but zero.** -/
theorem conservesNoCode_f18_f146_f126 (h : LocalRule.ClearsWindows f18 hq18) :
    LocalRule.ConservesNoCode f18 hq18 ∧ LocalRule.ConservesNoCode f146 hq146 ∧
      LocalRule.ConservesNoCode f126 hq126 :=
  ⟨h.conservesNoCode, conservesNoCode_f146 h, conservesNoCode_f126 h.conservesNoCode⟩

/-- Every neighbourhood goes to `0` at the zero table. -/
private theorem wolframRule_zero_apply : ∀ a b c : ZMod 2, wolframRule 0 a b c = 0 := by decide

/-- **The hypothesis is not empty**: the zero table clears every window, in one step. -/
theorem clearsWindows_wolframRule_zero :
    LocalRule.ClearsWindows (wolframRule 0) (by decide) := by
  intro a b x
  refine ⟨x, fun _ _ _ => rfl, 1, fun i _ _ => ?_⟩
  rw [Function.iterate_one, LocalRule.finRule_apply]
  exact wolframRule_zero_apply _ _ _

/-- **The hypothesis is not universal**: table `206` conserves a code that is not zero, so it
clears no window. -/
theorem not_clearsWindows_f206 : ¬ LocalRule.ClearsWindows f206 hq206 := by
  intro h
  have h0 := h.conservesNoCode 2 codeF206 codeF206_zero blockCode_finRule_f206
  have h1 : codeF206 ![1, 0] = 0 := congrFun h0 _
  revert h1
  decide

end ECA

/-- info:
'ECA.LocalRule.ClearsWindows.conservesNoCode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.ClearsWindows.conservesNoCode

/-- info:
'ECA.conservesNoCode_f146' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f146

/-- info:
'ECA.conservesNoCode_f126' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f126

/-- info:
'ECA.conservesNoCode_f18_f146_f126' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f18_f146_f126

/-- info:
'ECA.clearsWindows_wolframRule_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.clearsWindows_wolframRule_zero

/-- info:
'ECA.not_clearsWindows_f206' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_clearsWindows_f206
