/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.ParityEmulation
public import CellularAutomata.Doubling
public import CellularAutomata.BlockCount
-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The replication bracket over the quiescent radius-one tables
([RuleSpace] §3 and §5; rows RS-27 and RS-28 for the tables that host themselves)

A state of the line is a finitely supported map `ℤ →₀ ZMod 2`, and a radius-one table with a
quiescent zero cell steps it through `tableRule`. A pattern `p` is nonzero; a state is `k`
copies of `p` at gap `G` when it is the sum of `k` translates of `p` whose offsets are at least
`diam p + G` apart (so the translates have disjoint supports and `G` clear cells sit between
neighbouring copies). A map `U` replicates `p` when for every bound `N` and gap `G` some
iterate of `U` at `p` is at least `N` copies at gap `G`.

The bracket sits on the diameter classes of [RuleSpace] §3: at the seventy-four quiescent tables
outside the fifty-four accreting ones (`AccretesByEndpoints`, with tables `106` and `120`) every
orbit has bounded diameter, and a map of bounded diameter replicates no pattern. The other half,
that each of fourteen tables replicates some pattern, is the parent theorem's third hypothesis
and is proved below by three mechanisms, so the bracket stands unconditionally.

## Main results

* `Copies` / `Replicates` / `DiamBounded` — the three notions; `ReplicatesExactly` is the
  exact-count reading, kept as the guards' object.
* `fourteen` — the fourteen tables, among them the six defined here (`f26`, `f60`, `f82`, `f102`,
  `f146`, `f218`).
* `replication_bracket` — **the parent**, from three hypotheses: bounded diameter forbids
  replication (`NotReplicatesOfDiamBounded`), the seventy-four tables outside the accreting
  fifty-four have bounded diameter (`DiamBoundedOfNotAccreting`), and each of the fourteen
  replicates a pattern (`ReplicatesOfMemFourteen`).
* `fourteen_subset_accreting` — the lower half is not vacuous: all fourteen are accreting.
* `copies_diam_le` / `not_replicates_of_diamBounded` — **the first hypothesis, proved**: `k`
  copies of a nonzero pattern have diameter at least `k` times the pattern's.
* `classify_outside_accreting` / `diamBounded_of_zeroByEndpoints` / `diamBounded_of_not_accreting`
  — **the second hypothesis, proved**: the seventy-four are the forty-eight of `ZeroByEndpoints`
  and twenty-six tables each decided by a landed diameter bound, thirteen and their mirrors.
* `not_copies_three_of_twoTap` / `not_copies_three_f90_single` / `not_copies_three_f60_single` /
  `not_replicates_single_f90_f60` — **guards**: from a single cell no iterate of table `60` or
  `90` is exactly three copies of it, so the exact count of `ReplicatesExactly` fails at those
  two tables, the translate-sum identities reaching only powers of two.
* `replicates_of_linear` / `replicates_of_agreesOffAdjacent` / `replicates_of_doubledAgree` —
  **the third hypothesis, proved**, by three mechanisms: the squaring identity of the linear
  tables `60`, `90`, `102`, `150`; the doubling identity of table `90` over one-parity states at
  the seven tables agreeing with it off adjacent cells; and the doubling of table `90`'s
  orbits at the tables agreeing with it at equal adjacent cells. `replicates_of_mem_fourteen`
  collects the fourteen instances.
-/

@[expose] public section

namespace ReplicationBracket

open ExtremeTapWidth EndpointClasses LightConeWidth

/-! ## Piece 1: the notions, the tables, and the bracket -/

/-- **`k` copies of a pattern at gap `G`**: `s` is the sum of `k` translates of `p` whose offsets
are at least `diam p + G` apart, so the supports are pairwise disjoint with `G` clear cells
between neighbours. -/
def Copies (p s : ℤ →₀ ZMod 2) (k : ℕ) (G : ℕ) : Prop :=
  ∃ c : ℕ → ℤ, (∀ j, j + 1 < k → c j + diam p + G ≤ c (j + 1)) ∧
    s = (Finset.range k).sum fun j => EndpointClasses.translate (c j) p

/-- **`U` replicates `p` with exact counts**: `p` is nonzero, and for every `k` and `G` some
iterate is exactly `k` copies at gap `G`; the reading refuted at the linear tables, kept as the
guards' object. -/
def ReplicatesExactly (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (p : ℤ →₀ ZMod 2) : Prop :=
  p ≠ 0 ∧ ∀ k G : ℕ, ∃ t, Copies p (U^[t] p) k G

/-- **`U` replicates `p`**: `p` is nonzero, and for every bound `N` and gap `G` some iterate of
`U` at `p` is at least `N` copies of `p` at gap `G`. -/
def Replicates (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (p : ℤ →₀ ZMod 2) : Prop :=
  p ≠ 0 ∧ ∀ N G : ℕ, ∃ t k, N ≤ k ∧ Copies p (U^[t] p) k G

/-- **Bounded diameter**: along every orbit the support diameter stays below a bound that may
depend on the start. -/
def DiamBounded (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) : Prop :=
  ∀ s, ∃ c, ∀ t, diam (U^[t] s) ≤ c

/-- Table `26` (Wolfram's number): `c + a + a * b + a * b * c`, with `a` the left neighbour. -/
def f26 (a b c : ZMod 2) : ZMod 2 := c + a + a * b + a * b * c

/-- Table `60`: the sum of the left neighbour and the cell itself. -/
def f60 (a b _c : ZMod 2) : ZMod 2 := a + b

/-- Table `82`, the mirror of table `26`: `c + b * c + a + a * b * c`. -/
def f82 (a b c : ZMod 2) : ZMod 2 := c + b * c + a + a * b * c

/-- Table `102`, the mirror of table `60`: the sum of the cell itself and the right neighbour. -/
def f102 (_a b c : ZMod 2) : ZMod 2 := b + c

/-- Table `146`: `c + b * c + a + a * b + a * b * c`. -/
def f146 (a b c : ZMod 2) : ZMod 2 := c + b * c + a + a * b + a * b * c

/-- Table `218`: `c + a + a * b * c`. -/
def f218 (a b c : ZMod 2) : ZMod 2 := c + a + a * b * c

/-- Table `120`, the mirror of table `106`: `b * c + a`. -/
def f120 (a b c : ZMod 2) : ZMod 2 := b * c + a

/-- Table `26` is quiescent. -/
theorem hq26 : f26 0 0 0 = 0 := by decide
/-- Table `60` is quiescent. -/
theorem hq60 : f60 0 0 0 = 0 := by decide
/-- Table `82` is quiescent. -/
theorem hq82 : f82 0 0 0 = 0 := by decide
/-- Table `102` is quiescent. -/
theorem hq102 : f102 0 0 0 = 0 := by decide
/-- Table `146` is quiescent. -/
theorem hq146 : f146 0 0 0 = 0 := by decide
/-- Table `218` is quiescent. -/
theorem hq218 : f218 0 0 0 = 0 := by decide
/-- Table `120` is quiescent. -/
theorem hq120 : f120 0 0 0 = 0 := by decide

/-- The six new tables and table `120` are the tables of their Wolfram numbers. -/
theorem new_tables_eq_wolframTable :
    (∀ a b c, f26 a b c = Doubling.wolframTable 26 a b c) ∧
      (∀ a b c, f60 a b c = Doubling.wolframTable 60 a b c) ∧
      (∀ a b c, f82 a b c = Doubling.wolframTable 82 a b c) ∧
      (∀ a b c, f102 a b c = Doubling.wolframTable 102 a b c) ∧
      (∀ a b c, f146 a b c = Doubling.wolframTable 146 a b c) ∧
      (∀ a b c, f218 a b c = Doubling.wolframTable 218 a b c) ∧
      (∀ a b c, f120 a b c = Doubling.wolframTable 120 a b c) := by
  decide

/-- Table `120` is the mirror of table `106`. -/
theorem f120_eq_mirrorTable_f106 :
    ∀ a b c, f120 a b c = OneTapWidth.mirrorTable OneTapWidth.f106 a b c := by
  decide

/-- **The fourteen tables**: Wolfram numbers `18`, `26`, `60`, `82`, `90`, `94`, `102`, `122`,
`126`, `146`, `150`, `154`, `210`, `218`. -/
def fourteen : List (ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) :=
  [ParityEmulation.f18, f26, f60, f82, EndpointClasses.f90, Doubling.f94, f102, Doubling.f122,
    Doubling.f126, f146, EndpointClasses.f150, ExtremeTapWidth.f154, ExtremeTapWidth.f210, f218]

/-- **Leaf: bounded diameter forbids replication.** -/
def NotReplicatesOfDiamBounded : Prop :=
  ∀ (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)), DiamBounded U → ∀ p, ¬ Replicates U p

/-- **Leaf: outside the fifty-four accreting tables every orbit has bounded diameter.** -/
def DiamBoundedOfNotAccreting : Prop :=
  ∀ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0),
    ¬ (AccretesByEndpoints f ∨ f = OneTapWidth.f106 ∨ f = f120) → DiamBounded (tableRule f hq)

/-- **Leaf: each of the fourteen tables replicates a pattern.** -/
def ReplicatesOfMemFourteen : Prop :=
  ∀ f (hq : f 0 0 0 = 0), f ∈ fourteen → ∃ p, Replicates (tableRule f hq) p

/-- **The replication bracket**: the fourteen tables replicate a pattern, and no table outside
the accreting fifty-four does. -/
theorem replication_bracket (h1 : NotReplicatesOfDiamBounded) (h2 : DiamBoundedOfNotAccreting)
    (h3 : ReplicatesOfMemFourteen) (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) :
    (f ∈ fourteen → ∃ p, Replicates (tableRule f hq) p) ∧
    (¬ (AccretesByEndpoints f ∨ f = OneTapWidth.f106 ∨ f = f120) →
      ∀ p, ¬ Replicates (tableRule f hq) p) :=
  ⟨h3 f hq, fun h p => h1 _ (h2 f hq h) p⟩

/-- **The lower half is not vacuous**: every one of the fourteen tables accretes. -/
theorem fourteen_subset_accreting : ∀ f ∈ fourteen, AccretesByEndpoints f := by
  intro f hf
  simp only [fourteen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
    unfold AccretesByEndpoints <;> decide

/-! ## Piece 2 (a): bounded diameter forbids replication -/

private theorem translate_apply' (i : ℤ) (p : ℤ →₀ ZMod 2) (x : ℤ) :
    EndpointClasses.translate i p x = p (x - i) := by
  have h := Finsupp.mapDomain_apply_of_injective (add_left_injective i) p (x - i)
  rw [sub_add_cancel] at h
  exact h

private theorem le_diam_of_cells {s : ℤ →₀ ZMod 2} {a b : ℤ} (ha : s a ≠ 0)
    (hb : s b ≠ 0) : (b - a).toNat + 1 ≤ diam s := by
  have hne : s.support.Nonempty := ⟨a, Finsupp.mem_support_iff.mpr ha⟩
  have h1 := Finset.min'_le s.support a (Finsupp.mem_support_iff.mpr ha)
  have h2 := Finset.le_max' s.support b (Finsupp.mem_support_iff.mpr hb)
  unfold diam
  rw [dite_eq_left hne]
  omega

private theorem offsets_mono {c : ℕ → ℤ} {k G d : ℕ}
    (hc : ∀ j, j + 1 < k → c j + d + G ≤ c (j + 1)) :
    ∀ n j, j + n < k → c j + n * d ≤ c (j + n) := by
  intro n
  induction n with
  | zero => intro j _; simp
  | succ n ih =>
    intro j hj
    have h1 := ih j (by omega)
    have h2 := hc (j + n) (by omega)
    rw [← add_assoc]
    push_cast
    nlinarith

/-- **`k` copies of a nonzero pattern have diameter at least `k` times the pattern's**: the
leftmost cell of the first copy and the rightmost cell of the last copy are both set, and the
offsets are at least the pattern's diameter apart. -/
theorem copies_diam_le {p s : ℤ →₀ ZMod 2} {k G : ℕ} (hp : p ≠ 0) (h : Copies p s k G)
    (hk : 1 ≤ k) : k * diam p ≤ diam s := by
  obtain ⟨c, hc, rfl⟩ := h
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmM := Finset.min'_le_max' p.support hpne
  have hdiam : (diam p : ℤ) = p.support.max' hpne - p.support.min' hpne + 1 := by
    unfold diam
    rw [dite_eq_left hpne]
    have : (0 : ℤ) ≤ p.support.max' hpne - p.support.min' hpne := by omega
    omega
  have hlow : ∀ y, y < p.support.min' hpne → p y = 0 := fun y hy => by
    by_contra hne
    have := Finset.min'_le p.support y (Finsupp.mem_support_iff.mpr hne)
    omega
  have hhigh : ∀ y, p.support.max' hpne < y → p y = 0 := fun y hy => by
    by_contra hne
    have := Finset.le_max' p.support y (Finsupp.mem_support_iff.mpr hne)
    omega
  have hmem0 : p (p.support.min' hpne) ≠ 0 :=
    Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
  have hmem1 : p (p.support.max' hpne) ≠ 0 :=
    Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hmono := offsets_mono hc
  have hd1 : (1 : ℤ) ≤ diam p := by omega
  have hev : ∀ x, ((Finset.range (k' + 1)).sum fun j => EndpointClasses.translate (c j) p) x =
      (Finset.range (k' + 1)).sum fun j => p (x - c j) := by
    intro x
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun j _ => translate_apply' _ _ _
  have hs0 : ((Finset.range (k' + 1)).sum fun j => EndpointClasses.translate (c j) p)
      (p.support.min' hpne + c 0) ≠ 0 := by
    rw [hev, Finset.sum_eq_single 0]
    · simpa using hmem0
    · intro j hj hj0
      apply hlow
      have := hmono j 0 (by simp at hj; omega)
      have hj1 : (1 : ℤ) ≤ j := by omega
      simp only [zero_add] at this
      nlinarith
    · intro h0; simp at h0
  have hs1 : ((Finset.range (k' + 1)).sum fun j => EndpointClasses.translate (c j) p)
      (p.support.max' hpne + c k') ≠ 0 := by
    rw [hev, Finset.sum_eq_single k']
    · simpa using hmem1
    · intro j hj hjk
      apply hhigh
      have hjlt : j < k' := by simp at hj; omega
      have := hmono (k' - j) j (by omega)
      rw [show j + (k' - j) = k' by omega] at this
      have hj1 : (1 : ℤ) ≤ ((k' - j : ℕ) : ℤ) := by omega
      nlinarith
    · intro h0; simp at h0
  have hfin := hmono k' 0 (by omega)
  simp only [zero_add] at hfin
  have := le_diam_of_cells hs0 hs1
  have h3 : (((p.support.max' hpne + c k') - (p.support.min' hpne + c 0)).toNat : ℤ) =
      (p.support.max' hpne + c k') - (p.support.min' hpne + c 0) := by
    apply Int.toNat_of_nonneg
    have : (0 : ℤ) ≤ k' * diam p := by positivity
    omega
  have key : (k' : ℤ) * diam p + diam p ≤
      diam ((Finset.range (k' + 1)).sum fun j => EndpointClasses.translate (c j) p) := by
    omega
  zify
  linarith

/-- **Leaf (a)**: bounded diameter forbids replication. Take `k` one more than the bound and
`G = 0`. -/
theorem not_replicates_of_diamBounded : NotReplicatesOfDiamBounded := by
  intro U hU p ⟨hp, hrep⟩
  obtain ⟨c, hc⟩ := hU p
  obtain ⟨t, k, hk, ht⟩ := hrep (c + 1) 0
  have h1 := copies_diam_le hp ht (by omega)
  have hd : 1 ≤ diam p := by
    have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
    unfold diam
    rw [dite_eq_left hpne]
    omega
  have h2 := hc t
  nlinarith [Nat.mul_le_mul_right (diam p) hk]

/-! ## Piece 2 (b): outside the accreting tables every orbit has bounded diameter -/

/-- An affine bound along every orbit is a bounded diameter. -/
theorem diamBounded_of_affine {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℕ}
    (h : ∀ (s : ℤ →₀ ZMod 2) (k : ℕ), diam (U^[k] s) ≤ a * diam s + b) : DiamBounded U :=
  fun s => ⟨a * diam s + b, fun t => h s t⟩

/-- A diameter that grows by at most a constant is a bounded diameter. -/
theorem diamBounded_of_diamBoundedBy {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {c : ℕ}
    (h : OneTapWidth.DiamBoundedBy U c) : DiamBounded U :=
  fun s => ⟨diam s + c, fun t => h s t⟩

/-- A non-increasing diameter is a bounded diameter. -/
theorem diamBounded_of_step_le {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (h : ∀ s, diam (U s) ≤ diam s) : DiamBounded U := fun s =>
  ⟨diam s, fun t => by
    induction t with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (h _).trans ih⟩

/-- **The forty-eight tables of `ZeroByEndpoints` have bounded diameter**: the diameter never
grows, by the three one-step lemmas of [RuleSpace] §3 Proposition 3.1(iv) iterated. -/
theorem diamBounded_of_zeroByEndpoints {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    (hq : f 0 0 0 = 0) (hz : ZeroByEndpoints f) : DiamBounded (tableRule f hq) := by
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact diamBounded_of_step_le fun s => diam_tableRule_le_of_noTap (hq := hq) h1 h2 s
  · exact diamBounded_of_step_le fun s =>
      diam_tableRule_le_of_leftTap_rightDies (hq := hq) h1 h2 h3 h4 s
  · exact diamBounded_of_step_le fun s =>
      diam_tableRule_le_of_rightTap_leftDies (hq := hq) h1 h2 h3 h4 s

set_option maxRecDepth 8000 in
set_option synthInstance.maxHeartbeats 400000 in
-- the `Decidable` instance for a universal over 256 tables and 27 disjuncts needs the larger
-- synthesis limits.
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 8000000 in
-- the decision is over 256 tables and 27 disjuncts; the kernel reduction needs the larger
-- recursion and heartbeat limits.
/-- **The seventy-four tables outside the accreting fifty-four**: a quiescent table that is
neither in `AccretesByEndpoints` nor table `106` or `120` is in `ZeroByEndpoints` or is one of
the twenty-six tables [RuleSpace] §3 Propositions 3.2 to 3.7 decide one by one, thirteen tables
and their mirrors. -/
theorem classify_outside_accreting (g : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) :
    g 0 0 0 = 0 → ¬ (AccretesByEndpoints g ∨ (∀ a b c, g a b c = OneTapWidth.f106 a b c) ∨
        (∀ a b c, g a b c = f120 a b c)) →
      ZeroByEndpoints g ∨
        (∀ a b c, g a b c = OneTapWidth.f38 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.f46 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.f66 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.f166 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.f174 a b c) ∨
        (∀ a b c, g a b c = BlockTrainWidth.f6 a b c) ∨
        (∀ a b c, g a b c = BlockTrainWidth.f14 a b c) ∨
        (∀ a b c, g a b c = BlockTrainWidth.f142 a b c) ∨
        (∀ a b c, g a b c = BlockTrainWidth.f134 a b c) ∨
        (∀ a b c, g a b c = BlockTrainWidth.f74 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.f226 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.f194 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.f98 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable OneTapWidth.f38 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable OneTapWidth.f46 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable OneTapWidth.f66 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable OneTapWidth.f166 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable OneTapWidth.f174 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable BlockTrainWidth.f6 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable BlockTrainWidth.f14 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable BlockTrainWidth.f142 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable BlockTrainWidth.f134 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable BlockTrainWidth.f74 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable OneTapWidth.f226 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable OneTapWidth.f194 a b c) ∨
        (∀ a b c, g a b c = OneTapWidth.mirrorTable OneTapWidth.f98 a b c) := by
  revert g
  decide


private theorem funext₃ {g h : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    (e : ∀ a b c, g a b c = h a b c) : g = h :=
  funext fun a => funext fun b => funext fun c => e a b c

/-- **Leaf (b)**: outside the accreting fifty-four every orbit has bounded diameter. -/
theorem diamBounded_of_not_accreting : DiamBoundedOfNotAccreting := by
  intro f hq hn
  have hn' : ¬ (AccretesByEndpoints f ∨ (∀ a b c, f a b c = OneTapWidth.f106 a b c) ∨
      (∀ a b c, f a b c = f120 a b c)) := by
    rintro (h | h | h)
    · exact hn (Or.inl h)
    · exact hn (Or.inr (Or.inl (funext₃ h)))
    · exact hn (Or.inr (Or.inr (funext₃ h)))
  rcases classify_outside_accreting f hq hn' with hz | h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 |
      h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 |
      h23 | h24 | h25
  · exact diamBounded_of_zeroByEndpoints hq hz
  · obtain rfl := funext₃ h0
    exact diamBounded_of_diamBoundedBy OneTapWidth.diamBoundedBy_f38
  · obtain rfl := funext₃ h1
    exact diamBounded_of_diamBoundedBy OneTapWidth.diamBoundedBy_f46
  · obtain rfl := funext₃ h2
    exact diamBounded_of_diamBoundedBy OneTapWidth.diamBoundedBy_f66
  · obtain rfl := funext₃ h3
    exact diamBounded_of_diamBoundedBy OneTapWidth.diamBoundedBy_f166
  · obtain rfl := funext₃ h4
    exact diamBounded_of_diamBoundedBy OneTapWidth.diamBoundedBy_f174
  · obtain rfl := funext₃ h5
    exact diamBounded_of_affine (a := 5) (b := 5) fun s k =>
      BlockTrainWidth.diam_iterate_le_of_leftClear (hq := hq) BlockTrainWidth.f6_leftClear
        BlockTrainWidth.f6_tap s k
  · obtain rfl := funext₃ h6
    exact diamBounded_of_affine (a := 5) (b := 5) fun s k =>
      BlockTrainWidth.diam_iterate_le_of_leftClear (hq := hq) BlockTrainWidth.f14_leftClear
        BlockTrainWidth.f14_tap s k
  · obtain rfl := funext₃ h7
    exact diamBounded_of_affine (a := 5) (b := 5) fun s k =>
      BlockTrainWidth.diam_iterate_le_f142 s k
  · obtain rfl := funext₃ h8
    exact diamBounded_of_affine (a := 10) (b := 5) fun s k =>
      BlockTrainWidth.diam_iterate_le_f134 s k
  · obtain rfl := funext₃ h9
    exact diamBounded_of_affine (a := 8) (b := 19) fun s k =>
      BlockTrainWidth.diam_iterate_le_f74 s k
  · obtain rfl := funext₃ h10
    exact diamBounded_of_affine (a := 2) (b := 0) fun s k => by
      have := OneTapWidth.diam_iterate_le_two_mul_of_traffic (hq := hq)
        OneTapWidth.f226_traffic s k
      omega
  · obtain rfl := funext₃ h11
    exact diamBounded_of_affine (a := 2) (b := 0) fun s k => by
      have := OneTapWidth.diam_iterate_le_two_mul_of_traffic (hq := hq)
        OneTapWidth.f194_traffic s k
      omega
  · obtain rfl := funext₃ h12
    exact diamBounded_of_affine (a := 2) (b := 0) fun s k => by
      have := OneTapWidth.diam_iterate_le_two_mul_of_traffic (hq := hq)
        OneTapWidth.f98_traffic s k
      omega
  · obtain rfl := funext₃ h13
    exact diamBounded_of_diamBoundedBy
      (OneTapWidth.diamBoundedBy_mirrorTable OneTapWidth.diamBoundedBy_f38)
  · obtain rfl := funext₃ h14
    exact diamBounded_of_diamBoundedBy
      (OneTapWidth.diamBoundedBy_mirrorTable OneTapWidth.diamBoundedBy_f46)
  · obtain rfl := funext₃ h15
    exact diamBounded_of_diamBoundedBy
      (OneTapWidth.diamBoundedBy_mirrorTable OneTapWidth.diamBoundedBy_f66)
  · obtain rfl := funext₃ h16
    exact diamBounded_of_diamBoundedBy
      (OneTapWidth.diamBoundedBy_mirrorTable OneTapWidth.diamBoundedBy_f166)
  · obtain rfl := funext₃ h17
    exact diamBounded_of_diamBoundedBy
      (OneTapWidth.diamBoundedBy_mirrorTable OneTapWidth.diamBoundedBy_f174)
  · obtain rfl := funext₃ h18
    exact diamBounded_of_affine (a := 5) (b := 5) fun s k =>
      BlockTrainWidth.diam_iterate_le_of_leftClear_mirror (hq := hq) (f := BlockTrainWidth.f6)
        BlockTrainWidth.f6_leftClear BlockTrainWidth.f6_tap s k
  · obtain rfl := funext₃ h19
    exact diamBounded_of_affine (a := 5) (b := 5) fun s k =>
      BlockTrainWidth.diam_iterate_le_of_leftClear_mirror (hq := hq) (f := BlockTrainWidth.f14)
        BlockTrainWidth.f14_leftClear BlockTrainWidth.f14_tap s k
  · obtain rfl := funext₃ h20
    exact diamBounded_of_affine (a := 5) (b := 5) fun s k =>
      BlockTrainWidth.diam_iterate_le_mirror_f142 s k
  · obtain rfl := funext₃ h21
    exact diamBounded_of_affine (a := 10) (b := 5) fun s k =>
      BlockTrainWidth.diam_iterate_le_mirror_f134 s k
  · obtain rfl := funext₃ h22
    exact diamBounded_of_affine (a := 8) (b := 19) fun s k =>
      BlockTrainWidth.diam_iterate_le_mirror_f74 s k
  · obtain rfl := funext₃ h23
    exact diamBounded_of_affine (a := 2) (b := 0) fun s k => by
      have := OneTapWidth.diam_iterate_le_two_mul_of_traffic_mirror (hq := hq)
        (f := OneTapWidth.f226) OneTapWidth.f226_traffic s k
      omega
  · obtain rfl := funext₃ h24
    exact diamBounded_of_affine (a := 2) (b := 0) fun s k => by
      have := OneTapWidth.diam_iterate_le_two_mul_of_traffic_mirror (hq := hq)
        (f := OneTapWidth.f194) OneTapWidth.f194_traffic s k
      omega
  · obtain rfl := funext₃ h25
    exact diamBounded_of_affine (a := 2) (b := 0) fun s k => by
      have := OneTapWidth.diam_iterate_le_two_mul_of_traffic_mirror (hq := hq)
        (f := OneTapWidth.f98) OneTapWidth.f98_traffic s k
      omega

/-! ## Piece 3: the exact count of copies is not the right currency -/

/-- The parity of the number of set cells, as an additive map. -/
private noncomputable def weight : (ℤ →₀ ZMod 2) →+ ZMod 2 :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id (ZMod 2)

private theorem weight_translate (i : ℤ) (p : ℤ →₀ ZMod 2) :
    weight (EndpointClasses.translate i p) = weight p := by
  unfold weight EndpointClasses.translate
  simp only [Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

private theorem two_self_eq_zero (x : ZMod 2) : x + x = 0 := by revert x; decide

private theorem diam_single_zero_one : diam (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = 1 := by
  simp [diam]

/-- **Guard: an exact count of three copies is never reached from a single cell by a table whose
step adds two translates of the state.** One step changes the parity of the number of set cells
to even, so after a positive time the state has an even number of set cells, while three copies
of a single cell have three, and at time zero the state is one copy. Here `tableRule f hq s i`
is `s (i + a) + s (i + b)`, as at tables `60` and `90`. -/
theorem not_copies_three_of_twoTap {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}
    {a b : ℤ} (hU : ∀ s i, tableRule f hq s i = s (i + a) + s (i + b)) (t G : ℕ) :
    ¬ Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      ((tableRule f hq)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 3 G := by
  intro h
  have hp : (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ≠ 0 := by
    rw [Ne, Finsupp.single_eq_zero]; decide
  rcases t with _ | n
  · have := copies_diam_le hp h (by omega)
    rw [Function.iterate_zero, id_eq, diam_single_zero_one] at this
    omega
  · have hstep : ∀ s, weight (tableRule f hq s) = 0 := by
      intro s
      have e : tableRule f hq s = EndpointClasses.translate (-a) s +
          EndpointClasses.translate (-b) s := by
        ext i
        rw [hU, Finsupp.add_apply, translate_apply', translate_apply']
        simp [sub_eq_add_neg]
      rw [e, map_add, weight_translate, weight_translate]
      exact two_self_eq_zero _
    obtain ⟨c, -, hc⟩ := h
    have h1 := hstep ((tableRule f hq)^[n] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
    rw [← Function.iterate_succ_apply' (tableRule f hq) n, hc, map_sum] at h1
    simp only [weight_translate, Finset.sum_const, Finset.card_range] at h1
    have hw : weight (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = 1 := by
      simp [weight, Finsupp.liftAddHom_apply]
    rw [hw] at h1
    revert h1; decide

/-- **Guard: table `90` does not reach three copies of a single cell.** -/
theorem not_copies_three_f90_single (t G : ℕ) :
    ¬ Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      ((tableRule f90 ObservedColumn.hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 3 G :=
  not_copies_three_of_twoTap (a := -1) (b := 1) (fun s i => by
    rw [tableRule_apply]; simp [f90, sub_eq_add_neg]) t G

/-- **Guard: table `60` does not reach three copies of a single cell.** -/
theorem not_copies_three_f60_single (t G : ℕ) :
    ¬ Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2))
      ((tableRule f60 hq60)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 3 G :=
  not_copies_three_of_twoTap (a := -1) (b := 0) (fun s i => by
    rw [tableRule_apply]; simp [f60, sub_eq_add_neg]) t G

/-- **Guard: at tables `60` and `90` a single cell is not replicated in the exact-count sense of
`ReplicatesExactly`**, since no iterate is three copies of it at any gap. -/
theorem not_replicates_single_f90_f60 :
    ¬ ReplicatesExactly (tableRule f90 ObservedColumn.hq90)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ∧
      ¬ ReplicatesExactly (tableRule f60 hq60) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) :=
  ⟨fun ⟨_, h⟩ => by obtain ⟨t, ht⟩ := h 3 0; exact not_copies_three_f90_single t 0 ht,
    fun ⟨_, h⟩ => by obtain ⟨t, ht⟩ := h 3 0; exact not_copies_three_f60_single t 0 ht⟩

/-! ## Piece 4: the three mechanisms by which a table replicates -/

private theorem translate_zero' (s : ℤ →₀ ZMod 2) : EndpointClasses.translate 0 s = s := by
  ext x
  rw [translate_apply']
  simp

private theorem translate_translate' (a b : ℤ) (s : ℤ →₀ ZMod 2) :
    EndpointClasses.translate a (EndpointClasses.translate b s) =
      EndpointClasses.translate (b + a) s := by
  ext x
  rw [translate_apply', translate_apply', translate_apply']
  congr 1
  ring

private theorem translate_sum' (a : ℤ) (n : ℕ) (g : ℕ → ℤ →₀ ZMod 2) :
    EndpointClasses.translate a ((Finset.range n).sum g) =
      (Finset.range n).sum fun j => EndpointClasses.translate a (g j) := by
  ext x
  rw [translate_apply', Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun j _ => (translate_apply' _ _ _).symm

/-- A block of copies with a bound on how far the offsets spread. -/
private def CopiesW (p s : ℤ →₀ ZMod 2) (n G w : ℕ) : Prop :=
  ∃ c : ℕ → ℤ, (∀ j, j + 1 < n → c j + diam p + G ≤ c (j + 1)) ∧
    (∀ j, j < n → c j ≤ c 0 + w) ∧
    s = (Finset.range n).sum fun j => EndpointClasses.translate (c j) p

private theorem sum_range_mul_div_mod (g : ℕ → ℕ → ℤ →₀ ZMod 2) (n : ℕ) (hn : 0 < n) :
    ∀ q, (Finset.range (q * n)).sum (fun j => g (j / n) (j % n)) =
      (Finset.range q).sum fun m => (Finset.range n).sum fun l => g m l := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    have h1 : (q * n + x) / n = q := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hx', zero_add]
    have h2 : (q * n + x) % n = x := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx']
    rw [h1, h2]

private theorem div_mod_succ (n j : ℕ) (hn : 0 < n) :
    (j % n + 1 < n ∧ (j + 1) / n = j / n ∧ (j + 1) % n = j % n + 1) ∨
      (j % n + 1 = n ∧ (j + 1) / n = j / n + 1 ∧ (j + 1) % n = 0) := by
  have hr : j % n < n := Nat.mod_lt _ hn
  have hj : j = j % n + n * (j / n) := (Nat.mod_add_div j n).symm
  rcases Nat.lt_or_ge (j % n + 1) n with h | h
  · left
    have e : j + 1 = (j % n + 1) + n * (j / n) := by omega
    refine ⟨h, ?_, ?_⟩
    · rw [e, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt h, zero_add]
    · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  · right
    have h' : j % n + 1 = n := by omega
    have e : j + 1 = n * (j / n + 1) := by rw [Nat.mul_succ]; omega
    refine ⟨h', ?_, ?_⟩
    · rw [e, Nat.mul_div_cancel_left _ hn]
    · rw [e, Nat.mul_mod_right]

/-- The step of the block construction: summing `q` translates of a block of `n` copies, the
translates `e 0, …, e (q - 1)` being far enough apart, gives a block of `q * n` copies. -/
private theorem copiesW_step {p s : ℤ →₀ ZMod 2} {n G w : ℕ} (hn : 0 < n)
    (hs : CopiesW p s n G w) (q : ℕ) (e : ℕ → ℤ) (E : ℕ)
    (he : ∀ m, m + 1 < q → e m + w + diam p + G ≤ e (m + 1))
    (hE : ∀ m, m < q → e m ≤ e 0 + E) :
    CopiesW p ((Finset.range q).sum fun m => EndpointClasses.translate (e m) s)
      (q * n) G (w + E) := by
  obtain ⟨c, hc, hw, rfl⟩ := hs
  refine ⟨fun j => c (j % n) + e (j / n), ?_, ?_, ?_⟩
  · intro j hj
    have hlt : j / n < q := (Nat.div_lt_iff_lt_mul hn).mpr (by omega)
    have hr : j % n < n := Nat.mod_lt _ hn
    rcases div_mod_succ n j hn with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have := hc (j % n) h1
      simp only [h2, h3]
      omega
    · have hlt' : j / n + 1 < q := by
        have := (Nat.div_lt_iff_lt_mul hn).mpr (show j + 1 < q * n by omega)
        omega
      have h4 := he (j / n) hlt'
      have h5 := hw (j % n) hr
      simp only [h2, h3]
      omega
  · intro j hj
    have hlt : j / n < q := (Nat.div_lt_iff_lt_mul hn).mpr (by omega)
    have hr : j % n < n := Nat.mod_lt _ hn
    have h1 := hw (j % n) hr
    have h2 := hE (j / n) hlt
    simp only [Nat.zero_mod, Nat.zero_div]
    omega
  · change _ = (Finset.range (q * n)).sum fun j =>
      EndpointClasses.translate (c (j % n) + e (j / n)) p
    have := sum_range_mul_div_mod (fun m l => EndpointClasses.translate (c l + e m) p) n hn q
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [translate_sum']
    exact Finset.sum_congr rfl fun l _ => by rw [translate_translate']

/-- **The doubling-identity mechanism, in the abstract**: if at a nonzero `p` the iterate at
`2 ^ M + t` is the sum of `q ≥ 2` translates of the iterate at `t`, the translates sitting at
`2 ^ M * (a0 + m * b)`, then `U` replicates `p`. Taking the binary expansion of the time, the
iterate at the sum of well-spaced powers of two is `q ^ r` copies. -/
private theorem replicates_of_doubling_identity
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {p : ℤ →₀ ZMod 2} (hp : p ≠ 0) {q b : ℕ} (a0 : ℤ)
    (hq2 : 2 ≤ q) (hb : 1 ≤ b)
    (hid : ∀ M t (i : ℤ), (U^[2 ^ M + t] p) i =
      (Finset.range q).sum fun m => (U^[t] p) (i - 2 ^ M * (a0 + m * b))) :
    Replicates U p := by
  have hid' : ∀ M t, U^[2 ^ M + t] p = (Finset.range q).sum fun m =>
      EndpointClasses.translate ((2 : ℤ) ^ M * (a0 + m * b)) (U^[t] p) := by
    intro M t
    ext i
    rw [hid, Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun m _ => (translate_apply' _ _ _).symm
  have key : ∀ (G r : ℕ), ∃ t w, CopiesW p (U^[t] p) (q ^ r) G w := by
    intro G r
    induction r with
    | zero =>
      refine ⟨0, 0, fun _ => 0, ?_, ?_, ?_⟩
      · intro j hj; simp at hj
      · intro j hj; simp
      · simp [translate_zero']
    | succ r ih =>
      obtain ⟨t, w, hc⟩ := ih
      set M := w + diam p + G with hM
      have hMlt : (M : ℤ) < 2 ^ M := by exact_mod_cast Nat.lt_two_pow_self
      have hpos : (0 : ℤ) < 2 ^ M := by positivity
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      have hn : 0 < q ^ r := Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
      refine ⟨2 ^ M + t, w + 2 ^ M * b * q, ?_⟩
      have hstep := copiesW_step hn hc q (fun m => (2 : ℤ) ^ M * (a0 + m * b)) (2 ^ M * b * q)
        (fun m hm => by
          have e : (2 : ℤ) ^ M * (a0 + ((m + 1 : ℕ) : ℤ) * b) =
              2 ^ M * (a0 + m * b) + 2 ^ M * b := by push_cast; ring
          change _ ≤ (2 : ℤ) ^ M * (a0 + ((m + 1 : ℕ) : ℤ) * b)
          rw [e]
          have : (2 : ℤ) ^ M * 1 ≤ 2 ^ M * b := mul_le_mul_of_nonneg_left hb' hpos.le
          have hM' : ((w : ℤ) + diam p + G) = M := by rw [hM]; push_cast; ring
          nlinarith)
        (fun m hm => by
          have hm' : (m : ℤ) ≤ q := by exact_mod_cast hm.le
          have : (2 : ℤ) ^ M * ((m : ℤ) * b) ≤ 2 ^ M * ((q : ℤ) * b) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm' (by omega)) hpos.le
          push_cast
          nlinarith)
      rw [hid', pow_succ']
      exact hstep
  refine ⟨hp, fun N G => ?_⟩
  obtain ⟨t, w, c, hc, -, hs⟩ := key G N
  have hle : N ≤ q ^ N := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hq2 N)
  exact ⟨t, q ^ N, hle, c, hc, hs⟩

/-- **The linear tables**: a table whose rule is a sum of at least two of the three neighbouring
cells, `α * a + β * b + γ * c` over `ZMod 2`. These are tables `60`, `90`, `102` and `150`. -/
def LinearTaps (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  ∃ α β γ : ZMod 2, 2 ≤ α.val + β.val + γ.val ∧ ∀ a b c, f a b c = α * a + β * b + γ * c

instance (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Decidable (LinearTaps f) := by
  unfold LinearTaps; infer_instance

/-- **The squaring identity of a linear table**: `2 ^ M` steps of `α * a + β * b + γ * c` are the
same combination of cells at distance `2 ^ M`, the cross terms cancelling in characteristic two.
Rule `90` is the case `(1, 0, 1)`. -/
private theorem iterate_two_pow_linear {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    {hq : f 0 0 0 = 0} {α β γ : ZMod 2} (hf : ∀ a b c, f a b c = α * a + β * b + γ * c) :
    ∀ (M : ℕ) (s : ℤ →₀ ZMod 2) (i : ℤ),
      ((tableRule f hq)^[2 ^ M] s) i = α * s (i - 2 ^ M) + β * s i + γ * s (i + 2 ^ M) := by
  intro M
  induction M with
  | zero =>
    intro s i
    rw [pow_zero, Function.iterate_one, tableRule_apply, hf]
    simp
  | succ M ih =>
    intro s i
    have hiter : (2 : ℕ) ^ (M + 1) = 2 ^ M + 2 ^ M := by rw [pow_succ]; ring
    have hpow : (2 : ℤ) ^ (M + 1) = (2 : ℤ) ^ M + (2 : ℤ) ^ M := by rw [pow_succ]; ring
    rw [hiter, Function.iterate_add_apply, ih ((tableRule f hq)^[2 ^ M] s) i,
      ih s (i - (2 : ℤ) ^ M), ih s i, ih s (i + (2 : ℤ) ^ M)]
    have e1 : i - (2 : ℤ) ^ M - (2 : ℤ) ^ M = i - (2 : ℤ) ^ (M + 1) := by rw [hpow]; ring
    have e2 : i - (2 : ℤ) ^ M + (2 : ℤ) ^ M = i := by ring
    have e3 : i + (2 : ℤ) ^ M - (2 : ℤ) ^ M = i := by ring
    have e4 : i + (2 : ℤ) ^ M + (2 : ℤ) ^ M = i + (2 : ℤ) ^ (M + 1) := by rw [hpow]; ring
    rw [e1, e2, e3, e4]
    have hc : ∀ α β γ x y z u v : ZMod 2, α * (α * x + β * y + γ * z) +
        β * (α * y + β * z + γ * u) + γ * (α * z + β * u + γ * v) = α * x + β * z + γ * v := by
      decide
    exact hc α β γ _ _ _ _ _

/-- **Linear tables replicate a single cell**: at `t = 2 ^ M₁ + … + 2 ^ Mᵣ` with the exponents
well spaced the iterate is `|T| ^ r` copies of the cell, `T` the set of taps
([RuleSpace] §3 and §5). -/
theorem replicates_of_linear (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (h : LinearTaps f) : Replicates (tableRule f hq) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) := by
  obtain ⟨α, β, γ, hT, hf⟩ := h
  have hp : (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ≠ 0 := by
    rw [Ne, Finsupp.single_eq_zero]; decide
  have Φ := iterate_two_pow_linear (hq := hq) hf
  have hid : ∀ M t (i : ℤ), ((tableRule f hq)^[2 ^ M + t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i
      = α * ((tableRule f hq)^[t] (Finsupp.single 0 1)) (i - 2 ^ M) +
        β * ((tableRule f hq)^[t] (Finsupp.single 0 1)) i +
        γ * ((tableRule f hq)^[t] (Finsupp.single 0 1)) (i + 2 ^ M) := by
    intro M t i
    rw [Function.iterate_add_apply, Φ]
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases α with rfl | rfl <;> rcases hcases β with rfl | rfl <;>
    rcases hcases γ with rfl | rfl
  · exact absurd hT (by decide)
  · exact absurd hT (by decide)
  · exact absurd hT (by decide)
  · refine replicates_of_doubling_identity hp (q := 2) (b := 1) (-1) le_rfl le_rfl
      fun M t i => ?_
    rw [hid]
    simp [Finset.sum_range_succ]
    abel_nf
  · exact absurd hT (by decide)
  · refine replicates_of_doubling_identity hp (q := 2) (b := 2) (-1) le_rfl (by omega)
      fun M t i => ?_
    rw [hid]
    simp [Finset.sum_range_succ]
    ring_nf
  · refine replicates_of_doubling_identity hp (q := 2) (b := 1) 0 le_rfl le_rfl
      fun M t i => ?_
    rw [hid]
    simp [Finset.sum_range_succ]
    abel_nf
  · refine replicates_of_doubling_identity hp (q := 3) (b := 1) (-1) (by omega) le_rfl
      fun M t i => ?_
    rw [hid]
    simp [Finset.sum_range_succ]
    ring_nf

/-- **The tables agreeing with table `90` off adjacent cells replicate two cells of one parity**:
`AgreesOffAdjacent` is the hypothesis of the doubling identity over one-parity states
([RuleSpace] §4 Proposition 4.2(iv)), and the pattern is the two cells at `0` and `2`. -/
theorem replicates_of_agreesOffAdjacent (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (h : ParityEmulation.AgreesOffAdjacent f) :
    Replicates (tableRule f hq)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) := by
  have hs : ParityEmulation.OneParity
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) := by
    intro i j hi hj
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
    rw [even_iff_two_dvd]
    split_ifs at hi hj <;> first | omega | simp_all
  have hp : (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun x => x 0) h0
    simp at this
  refine replicates_of_doubling_identity hp (q := 2) (b := 2) (-1) le_rfl (by omega)
    fun M t i => ?_
  have := ParityEmulation.iterate_two_pow_add_of_oneParity f h _ hs M t i
  refine this.trans ?_
  simp [Finset.sum_range_succ]
  ring_nf

private theorem dbl_translate' (c : ℤ) (x : ℤ →₀ ZMod 2) :
    Doubling.dbl (EndpointClasses.translate c x) =
      EndpointClasses.translate (2 * c) (Doubling.dbl x) := by
  ext j
  rw [Doubling.dbl_apply, translate_apply', translate_apply', Doubling.dbl_apply]
  congr 1
  omega

private theorem dbl_sum' (n : ℕ) (g : ℕ → ℤ →₀ ZMod 2) :
    Doubling.dbl ((Finset.range n).sum g) = (Finset.range n).sum fun j => Doubling.dbl (g j) := by
  ext j
  rw [Doubling.dbl_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ => (Doubling.dbl_apply _ _).symm

private theorem diam_dbl_single_le :
    diam (Doubling.dbl (Finsupp.single (0 : ℤ) (1 : ZMod 2))) ≤ 2 := by
  have hne : (Doubling.dbl (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support.Nonempty := by
    refine ⟨0, Finsupp.mem_support_iff.mpr ?_⟩
    simp [Doubling.dbl_apply]
  unfold diam
  rw [dite_eq_left hne]
  have h1 : (Doubling.dbl (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support.max' hne ≤ 1 := by
    apply Finset.max'_le
    intro y hy
    by_contra hlt
    have := Finsupp.mem_support_iff.mp hy
    apply this
    rw [Doubling.dbl_apply]
    exact Finsupp.single_eq_of_ne (by omega)
  have h2 : 0 ≤ (Doubling.dbl (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support.min' hne := by
    apply Finset.le_min'
    intro y hy
    by_contra hlt
    have := Finsupp.mem_support_iff.mp hy
    apply this
    rw [Doubling.dbl_apply]
    exact Finsupp.single_eq_of_ne (by omega)
  omega

private theorem copies_dbl_single {s : ℤ →₀ ZMod 2} {k G : ℕ}
    (h : Copies (Finsupp.single (0 : ℤ) (1 : ZMod 2)) s k G) :
    Copies (Doubling.dbl (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (Doubling.dbl s) k G := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun j => 2 * c j, fun j hj => ?_, ?_⟩
  · have := hc j hj
    rw [diam_single_zero_one] at this
    have h2 := diam_dbl_single_le
    change 2 * c j + _ + G ≤ 2 * c (j + 1)
    omega
  · rw [dbl_sum']
    exact Finset.sum_congr rfl fun j _ => dbl_translate' _ _

private theorem iterate_two_mul_dbl (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (hA : Doubling.DoubledAgree f) (x : ℤ →₀ ZMod 2) (k : ℕ) :
    (tableRule f hq)^[2 * k] (Doubling.dbl x) =
      Doubling.dbl ((tableRule f90 ObservedColumn.hq90)^[k] x) := by
  rw [Function.iterate_mul]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply' ((tableRule f hq)^[2]) k, ih,
      Function.iterate_succ_apply' (tableRule f90 ObservedColumn.hq90) k,
      Doubling.tableRule_two_dbl f hq hA]

/-- **The tables agreeing with table `90` at equal adjacent cells replicate the adjacent pair**:
two steps on a doubled state are one step of table `90` on the half-size state
([RuleSpace] §5), so the copies of a single cell that table `90` reaches double to copies of the
pair. -/
theorem replicates_of_doubledAgree (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (hA : Doubling.DoubledAgree f) :
    Replicates (tableRule f hq) (Doubling.dbl (Finsupp.single (0 : ℤ) (1 : ZMod 2))) := by
  have h90 := replicates_of_linear f90 ObservedColumn.hq90 (by decide)
  refine ⟨?_, fun N G => ?_⟩
  · intro h0
    have := congrArg (fun x => x 0) h0
    simp [Doubling.dbl_apply] at this
  · obtain ⟨t, k, hk, hcop⟩ := h90.2 N G
    refine ⟨2 * t, k, hk, ?_⟩
    rw [iterate_two_mul_dbl f hq hA]
    exact copies_dbl_single hcop

/-- **Leaf: each of the fourteen tables replicates a pattern**, by the three mechanisms:
linear taps (tables `60`, `90`, `102`, `150`), agreement with table `90` off adjacent cells
(tables `18`, `26`, `82`, `146`, `154`, `210`, `218`), and doubled agreement (tables `94`, `122`,
`126`). -/
theorem replicates_of_mem_fourteen : ReplicatesOfMemFourteen := by
  intro f hq hf
  simp only [fourteen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
    first
    | exact ⟨_, replicates_of_linear _ hq (by decide)⟩
    | exact ⟨_, replicates_of_agreesOffAdjacent _ hq
        (by unfold ParityEmulation.AgreesOffAdjacent; decide)⟩
    | exact ⟨_, replicates_of_doubledAgree _ hq (by decide)⟩

/-- **The three leaves hold together**: the conjunction of the three leaf statements of
`replication_bracket`, each proved above, so the parent is not vacuous. -/
theorem replication_bracket_nonvacuous :
    NotReplicatesOfDiamBounded ∧ DiamBoundedOfNotAccreting ∧ ReplicatesOfMemFourteen :=
  ⟨not_replicates_of_diamBounded, diamBounded_of_not_accreting, replicates_of_mem_fourteen⟩

/-- The linear mechanism has a fixed instance: table `60` and its single-cell pattern. -/
theorem replicates_of_linear_nonvacuous :
    ∃ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0), LinearTaps f ∧
      Replicates (tableRule f hq) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) :=
  ⟨f60, hq60, by decide, replicates_of_linear f60 hq60 (by decide)⟩

/-- The one-parity mechanism has a fixed instance: table `18` and the two cells at `0` and `2`. -/
theorem replicates_of_agreesOffAdjacent_nonvacuous :
    ∃ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0),
      ParityEmulation.AgreesOffAdjacent f ∧
      Replicates (tableRule f hq)
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2)) :=
  ⟨ParityEmulation.f18, ParityEmulation.hq18, ParityEmulation.agreesOffAdjacent_f18,
    replicates_of_agreesOffAdjacent _ _ ParityEmulation.agreesOffAdjacent_f18⟩

/-- The doubled mechanism has a fixed instance: table `94` and the adjacent pair. -/
theorem replicates_of_doubledAgree_nonvacuous :
    ∃ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0), Doubling.DoubledAgree f ∧
      Replicates (tableRule f hq) (Doubling.dbl (Finsupp.single (0 : ℤ) (1 : ZMod 2))) :=
  ⟨Doubling.f94, by decide, by decide, replicates_of_doubledAgree _ _ (by decide)⟩

end ReplicationBracket

/-- info: 'ReplicationBracket.replication_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replication_bracket

/-- info: 'ReplicationBracket.fourteen_subset_accreting' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.fourteen_subset_accreting

/-- info: 'ReplicationBracket.copies_diam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.copies_diam_le

/-- info: 'ReplicationBracket.not_replicates_of_diamBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.not_replicates_of_diamBounded

/-- info: 'ReplicationBracket.classify_outside_accreting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.classify_outside_accreting

/-- info: 'ReplicationBracket.diamBounded_of_not_accreting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.diamBounded_of_not_accreting

/-- info: 'ReplicationBracket.not_copies_three_of_twoTap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.not_copies_three_of_twoTap

/-- info: 'ReplicationBracket.not_replicates_single_f90_f60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.not_replicates_single_f90_f60

/-- info: 'ReplicationBracket.replicates_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replicates_of_linear

/-- info: 'ReplicationBracket.replicates_of_agreesOffAdjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replicates_of_agreesOffAdjacent

/-- info: 'ReplicationBracket.replicates_of_doubledAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replicates_of_doubledAgree

/-- info: 'ReplicationBracket.replicates_of_mem_fourteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replicates_of_mem_fourteen

/-- info: 'ReplicationBracket.replication_bracket_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replication_bracket_nonvacuous

/-- info: 'ReplicationBracket.replicates_of_linear_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replicates_of_linear_nonvacuous

/-- info: 'ReplicationBracket.replicates_of_agreesOffAdjacent_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replicates_of_agreesOffAdjacent_nonvacuous

/-- info: 'ReplicationBracket.replicates_of_doubledAgree_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReplicationBracket.replicates_of_doubledAgree_nonvacuous
