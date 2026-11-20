module

public import ECA.Doubling
public import ECA.ObservedColumnClasses
public import ECA.ObservedRays
public import ECA.ParityEmulation
public import ECA.ReproductionBracket
public import ECA.Rule150Rays
public import ECA.StretchColumns
public import ErgodicTheory.DrivenColumns
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorization.Basic
import all ECA.StretchColumns
import Rule30Open.Analogs.SymmetricAxes

/-!
# Mirror columns: a column from a finite seed at rule `90` or `150` is eventually periodic
exactly when the seed is mirror symmetric about its cell
([RuleSpace] §4 Proposition 4.8, row RS-92)

`ObservedColumnClasses` shows that a seed mirror symmetric about a cell has an eventually periodic
column there, at rule `90` and at rule `150`. This file proves the converse, so the two
rules' columns from a finite seed are classified at every cell: the column of rule `90` or of
rule `150` from `s₀` at the cell `c` is eventually periodic if and only if `s₀ (c + i) = s₀ (c - i)`
for every `i`.

The two iffs are proved from the same statements in the `rule30-open` library of
lhallee, over a bridge that reads a finite configuration as a row of booleans; that library
proved them first. This file's own route, kept for the engine's other uses, is the two-power
identity of the two rules, `2 ^ j` steps reading the cells at distance
`2 ^ j` (`iterate_two_pow_f90`, `iterate_two_pow_f150`), and an arithmetic engine about sequences
(`not_eventuallyPeriodic_of_two_pow_blocks`): a sequence that, at every position `q`, copies a
block `w q` at the position `q + 2 ^ j` for every large `j`, and at the corner `2 ^ j - m` differs
from the block at the position one power further on for arbitrarily large `j`, is not eventually
periodic, since a period `2 ^ a * q` with `q` odd is met by the powers `2 ^ (j + k * φ q)` modulo
itself. At the far edge of a seed the corner reads the edge cell, which no light cone has moved.
A seed that is asymmetric about `c` is split at the largest asymmetric offset into a part
symmetric about `c`, whose column at `c` is clear from the start, and a part inside that offset
whose edge, on one side, is the corner of the engine.

The classes of rules that step as rule `90` carry the result over: on one-parity seeds
(`LocalRule.AgreesOffAdjacent`), and on doubled seeds (`LocalRule.DoubledAgree`) at the doubled
cell, whose even subsequence of times is rule `90`'s column of the undoubled seed.

## Main results

* `not_eventuallyPeriodic_of_two_pow_blocks` — the engine, over any type.
* `eventuallyPeriodic_observedColumn_f90_iff`, `eventuallyPeriodic_observedColumn_f150_iff` —
  **a column of rule `90` or `150` from a finite seed is eventually periodic exactly when the seed
  is mirror symmetric about its cell.**
* `eventuallyPeriodic_observedColumn_iff_of_oneParity` — the same at every rule that agrees with
  rule `90` off adjacent cells, from a one-parity seed.
* `not_eventuallyPeriodic_observedColumn_dbl` — at a rule that agrees with rule `90` where two
  adjacent cells are equal, the column of a doubled seed at the doubled cell is not eventually
  periodic when the undoubled seed is not mirror symmetric about the cell.
* `not_eventuallyPeriodic_observedColumn_min_f90`, `not_eventuallyPeriodic_observedColumn_min_f150`,
  `not_eventuallyPeriodic_observedColumn_min_of_oneParity`,
  `not_eventuallyPeriodic_observedColumn_dbl_min` — a seed of two or more set cells is never mirror
  symmetric about its leftmost set cell, so the column there is not eventually periodic.
* `eventuallyPeriodic_observedColumn_iff_of_iterate_oneParity` — the same at a seed whose orbit
  reaches a state of one parity, the column eventually periodic exactly when that state is mirror
  symmetric about the cell ([RuleSpace] §4 Proposition 4.8, row RS-92), and
  `not_eventuallyPeriodic_observedColumn_f18_reaches_oneParity`,
  `not_eventuallyPeriodic_observedColumn_f146_reaches_oneParity` — its fourteen instances, at seven
  seeds of diameter at most five at rules `18` and `146`.
* The `_nonvacuous` theorems meet the hypotheses of each at once.

## Scope

The statements are about the columns of rules `90` and `150` and of the two classes that step as
rule `90` on the seeds named above, at one seed and one cell. Nothing is claimed about any other
rule, and nothing about a column read at a cell along a ray of positive speed.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The engine: blocks copied at the powers of two -/

/-- **A sequence that copies a block at every large power of two and differs from it at a corner is
not eventually periodic** ([RuleSpace] §4 Proposition 4.8, row RS-92). Here `hcopy` says that at
every position `q` the value at `q + 2 ^ j` is `w q` for all large `j`, and `hcorner` that at
arbitrarily large `j` the value at `2 ^ j - m + 2 ^ j` is not `w (2 ^ j - m)`. A period `2 ^ a * q`
with `q` odd is met by the powers `2 ^ (j + k * φ q)`, which are congruent to `2 ^ j` modulo it, so
`hcopy` carries the value at the corner to the far power and `hcorner` contradicts it. -/
theorem not_eventuallyPeriodic_of_two_pow_blocks {α : Type*} (u w : ℕ → α) (m : ℕ)
    (hcopy : ∀ q, ∃ J, ∀ j ≥ J, u (q + 2 ^ j) = w q)
    (hcorner : ∀ J, ∃ j ≥ J, u (2 ^ j - m + 2 ^ j) ≠ w (2 ^ j - m)) :
    ¬ DrivenColumns.EventuallyPeriodic u := by
  rintro ⟨P, N, hP, hper⟩
  have hk : ∀ x, N ≤ x → ∀ k, u (x + k * P) = u x := by
    intro x hx k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hper (x + k * P) (le_trans hx (Nat.le_add_right _ _))
      rw [Nat.succ_mul, ← add_assoc, h, ih]
  obtain ⟨a, q, hq, hPq⟩ := Nat.exists_eq_two_pow_mul_odd hP.ne'
  obtain ⟨j, hjJ, hj⟩ := hcorner (max a (N + m))
  have hja : a ≤ j := le_trans (le_max_left _ _) hjJ
  have hjN : N + m ≤ j := le_trans (le_max_right _ _) hjJ
  have hlt : j < 2 ^ j := Nat.lt_two_pow_self
  obtain ⟨J, hJ⟩ := hcopy (2 ^ j - m)
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hq
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq.pos
  set j' := j + Nat.totient q * J with hj'
  have hj'J : J ≤ j' := by
    have : J ≤ Nat.totient q * J := Nat.le_mul_of_pos_left _ hφ
    omega
  have hmod : 2 ^ Nat.totient q ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop
  have hq1 : 2 ^ j ≡ 2 ^ j' [MOD q] := by
    have h1 : (2 ^ Nat.totient q) ^ J ≡ 1 ^ J [MOD q] := hmod.pow J
    have h2 := h1.mul_left (2 ^ j)
    rw [one_pow, mul_one, ← pow_mul, ← pow_add] at h2
    exact h2.symm
  have hle : 2 ^ j ≤ 2 ^ j' := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdq : q ∣ 2 ^ j' - 2 ^ j := (Nat.modEq_iff_dvd' hle).mp hq1
  have hda : 2 ^ a ∣ 2 ^ j' - 2 ^ j :=
    Nat.dvd_sub (pow_dvd_pow 2 (by omega)) (pow_dvd_pow 2 hja)
  have hdP : P ∣ 2 ^ j' - 2 ^ j := by
    rw [hPq]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left a hcop) hda hdq
  obtain ⟨d, hd⟩ := hdP
  have hx : N ≤ 2 ^ j - m + 2 ^ j := by omega
  have e1 : 2 ^ j - m + 2 ^ j' = (2 ^ j - m + 2 ^ j) + d * P := by
    rw [mul_comm d P, ← hd]
    omega
  have h1 := hJ j' hj'J
  rw [e1, hk _ hx d] at h1
  exact hj h1

/-! ## Rules with three taps `1, ε, 1` -/

/-- The one-step law of a rule that adds its two neighbours and `ε` times its own cell. -/
private def ThreeTap (F : FiniteConfiguration → FiniteConfiguration) (ε : ZMod 2) : Prop :=
  ∀ (s : FiniteConfiguration) (i : ℤ), F s i = s (i - 1) + ε * s i + s (i + 1)

private theorem threeTap_add {F : FiniteConfiguration → FiniteConfiguration} {ε : ZMod 2}
    (hF : ThreeTap F ε) (a b : FiniteConfiguration) : F (a + b) = F a + F b := by
  ext i
  rw [Finsupp.add_apply, hF a i, hF b i, hF (a + b) i]
  simp only [Finsupp.add_apply]
  ring

private theorem threeTap_iterate_add {F : FiniteConfiguration → FiniteConfiguration} {ε : ZMod 2}
    (hF : ThreeTap F ε) (t : ℕ) :
    ∀ (a b : FiniteConfiguration) (i : ℤ), (F^[t] (a + b)) i = (F^[t] a) i + (F^[t] b) i := by
  induction t with
  | zero => intro a b i; rfl
  | succ t ih =>
    intro a b i
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      threeTap_add hF]
    exact ih _ _ i

/-- The light cone to the left: cells at or below `a - t` are clear at time `t` when the seed
is clear at and below `a`. -/
private theorem threeTap_iterate_below {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε) (s : FiniteConfiguration) (a : ℤ)
    (hs : ∀ i, i ≤ a → s i = 0) (t : ℕ) : ∀ i : ℤ, i ≤ a - t → (F^[t] s) i = 0 := by
  induction t with
  | zero => intro i hi; exact hs i (by simpa using hi)
  | succ t ih =>
    intro i hi
    rw [Function.iterate_succ_apply', hF, ih (i - 1) (by push_cast at hi; omega),
      ih i (by push_cast at hi; omega), ih (i + 1) (by push_cast at hi; omega)]
    simp

/-- The light cone to the right: cells at or above `b + t` are clear at time `t` when the seed
is clear at and above `b`. -/
private theorem threeTap_iterate_above {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε) (s : FiniteConfiguration) (b : ℤ)
    (hs : ∀ i, b ≤ i → s i = 0) (t : ℕ) : ∀ i : ℤ, b + t ≤ i → (F^[t] s) i = 0 := by
  induction t with
  | zero => intro i hi; exact hs i (by simpa using hi)
  | succ t ih =>
    intro i hi
    rw [Function.iterate_succ_apply', hF, ih (i - 1) (by push_cast at hi; omega),
      ih i (by push_cast at hi; omega), ih (i + 1) (by push_cast at hi; omega)]
    simp

/-- The right edge of a seed moves out one cell per step and stays set. -/
private theorem threeTap_iterate_edge {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε) (s : FiniteConfiguration) (R : ℤ) (h1 : s R = 1)
    (h2 : ∀ i, R < i → s i = 0) (t : ℕ) : (F^[t] s) (R + t) = 1 := by
  induction t with
  | zero => simpa using h1
  | succ t ih =>
    have hab := threeTap_iterate_above hF s (R + 1) (fun i hi => h2 i (by omega)) t
    rw [Function.iterate_succ_apply', hF, show R + ((t + 1 : ℕ) : ℤ) - 1 = R + t by push_cast; ring,
      ih, hab (R + ((t + 1 : ℕ) : ℤ)) (by push_cast; omega),
      hab (R + ((t + 1 : ℕ) : ℤ) + 1) (by push_cast; omega)]
    simp

/-- The seed reflected in the cell `c`. -/
private noncomputable def mirrorConfig (c : ℤ) (s : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.equivMapDomain (Equiv.subLeft (2 * c)) s

private theorem mirrorConfig_apply (c : ℤ) (s : FiniteConfiguration) (i : ℤ) :
    mirrorConfig c s i = s (2 * c - i) := by
  simp only [mirrorConfig, Finsupp.equivMapDomain_apply]
  congr 1
  simp [Equiv.subLeft]
  ring

private theorem threeTap_mirror {F : FiniteConfiguration → FiniteConfiguration} {ε : ZMod 2}
    (hF : ThreeTap F ε) (c : ℤ) (s : FiniteConfiguration) :
    F (mirrorConfig c s) = mirrorConfig c (F s) := by
  ext i
  rw [hF (mirrorConfig c s) i, mirrorConfig_apply c (F s) i, hF s (2 * c - i)]
  simp only [mirrorConfig_apply]
  rw [show 2 * c - (i - 1) = 2 * c - i + 1 by ring, show 2 * c - (i + 1) = 2 * c - i - 1 by ring]
  ring

private theorem threeTap_iterate_mirror {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε) (c : ℤ) (s : FiniteConfiguration) (t : ℕ) :
    F^[t] (mirrorConfig c s) = mirrorConfig c (F^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      threeTap_mirror hF]

/-- The column of the reflected seed at the cell of reflection is the seed's own column. -/
private theorem threeTap_column_mirror {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε) (c : ℤ) (s : FiniteConfiguration) :
    observedColumn F (mirrorConfig c s) c = observedColumn F s c := by
  funext t
  unfold observedColumn
  rw [threeTap_iterate_mirror hF, mirrorConfig_apply, show 2 * c - c = c by ring]

/-- A seed symmetric about `c` and clear at `c` has a column at `c` that is clear throughout. -/
private theorem threeTap_column_eq_zero_of_symm {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε) (s : FiniteConfiguration) (c : ℤ)
    (hs : ∀ i, s (c + i) = s (c - i)) (h0 : s c = 0) (t : ℕ) : (F^[t] s) c = 0 := by
  have hm : mirrorConfig c s = s := by
    ext i
    rw [mirrorConfig_apply]
    have := hs (c - i)
    rw [show c + (c - i) = 2 * c - i by ring, show c - (c - i) = i by ring] at this
    exact this
  have hsym : ∀ t i, (F^[t] s) (c + i) = (F^[t] s) (c - i) := by
    intro t i
    have h := congrArg (fun g : FiniteConfiguration => g (c + i))
      (threeTap_iterate_mirror hF c s t)
    simp only [mirrorConfig_apply, hm] at h
    rw [h, show 2 * c - (c + i) = c - i by ring]
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    have e1 := hsym t 1
    rw [Function.iterate_succ_apply', hF, show c - 1 = c - 1 from rfl, ih]
    have e2 : (F^[t] s) (c + 1) = (F^[t] s) (c - 1) := e1
    rw [e2]
    have h2 : (2 : ZMod 2) = 0 := by decide
    linear_combination ((F^[t] s) (c - 1)) * h2

/-! ## The corner of an edge -/

/-- **The two conditions of the engine, at the right edge of a seed**: at a rule with the taps
`1, ε, 1` and the two-power identity, a seed set at `R`, clear beyond `R` and clear at and below
`2 * c - R` has, at the cell `c`, the column `u` that copies the block `ε * u q` at every large
power of two. -/
private theorem edge_copy {F : FiniteConfiguration → FiniteConfiguration} {ε : ZMod 2}
    (hF : ThreeTap F ε)
    (hid : ∀ (j : ℕ) (s : FiniteConfiguration) (i : ℤ),
      (F^[2 ^ j] s) i = s (i - 2 ^ j) + ε * s i + s (i + 2 ^ j))
    (s : FiniteConfiguration) (c R : ℤ) (hR2 : ∀ i, R < i → s i = 0)
    (hL : ∀ i, i ≤ 2 * c - R → s i = 0) (q : ℕ) :
    ∃ J, ∀ j ≥ J, observedColumn F s c (q + 2 ^ j) = ε * (F^[q] s) c := by
  refine ⟨(R + q - c).toNat + 1, fun j hj => ?_⟩
  have hlt : j < 2 ^ j := Nat.lt_two_pow_self
  have hlt' : (j : ℤ) < (2 : ℤ) ^ j := by exact_mod_cast hlt
  unfold observedColumn
  rw [add_comm, Function.iterate_add_apply, hid,
    threeTap_iterate_below hF s (2 * c - R) hL q (c - 2 ^ j) (by omega),
    threeTap_iterate_above hF s (R + 1) (fun i hi => hR2 i (by omega)) q (c + 2 ^ j)
      (by omega)]
  simp

private theorem edge_corner {F : FiniteConfiguration → FiniteConfiguration} {ε : ZMod 2}
    (hF : ThreeTap F ε)
    (hid : ∀ (j : ℕ) (s : FiniteConfiguration) (i : ℤ),
      (F^[2 ^ j] s) i = s (i - 2 ^ j) + ε * s i + s (i + 2 ^ j))
    (s : FiniteConfiguration) (c R : ℤ) (hR1 : s R = 1) (hR2 : ∀ i, R < i → s i = 0)
    (hL : ∀ i, i ≤ 2 * c - R → s i = 0) (m : ℕ) (hm : (m : ℤ) = R - c) (J : ℕ) :
    ∃ j ≥ J, observedColumn F s c (2 ^ j - m + 2 ^ j) ≠ ε * (F^[2 ^ j - m] s) c := by
  refine ⟨J + m, by omega, ?_⟩
  have hlt : J + m < 2 ^ (J + m) := Nat.lt_two_pow_self
  set j := J + m with hj
  have ht : 2 ^ j - m + m = 2 ^ j := by omega
  set t := 2 ^ j - m with htdef
  have hpow : (2 : ℤ) ^ j = (t : ℤ) + (m : ℤ) := by exact_mod_cast ht.symm
  unfold observedColumn
  rw [add_comm, Function.iterate_add_apply, hid,
    show c - (2 : ℤ) ^ j = 2 * c - R - t by omega,
    show c + (2 : ℤ) ^ j = R + t by omega,
    threeTap_iterate_below hF s (2 * c - R) hL t (2 * c - R - t) (by omega),
    threeTap_iterate_edge hF s R hR1 hR2 t]
  intro h
  have h1 : (1 : ZMod 2) = 0 := by linear_combination h
  exact absurd h1 (by decide)

/-- **The right edge of a seed forces a column that is not eventually periodic**: at a rule with the
taps `1, ε, 1` and the two-power identity, a seed set at `R`, clear beyond `R` and clear at and
below `2 * c - R` has a column at `c` that is not eventually periodic. -/
private theorem not_eventuallyPeriodic_of_right_edge {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε)
    (hid : ∀ (j : ℕ) (s : FiniteConfiguration) (i : ℤ),
      (F^[2 ^ j] s) i = s (i - 2 ^ j) + ε * s i + s (i + 2 ^ j))
    (s : FiniteConfiguration) (c R : ℤ) (hR1 : s R = 1) (hR2 : ∀ i, R < i → s i = 0)
    (hL : ∀ i, i ≤ 2 * c - R → s i = 0) :
    ¬ DrivenColumns.EventuallyPeriodic (observedColumn F s c) := by
  have hc : c < R := by
    by_contra h
    have := hL R (by omega)
    rw [hR1] at this
    exact absurd this (by decide)
  exact not_eventuallyPeriodic_of_two_pow_blocks (observedColumn F s c)
    (fun q => ε * (F^[q] s) c) (R - c).toNat
    (fun q => edge_copy hF hid s c R hR2 hL q)
    (edge_corner hF hid s c R hR1 hR2 hL _ (Int.toNat_of_nonneg (by omega)))

/-- **The left edge of a seed forces a column that is not eventually periodic**, by reflecting the
seed in `c`. -/
private theorem not_eventuallyPeriodic_of_left_edge {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε)
    (hid : ∀ (j : ℕ) (s : FiniteConfiguration) (i : ℤ),
      (F^[2 ^ j] s) i = s (i - 2 ^ j) + ε * s i + s (i + 2 ^ j))
    (s : FiniteConfiguration) (c L : ℤ) (hL1 : s L = 1) (hL2 : ∀ i, i < L → s i = 0)
    (hR : ∀ i, 2 * c - L ≤ i → s i = 0) :
    ¬ DrivenColumns.EventuallyPeriodic (observedColumn F s c) := by
  rw [← threeTap_column_mirror hF c s]
  refine not_eventuallyPeriodic_of_right_edge hF hid (mirrorConfig c s) c (2 * c - L) ?_ ?_ ?_
  · rw [mirrorConfig_apply, show 2 * c - (2 * c - L) = L by ring, hL1]
  · intro i hi
    rw [mirrorConfig_apply]
    exact hL2 _ (by omega)
  · intro i hi
    rw [mirrorConfig_apply]
    exact hR _ (by omega)

/-! ## An asymmetric seed -/

/-- **A seed not mirror symmetric about `c` has a column at `c` that is not eventually periodic**,
at a rule with the taps `1, ε, 1` and the two-power identity. The seed is split at the largest
offset `y` where it is asymmetric: the part beyond `y` is symmetric about `c` and clear at `c`, so
its column is clear throughout, and the part within `y` has exactly one of its two cells at the
offset `y` set, which is an edge. -/
private theorem not_eventuallyPeriodic_of_asymm {F : FiniteConfiguration → FiniteConfiguration}
    {ε : ZMod 2} (hF : ThreeTap F ε)
    (hid : ∀ (j : ℕ) (s : FiniteConfiguration) (i : ℤ),
      (F^[2 ^ j] s) i = s (i - 2 ^ j) + ε * s i + s (i + 2 ^ j))
    (s : FiniteConfiguration) (c : ℤ) (hs : ¬ ∀ i, s (c + i) = s (c - i)) :
    ¬ DrivenColumns.EventuallyPeriodic (observedColumn F s c) := by
  classical
  -- the asymmetric offsets, as natural numbers
  have hex : ∃ n : ℕ, s (c + n) ≠ s (c - n) := by
    obtain ⟨i, hi⟩ := not_forall.mp hs
    rcases le_or_gt 0 i with h | h
    · exact ⟨i.toNat, by rwa [Int.toNat_of_nonneg h]⟩
    · refine ⟨(-i).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega), sub_neg_eq_add, ← sub_eq_add_neg]
      exact fun h' => hi h'.symm
  -- beyond a bound the seed is clear at both cells
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ n : ℕ, B < n → s (c + n) = 0 ∧ s (c - n) = 0 := by
    refine ⟨s.support.sup Int.natAbs + c.natAbs, fun n hn => ⟨?_, ?_⟩⟩
    · by_contra h
      have := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.mpr h)
      omega
    · by_contra h
      have := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.mpr h)
      omega
  obtain ⟨n₀, hn₀⟩ := hex
  have hn₀B : n₀ ≤ B := by
    by_contra h
    obtain ⟨h1, h2⟩ := hB n₀ (by omega)
    exact hn₀ (h1.trans h2.symm)
  set y := Nat.findGreatest (fun n : ℕ => s (c + n) ≠ s (c - n)) B with hy
  have hyspec : s (c + y) ≠ s (c - y) :=
    Nat.findGreatest_spec (P := fun n : ℕ => s (c + n) ≠ s (c - n)) hn₀B hn₀
  have hymax : ∀ n : ℕ, y < n → s (c + n) = s (c - n) := by
    intro n hn
    by_cases hnB : n ≤ B
    · by_contra h
      exact Nat.findGreatest_is_greatest (P := fun n : ℕ => s (c + n) ≠ s (c - n)) hn hnB h
    · obtain ⟨h1, h2⟩ := hB n (by omega)
      exact h1.trans h2.symm
  -- the split
  obtain ⟨sin, sout, hsum, hin1, hin2, hout1, hout2⟩ : ∃ sin sout : FiniteConfiguration,
      s = sin + sout ∧ (∀ i, c - y ≤ i → i ≤ c + y → sin i = s i) ∧
      (∀ i, (i < c - y ∨ c + y < i) → sin i = 0) ∧
      (∀ i, c - y ≤ i → i ≤ c + y → sout i = 0) ∧
      (∀ i, (i < c - y ∨ c + y < i) → sout i = s i) := by
    refine ⟨s.filter (fun i => c - y ≤ i ∧ i ≤ c + y),
      s.filter (fun i => ¬ (c - y ≤ i ∧ i ≤ c + y)), (Finsupp.filter_add_filter_not _ _).symm,
      ?_, ?_, ?_, ?_⟩
    · intro i h1 h2
      exact Finsupp.filter_apply_pos _ _ ⟨h1, h2⟩
    · intro i h
      exact Finsupp.filter_apply_neg _ _ (by omega)
    · intro i h1 h2
      exact Finsupp.filter_apply_neg _ _ (by omega)
    · intro i h
      exact Finsupp.filter_apply_pos _ _ (by omega)
  have hsymm : ∀ i, sout (c + i) = sout (c - i) := by
    intro i
    by_cases hi : -(y : ℤ) ≤ i ∧ i ≤ y
    · rw [hout1 _ (by omega) (by omega), hout1 _ (by omega) (by omega)]
    · rw [hout2 _ (by omega), hout2 _ (by omega)]
      rcases le_or_gt 0 i with h | h
      · have := hymax i.toNat (by omega)
        rwa [Int.toNat_of_nonneg h] at this
      · have := hymax (-i).toNat (by omega)
        rw [Int.toNat_of_nonneg (by omega), sub_neg_eq_add, ← sub_eq_add_neg] at this
        exact this.symm
  have hcol : observedColumn F s c = observedColumn F sin c := by
    funext t
    unfold observedColumn
    have h0 : sout c = 0 := hout1 c (by omega) (by omega)
    have hz := threeTap_column_eq_zero_of_symm hF sout c hsymm h0 t
    conv_lhs => rw [hsum]
    rw [threeTap_iterate_add hF, hz, add_zero]
  rw [hcol]
  have hc1 : sin (c + y) = s (c + y) := hin1 _ (by omega) le_rfl
  have hc2 : sin (c - y) = s (c - y) := hin1 _ le_rfl (by omega)
  have hcases : ∀ a b : ZMod 2, a ≠ b → (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by decide
  rcases hcases _ _ hyspec with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine not_eventuallyPeriodic_of_right_edge hF hid sin c (c + y) (by rw [hc1, h1]) ?_ ?_
    · intro i hi
      exact hin2 i (Or.inr hi)
    · intro i hi
      rcases lt_or_ge i (c - y) with h | h
      · exact hin2 i (Or.inl h)
      · have : i = c - y := by omega
        rw [this, hc2, h2]
  · refine not_eventuallyPeriodic_of_left_edge hF hid sin c (c - y) (by rw [hc2, h2]) ?_ ?_
    · intro i hi
      exact hin2 i (Or.inl hi)
    · intro i hi
      rcases lt_or_ge (c + y) i with h | h
      · exact hin2 i (Or.inr h)
      · have : i = c + y := by omega
        rw [this, hc1, h1]

/-! ## Rules `90` and `150` -/

private theorem threeTap_f90 : ThreeTap (finRule f90 hq90) 0 := by
  intro s i
  rw [finRule_apply]
  simp [f90]

private theorem threeTap_f150 : ThreeTap (finRule f150 hq150) 1 := by
  intro s i
  rw [finRule_apply]
  simp [f150]

private theorem two_pow_f90 (j : ℕ) (s : FiniteConfiguration) (i : ℤ) :
    ((finRule f90 hq90)^[2 ^ j] s) i = s (i - 2 ^ j) + 0 * s i + s (i + 2 ^ j) := by
  rw [iterate_two_pow_f90]
  simp

private theorem two_pow_f150 (j : ℕ) (s : FiniteConfiguration) (i : ℤ) :
    ((finRule f150 hq150)^[2 ^ j] s) i = s (i - 2 ^ j) + 1 * s i + s (i + 2 ^ j) :=
  by rw [iterate_two_pow_f150, one_mul]

/-! ## The bridge to the iffs of `rule30-open`

A finite seed read as a row of `Bool`s, a cell set when it is `1`, runs under our rule as the row
runs under the rule's `Bool` form in the `rule30-open` repository (`Rule30Open.iter90`,
`Rule30Open.iter150`), and the injective reading carries eventual periodicity of the column and
the mirror condition both ways. -/

/-- A cell of `ZMod 2` read as a `Bool`: set when it is `1`. -/
private def toBool (a : ZMod 2) : Bool := decide (a = 1)

private theorem toBool_injective : Function.Injective toBool := by
  decide +revert

private theorem toBool_add (a b : ZMod 2) : toBool (a + b) = xor (toBool a) (toBool b) := by
  revert a b; decide

private theorem toBool_step_f90 (x : ℤ → ZMod 2) :
    (fun i => toBool (LocalRuleColumns.step f90 x i)) =
      Rule30Open.step90 (fun i => toBool (x i)) := by
  funext i
  simp [LocalRuleColumns.step, Rule30Open.step90, f90, toBool_add]

private theorem toBool_step_f150 (x : ℤ → ZMod 2) :
    (fun i => toBool (LocalRuleColumns.step f150 x i)) =
      Rule30Open.stepLin true (fun i => toBool (x i)) := by
  funext i
  simp [LocalRuleColumns.step, Rule30Open.stepLin, f150, toBool_add]

private theorem toBool_iterate_f90 (x : ℤ → ZMod 2) (t : ℕ) :
    (fun i => toBool ((LocalRuleColumns.step f90)^[t] x i)) =
      Rule30Open.iter90 (fun i => toBool (x i)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', toBool_step_f90, ih]
      rfl

private theorem toBool_iterate_f150 (x : ℤ → ZMod 2) (t : ℕ) :
    (fun i => toBool ((LocalRuleColumns.step f150)^[t] x i)) =
      Rule30Open.iterLin true (fun i => toBool (x i)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', toBool_step_f150, ih]
      rfl

private theorem eventuallyPeriodic_toBool_iff (u : ℕ → ZMod 2) :
    DrivenColumns.EventuallyPeriodic u ↔
      Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic (fun t => toBool (u t)) := by
  constructor
  · rintro ⟨P, N, hP, h⟩
    exact ⟨N, P, hP, fun t ht => by simp only [h t ht]⟩
  · rintro ⟨N, P, hP, h⟩
    exact ⟨P, N, hP, fun t ht => toBool_injective (h t ht)⟩

private theorem toBool_support (s : FiniteConfiguration) :
    ∃ N : ℕ, ∀ x : ℤ, N < x.natAbs → toBool (s x) = false := by
  refine ⟨s.support.sup Int.natAbs, fun x hx => ?_⟩
  have : x ∉ s.support := fun hmem => by
    have := Finset.le_sup (f := Int.natAbs) hmem
    omega
  rw [Finsupp.notMem_support_iff.mp this]
  rfl

private theorem toBool_mirror_iff (s : FiniteConfiguration) (c : ℤ) :
    (∀ m : ℤ, toBool (s (c + m)) = toBool (s (c - m))) ↔ ∀ i, s (c + i) = s (c - i) :=
  ⟨fun h i => toBool_injective (h i), fun h i => by rw [h i]⟩

/-- **Rule `90`: the column from a finite seed at a cell is eventually periodic exactly when the
seed is mirror symmetric about the cell** ([RuleSpace] §4 Proposition 4.8, row RS-92). The proof is
the bridge to `Rule30Open.iter90_column_periodic_iff` of the `rule30-open` repository, which proves
the statement for `Bool` rows. -/
theorem eventuallyPeriodic_observedColumn_f90_iff (s₀ : FiniteConfiguration) (c : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f90 hq90) s₀ c) ↔
      ∀ i, s₀ (c + i) = s₀ (c - i) := by
  obtain ⟨N, hN⟩ := toBool_support s₀
  have hcol : (fun t => toBool (observedColumn (finRule f90 hq90) s₀ c t)) =
      fun t => Rule30Open.iter90 (fun i => toBool (s₀ i)) t c := by
    funext t
    have h := congrFun (toBool_iterate_f90 (⇑s₀) t) c
    simpa [observedColumn, coe_finRule_iterate] using h
  rw [eventuallyPeriodic_toBool_iff, hcol, Rule30Open.iter90_column_periodic_iff _ N hN c]
  exact toBool_mirror_iff s₀ c

/-- **Rule `150`: the column from a finite seed at a cell is eventually periodic exactly when the
seed is mirror symmetric about the cell** ([RuleSpace] §4 Proposition 4.8, row RS-92). The proof is
the bridge to `Rule30Open.iter150_column_periodic_iff` of the `rule30-open` repository, which
proves the statement for `Bool` rows. -/
theorem eventuallyPeriodic_observedColumn_f150_iff (s₀ : FiniteConfiguration) (c : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f150 hq150) s₀ c) ↔
      ∀ i, s₀ (c + i) = s₀ (c - i) := by
  obtain ⟨N, hN⟩ := toBool_support s₀
  have hcol : (fun t => toBool (observedColumn (finRule f150 hq150) s₀ c t)) =
      fun t => Rule30Open.iter150 (fun i => toBool (s₀ i)) t c := by
    funext t
    have h := congrFun (toBool_iterate_f150 (⇑s₀) t) c
    simpa [observedColumn, coe_finRule_iterate, Rule30Open.iter150_eq] using h
  rw [eventuallyPeriodic_toBool_iff, hcol, Rule30Open.iter150_column_periodic_iff _ N hN c]
  exact toBool_mirror_iff s₀ c

/-! ## The classes that step as rule `90` -/

/-- **One-parity seeds: the column is eventually periodic exactly when the seed is mirror symmetric
about the cell**, at every rule that agrees with rule `90` off adjacent cells
([RuleSpace] §4 Proposition 4.8, row RS-92), by the orbit identity of the class and
`eventuallyPeriodic_observedColumn_f90_iff`. -/
theorem eventuallyPeriodic_observedColumn_iff_of_oneParity (f : LocalRule)
    (h : LocalRule.AgreesOffAdjacent f) (s₀ : FiniteConfiguration) (hs : s₀.OneParity) (c : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f h.1) s₀ c) ↔
      ∀ i, s₀ (c + i) = s₀ (c - i) := by
  have e : observedColumn (finRule f h.1) s₀ c = observedColumn (finRule f90 hq90) s₀ c := by
    funext t
    unfold observedColumn
    rw [FiniteConfiguration.OneParity.iterate_eq_f90 f h s₀ hs t]
  rw [e]
  exact eventuallyPeriodic_observedColumn_f90_iff s₀ c

/-- The joint-satisfiability witness for the one-parity transfer: rule `18` agrees with rule `90`
off adjacent cells, and the seed at cells `0` and `2` is of one parity. -/
theorem eventuallyPeriodic_observedColumn_iff_of_oneParity_nonvacuous :
    LocalRule.AgreesOffAdjacent f18 ∧
      FiniteConfiguration.OneParity (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1) := by
  refine ⟨agreesOffAdjacent_f18, ?_⟩
  intro i j hi hj
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hi hj
  rw [even_iff_two_dvd]
  split_ifs at hi hj <;> first | omega | simp_all

/-- **Doubled seeds: the column at the doubled cell is not eventually periodic when the seed is not
mirror symmetric about the cell** ([RuleSpace] §4 Proposition 4.8, row RS-92), at every rule that
agrees with rule `90` where two adjacent cells are equal. Two steps of the rule on a doubled seed
are the doubled step of rule `90`, so the even-time subsequence of the column is rule `90`'s
column of the undoubled seed. -/
theorem not_eventuallyPeriodic_observedColumn_dbl (f : LocalRule) (hq : f 0 0 0 = 0)
    (hA : LocalRule.DoubledAgree f) (x : FiniteConfiguration) (c : ℤ)
    (hx : ¬ ∀ i, x (c + i) = x (c - i)) :
    ¬ DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) (dbl x) (2 * c)) := by
  have key : ∀ k : ℕ, (finRule f hq)^[2 * k] (dbl x) = dbl ((finRule f90 hq90)^[k] x) := by
    intro k
    rw [Function.iterate_mul]
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply' ((finRule f hq)^[2]) k, ih,
        Function.iterate_succ_apply' (finRule f90 hq90) k, LocalRule.finRule_two_dbl f hq hA]
  have heven : ∀ k : ℕ, observedColumn (finRule f hq) (dbl x) (2 * c) (2 * k) =
      observedColumn (finRule f90 hq90) x c k := by
    intro k
    unfold observedColumn
    rw [key k, FiniteConfiguration.dbl_apply, show 2 * c / 2 = c by omega]
  rintro ⟨P, N, hP, hper⟩
  refine hx ((eventuallyPeriodic_observedColumn_f90_iff x c).mp ⟨P, N, hP, fun k hk => ?_⟩)
  rw [← heven, ← heven, show 2 * (k + P) = (2 * k + P) + P by ring,
    hper _ (by omega), hper _ (by omega)]

/-- The joint-satisfiability witness for the doubled transfer: rule `126` agrees with rule `90`
where two adjacent cells are equal, and the seed at cells `0` and `1` is not mirror symmetric
about `0`. -/
theorem not_eventuallyPeriodic_observedColumn_dbl_nonvacuous :
    LocalRule.DoubledAgree f126 ∧
      ¬ ∀ i : ℤ, ((Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 :
          FiniteConfiguration) : ℤ → ZMod 2) (0 + i) =
        ((Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 :
          FiniteConfiguration) : ℤ → ZMod 2) (0 - i) := by
  refine ⟨doubledAgree_f126, fun h => ?_⟩
  have := h 1
  simp at this

/-! ## The leftmost cell of a seed -/

/-- A seed of two or more set cells is not mirror symmetric about its leftmost set cell: the
cell as far right as another set cell has no set partner on the left. -/
private theorem not_mirror_min (s₀ : FiniteConfiguration) (hs : s₀.support.Nonempty)
    (h2 : 1 < s₀.support.card) :
    ¬ ∀ i, s₀ (s₀.support.min' hs + i) = s₀ (s₀.support.min' hs - i) := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  have hmin := s₀.support.min'_mem hs
  obtain ⟨b', hb', hne⟩ : ∃ b' ∈ s₀.support, b' ≠ s₀.support.min' hs := by
    by_cases hae : a = s₀.support.min' hs
    · exact ⟨b, hb, fun hbe => hab (hae.trans hbe.symm)⟩
    · exact ⟨a, ha, hae⟩
  have hle : s₀.support.min' hs ≤ b' := Finset.min'_le _ _ hb'
  have h1 := h (b' - s₀.support.min' hs)
  rw [show s₀.support.min' hs + (b' - s₀.support.min' hs) = b' by ring] at h1
  have h3 : s₀ (s₀.support.min' hs - (b' - s₀.support.min' hs)) = 0 := by
    by_contra hc
    have := Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hc)
    omega
  rw [h3] at h1
  exact (Finsupp.mem_support_iff.mp hb') h1

/-- **Rule `90`: a seed of two or more set cells has a column at its leftmost set cell that is not
eventually periodic** ([RuleSpace] §4 Proposition 4.8, row RS-92). -/
theorem not_eventuallyPeriodic_observedColumn_min_f90 (s₀ : FiniteConfiguration)
    (hs : s₀.support.Nonempty) (h2 : 1 < s₀.support.card) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedColumn (finRule f90 hq90) s₀ (s₀.support.min' hs)) :=
  fun h => not_mirror_min s₀ hs h2
    ((eventuallyPeriodic_observedColumn_f90_iff s₀ _).mp h)

/-- **Rule `150`: a seed of two or more set cells has a column at its leftmost set cell that is not
eventually periodic** ([RuleSpace] §4 Proposition 4.8, row RS-92). -/
theorem not_eventuallyPeriodic_observedColumn_min_f150 (s₀ : FiniteConfiguration)
    (hs : s₀.support.Nonempty) (h2 : 1 < s₀.support.card) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedColumn (finRule f150 hq150) s₀ (s₀.support.min' hs)) :=
  fun h => not_mirror_min s₀ hs h2
    ((eventuallyPeriodic_observedColumn_f150_iff s₀ _).mp h)

/-- **One-parity seeds: a seed of two or more set cells has a column at its leftmost set cell that
is not eventually periodic**, at every rule that agrees with rule `90` off adjacent cells
([RuleSpace] §4 Proposition 4.8, row RS-92). -/
theorem not_eventuallyPeriodic_observedColumn_min_of_oneParity (f : LocalRule)
    (h : LocalRule.AgreesOffAdjacent f) (s₀ : FiniteConfiguration) (hpar : s₀.OneParity)
    (hs : s₀.support.Nonempty) (h2 : 1 < s₀.support.card) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedColumn (finRule f h.1) s₀ (s₀.support.min' hs)) :=
  fun hp => not_mirror_min s₀ hs h2
    ((eventuallyPeriodic_observedColumn_iff_of_oneParity f h s₀ hpar _).mp hp)

/-- **Doubled seeds: a seed of two or more set cells has a doubled column, at twice its leftmost
set cell, that is not eventually periodic**, at every rule that agrees with rule `90` where two
adjacent cells are equal ([RuleSpace] §4 Proposition 4.8, row RS-92). -/
theorem not_eventuallyPeriodic_observedColumn_dbl_min (f : LocalRule) (hq : f 0 0 0 = 0)
    (hA : LocalRule.DoubledAgree f) (x : FiniteConfiguration) (hx : x.support.Nonempty)
    (h2 : 1 < x.support.card) :
    ¬ DrivenColumns.EventuallyPeriodic
      (observedColumn (finRule f hq) (dbl x) (2 * x.support.min' hx)) :=
  not_eventuallyPeriodic_observedColumn_dbl f hq hA x _ (not_mirror_min x hx h2)

private theorem two_cells_support (a b : ℤ) (h : a ≠ b) :
    (Finsupp.single a (1 : ZMod 2) + Finsupp.single b 1).support.Nonempty ∧
      1 < (Finsupp.single a (1 : ZMod 2) + Finsupp.single b 1).support.card := by
  have ha : a ∈ (Finsupp.single a (1 : ZMod 2) + Finsupp.single b 1).support := by
    rw [Finsupp.mem_support_iff]
    simp [h.symm]
  have hb : b ∈ (Finsupp.single a (1 : ZMod 2) + Finsupp.single b 1).support := by
    rw [Finsupp.mem_support_iff]
    simp [h]
  exact ⟨⟨a, ha⟩, Finset.one_lt_card.mpr ⟨a, ha, b, hb, h⟩⟩

/-- The joint-satisfiability witness for rule `90`: the seed at cells `0` and `1` has a nonempty
support of more than one cell. -/
theorem not_eventuallyPeriodic_observedColumn_min_f90_nonvacuous :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1).support.Nonempty ∧
      1 < (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1).support.card :=
  two_cells_support 0 1 (by decide)

/-- The joint-satisfiability witness for rule `150`: the seed at cells `0` and `1` has a nonempty
support of more than one cell. -/
theorem not_eventuallyPeriodic_observedColumn_min_f150_nonvacuous :
    (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1).support.Nonempty ∧
      1 < (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1).support.card :=
  two_cells_support 0 1 (by decide)

/-- The joint-satisfiability witness for the one-parity class: rule `18` agrees with rule `90` off
adjacent cells, and the seed at cells `0` and `2` is of one parity with a nonempty support of more
than one cell. -/
theorem not_eventuallyPeriodic_observedColumn_min_of_oneParity_nonvacuous :
    LocalRule.AgreesOffAdjacent f18 ∧
      FiniteConfiguration.OneParity
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1) ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1).support.Nonempty ∧
      1 < (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 2 1).support.card :=
  ⟨eventuallyPeriodic_observedColumn_iff_of_oneParity_nonvacuous.1,
    eventuallyPeriodic_observedColumn_iff_of_oneParity_nonvacuous.2,
    (two_cells_support 0 2 (by decide)).1, (two_cells_support 0 2 (by decide)).2⟩

/-- The joint-satisfiability witness for the doubled class: rule `126` agrees with rule `90` where
two adjacent cells are equal, and the seed at cells `0` and `1` has a nonempty support of more
than one cell. -/
theorem not_eventuallyPeriodic_observedColumn_dbl_min_nonvacuous :
    LocalRule.DoubledAgree f126 ∧
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1).support.Nonempty ∧
      1 < (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1).support.card :=
  ⟨doubledAgree_f126, (two_cells_support 0 1 (by decide)).1,
    (two_cells_support 0 1 (by decide)).2⟩

/-- The joint-satisfiability witness for the engine, at rule `90` from the seed at cells `0` and
`1`, the cell `0`, the blocks `0` and the corner offset `1`: both hypotheses hold at once, so the
column there is not eventually periodic by the engine. -/
theorem not_eventuallyPeriodic_of_two_pow_blocks_nonvacuous :
    (∀ q, ∃ J, ∀ j ≥ J,
      observedColumn (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1)
        0 (q + 2 ^ j) = (fun _ : ℕ => (0 : ZMod 2)) q) ∧
    (∀ J, ∃ j ≥ J,
      observedColumn (finRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1)
        0 (2 ^ j - 1 + 2 ^ j) ≠ (fun _ : ℕ => (0 : ZMod 2)) (2 ^ j - 1)) := by
  have hR1 : ((Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 :
      FiniteConfiguration) : ℤ → ZMod 2) 1 = 1 := by
    simp
  have hR2 : ∀ i : ℤ, 1 < i →
      ((Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 :
        FiniteConfiguration) : ℤ → ZMod 2) i = 0 := by
    intro i hi
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> first | omega | rfl
  have hL : ∀ i : ℤ, i ≤ 2 * 0 - 1 →
      ((Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1 :
        FiniteConfiguration) : ℤ → ZMod 2) i = 0 := by
    intro i hi
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> first | omega | rfl
  refine ⟨fun q => ?_, fun J => ?_⟩
  · obtain ⟨J, hJ⟩ := edge_copy threeTap_f90 two_pow_f90 _ 0 1 hR2 hL q
    exact ⟨J, fun j hj => by rw [hJ j hj, zero_mul]⟩
  · obtain ⟨j, hj, hne⟩ := edge_corner threeTap_f90 two_pow_f90 _ 0 1 hR1 hR2 hL 1 (by norm_num) J
    exact ⟨j, hj, by simpa using hne⟩

/-! ## A seed whose orbit reaches one parity -/

/-- Eventual periodicity does not see a shift of the index. -/
private theorem eventuallyPeriodic_add_iff {α : Type*} (u : ℕ → α) (k : ℕ) :
    DrivenColumns.EventuallyPeriodic (fun t => u (t + k)) ↔ DrivenColumns.EventuallyPeriodic u := by
  constructor
  · rintro ⟨P, N, hP, hper⟩
    refine ⟨P, N + k, hP, fun t ht => ?_⟩
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ t by omega)
    have h := hper s (by omega)
    simp only at h
    rw [show k + s + P = s + P + k by ring, show k + s = s + k by ring]
    exact h
  · rintro ⟨P, N, hP, hper⟩
    refine ⟨P, N, hP, fun t ht => ?_⟩
    simp only
    rw [show t + P + k = t + k + P by ring]
    exact hper (t + k) (by omega)

/-- The column from the `k`-th iterate of a seed is the column from the seed, read from step `k`. -/
private theorem observedColumn_iterate_add (U : FiniteConfiguration → FiniteConfiguration)
    (s₀ : FiniteConfiguration) (c : ℤ) (k : ℕ) :
    observedColumn U (U^[k] s₀) c = fun t => observedColumn U s₀ c (t + k) := by
  funext t
  unfold observedColumn
  rw [← Function.iterate_add_apply]

/-- **A seed whose orbit reaches a state of one parity: the column is eventually periodic exactly
when that state is mirror symmetric about the cell** ([RuleSpace] §4 Proposition 4.8, row RS-92),
at every rule that agrees with rule `90` off adjacent cells. The column from the seed, read from
step `k` on, is the column from the `k`-th iterate, eventual periodicity does not see the first `k`
steps, and `eventuallyPeriodic_observedColumn_iff_of_oneParity` reads the iterate. -/
theorem eventuallyPeriodic_observedColumn_iff_of_iterate_oneParity (f : LocalRule)
    (h : LocalRule.AgreesOffAdjacent f) (s₀ : FiniteConfiguration) (k : ℕ)
    (hk : ((finRule f h.1)^[k] s₀).OneParity) (c : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f h.1) s₀ c) ↔
      ∀ i, ((finRule f h.1)^[k] s₀) (c + i) = ((finRule f h.1)^[k] s₀) (c - i) := by
  rw [← eventuallyPeriodic_add_iff (observedColumn (finRule f h.1) s₀ c) k,
    ← observedColumn_iterate_add]
  exact eventuallyPeriodic_observedColumn_iff_of_oneParity f h _ hk c

/-- A state that reads a list from a cell is of one parity when the set entries of the list sit at
positions of one parity. -/
private theorem oneParity_of_coe_listConfig (M : List (ZMod 2)) (a : ℤ) (s : FiniteConfiguration)
    (hs : ⇑s = listConfig M a)
    (hM : ∀ m, m < M.length → ∀ n, n < M.length → M.getD m 0 ≠ 0 → M.getD n 0 ≠ 0 →
      m % 2 = n % 2) :
    s.OneParity := by
  have key : ∀ i, s i ≠ 0 → ∃ m, m < M.length ∧ M.getD m 0 ≠ 0 ∧ (m : ℤ) = i - a := by
    intro i hi
    have h1 : listVal M (i - a) ≠ 0 := by
      intro hz
      apply hi
      rw [show s i = listConfig M a i from congrFun hs i]
      exact hz
    have h0 : 0 ≤ i - a := by
      by_contra hneg
      exact h1 (by
        rw [listVal]
        exact ite_eq_right_iff.mpr fun h => absurd h hneg)
    simp only [listVal, h0, ite_true] at h1
    refine ⟨(i - a).toNat, ?_, h1, Int.toNat_of_nonneg h0⟩
    by_contra hlen
    apply h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  intro i j hi hj
  obtain ⟨m, hm, hm0, hmi⟩ := key i hi
  obtain ⟨n, hn, hn0, hnj⟩ := key j hj
  have := hM m hm n hn hm0 hn0
  exact ⟨(i - j) / 2, by omega⟩

/-- The `k`-th iterate of a list seed is of one parity when the list `k` steps of the list
simulation on has its set entries at positions of one parity. -/
private theorem oneParity_iterate_listSeed (f : LocalRule) (hq : f 0 0 0 = 0) (L : List (ZMod 2))
    (k : ℕ)
    (hM : ∀ m, m < ((simStep f)^[k] L).length → ∀ n, n < ((simStep f)^[k] L).length →
      ((simStep f)^[k] L).getD m 0 ≠ 0 → ((simStep f)^[k] L).getD n 0 ≠ 0 → m % 2 = n % 2) :
    ((finRule f hq)^[k] (listSeed L)).OneParity :=
  oneParity_of_coe_listConfig _ _ _ (coe_iterate_listSeed f hq L k) hM

/-- A list seed whose `k`-th iterate is of one parity and asymmetric about the cell `0` at the
offset `i` has a column at `0` that is not eventually periodic. -/
private theorem not_eventuallyPeriodic_of_reaches_oneParity (f : LocalRule)
    (h : LocalRule.AgreesOffAdjacent f) (L : List (ZMod 2)) (k : ℕ) (i : ℤ)
    (hM : ∀ m, m < ((simStep f)^[k] L).length → ∀ n, n < ((simStep f)^[k] L).length →
      ((simStep f)^[k] L).getD m 0 ≠ 0 → ((simStep f)^[k] L).getD n 0 ≠ 0 → m % 2 = n % 2)
    (hasym : listVal ((simStep f)^[k] L) ((k : ℤ) + i) ≠
      listVal ((simStep f)^[k] L) ((k : ℤ) - i)) :
    ¬ DrivenColumns.EventuallyPeriodic (observedColumn (finRule f h.1) (listSeed L) 0) := by
  intro hep
  have hpar := oneParity_iterate_listSeed f h.1 L k hM
  have hsym := (eventuallyPeriodic_observedColumn_iff_of_iterate_oneParity f h (listSeed L) k hpar
    0).mp hep i
  have e : ∀ x : ℤ, ((finRule f h.1)^[k] (listSeed L)) x =
      listVal ((simStep f)^[k] L) (x + k) := by
    intro x
    have := congrFun (coe_iterate_listSeed f h.1 L k) x
    rw [show ((finRule f h.1)^[k] (listSeed L)) x = ⇑((finRule f h.1)^[k] (listSeed L)) x from rfl,
      this]
    unfold listConfig
    congr 1
    ring
  rw [e, e, zero_add, zero_sub, add_comm (-i) (k : ℤ), ← sub_eq_add_neg] at hsym
  exact hasym (by rw [add_comm]; exact hsym)

/-- The joint-satisfiability witness for the shift in time: rule `18` agrees with rule `90` off
adjacent cells, and the first iterate of the seed at cells `0`, `1` and `2`, the state at cells
`-1` and `3`, is of one parity. -/
theorem eventuallyPeriodic_observedColumn_iff_of_iterate_oneParity_nonvacuous :
    LocalRule.AgreesOffAdjacent f18 ∧
      FiniteConfiguration.OneParity
        ((finRule f18 agreesOffAdjacent_f18.1)^[1] (listSeed [1, 1, 1])) :=
  ⟨agreesOffAdjacent_f18,
    oneParity_iterate_listSeed f18 agreesOffAdjacent_f18.1 [1, 1, 1] 1 (by decide +kernel)⟩

private theorem agreesOffAdjacent_f146' : LocalRule.AgreesOffAdjacent f146 := by
  unfold LocalRule.AgreesOffAdjacent f146; decide

/-- **Rule `18`: a seed that reaches a state of one parity that is not mirror symmetric about the
seed's leftmost cell has a column there that is not eventually periodic** ([RuleSpace] §4
Proposition 4.8, row RS-92), at fourteen instances over seven seeds of diameter at most five read
from cell `0`. -/
theorem not_eventuallyPeriodic_observedColumn_f18_reaches_oneParity :
    ∀ L ∈ ([[1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 1, 0, 1], [1, 0, 0, 1, 1], [1, 1, 0, 1, 1],
        [1, 0, 1, 1, 1], [1, 1, 1, 1, 1]] : List (List (ZMod 2))),
      ¬ DrivenColumns.EventuallyPeriodic
        (observedColumn (finRule f18 agreesOffAdjacent_f18.1) (listSeed L) 0) := by
  intro L hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_eventuallyPeriodic_of_reaches_oneParity f18 agreesOffAdjacent_f18 _ 1 3
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f18 agreesOffAdjacent_f18 _ 8 12
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f18 agreesOffAdjacent_f18 _ 1 5
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f18 agreesOffAdjacent_f18 _ 8 12
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f18 agreesOffAdjacent_f18 _ 1 5
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f18 agreesOffAdjacent_f18 _ 1 5
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f18 agreesOffAdjacent_f18 _ 1 5
      (by decide +kernel) (by decide +kernel)

/-- **Rule `146`: the same seeds** ([RuleSpace] §4 Proposition 4.8, row RS-92): each reaches a state
of one parity that is not mirror symmetric about cell `0`, the first at the step `1` for six of the
seeds, at the step `8` for two of them, and at the step `2` for the seed `11111`. -/
theorem not_eventuallyPeriodic_observedColumn_f146_reaches_oneParity :
    ∀ L ∈ ([[1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 1, 0, 1], [1, 0, 0, 1, 1], [1, 1, 0, 1, 1],
        [1, 0, 1, 1, 1], [1, 1, 1, 1, 1]] : List (List (ZMod 2))),
      ¬ DrivenColumns.EventuallyPeriodic
        (observedColumn (finRule f146 hq146) (listSeed L) 0) := by
  intro L hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_eventuallyPeriodic_of_reaches_oneParity f146 agreesOffAdjacent_f146' _ 1 3
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f146 agreesOffAdjacent_f146' _ 8 12
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f146 agreesOffAdjacent_f146' _ 1 5
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f146 agreesOffAdjacent_f146' _ 8 12
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f146 agreesOffAdjacent_f146' _ 1 5
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f146 agreesOffAdjacent_f146' _ 1 5
      (by decide +kernel) (by decide +kernel)
  · exact not_eventuallyPeriodic_of_reaches_oneParity f146 agreesOffAdjacent_f146' _ 2 6
      (by decide +kernel) (by decide +kernel)

end ECA

/-! ## Axiom audit -/

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_of_two_pow_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_of_two_pow_blocks

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_of_two_pow_blocks_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_of_two_pow_blocks_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_f90_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_f90_iff

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_f150_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_f150_iff

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_iff_of_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_iff_of_oneParity

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_iff_of_oneParity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_iff_of_oneParity_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_dbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_dbl

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_dbl_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_dbl_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_min_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_min_f90

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_min_f90_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_min_f90_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_min_f150' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_min_f150

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_min_f150_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_min_f150_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_min_of_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_min_of_oneParity

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_min_of_oneParity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_min_of_oneParity_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_dbl_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_dbl_min

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_dbl_min_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_dbl_min_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_iff_of_iterate_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_iff_of_iterate_oneParity

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_iff_of_iterate_oneParity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_iff_of_iterate_oneParity_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_f18_reaches_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_f18_reaches_oneParity

set_option linter.style.longLine false in
/-- info: 'ECA.not_eventuallyPeriodic_observedColumn_f146_reaches_oneParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_eventuallyPeriodic_observedColumn_f146_reaches_oneParity
