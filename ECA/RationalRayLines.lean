module

public import ECA.RationalRaySeeds
public import ECA.RationalRayPairs

/-!
# The lines of rule `90` from the single seed that read a one past every step
([RuleSpace] §5 Proposition 5.6)

The converse of `[RuleSpace] §5 Proposition 5.3` at the single seed, registered as [RuleSpace] §5
Proposition 5.6, row RS-17. A line of slope `p / q` and
offset `c` reads at step `s` the cell `⌊(p s + c) / q⌋` (`OnLine`). The zero lines of
`[RuleSpace] §5 Proposition 5.3` are the lines of slope `1 / (2 ^ m - 1)` with `2 ≤ m` and offset
`-1` (`ZeroLine`); the single seed reads `0` along each from step one on. This file states that
every other line of slope `p / q` with `0 < p < q` coprime reads a `1` past every step.

The three named conditions below are the three ranges of the slope that split by the parities of
`p` and `q` and the size of `q` against `3 p`: that the line carries a pair of naturals with no
shared binary digit past every step (`LateDisjointOnLine`). Each is proved, and the main
equivalence follows from them.

## Main results

* `onLine_iff` — the line is the strip `0 ≤ (q + p) b - (q - p) a + c < q`.
* `LateOnLineSlow`, `LateOnLineFast`, `LateOnLineOdd` — the three named conditions: late
  disjoint pairs on every line of odd sum with `3 p < q`, of odd sum with `q < 3 p`, and of
  both terms odd off the zero lines. All three are theorems.
* `onLine_of_dvd`, `lateDisjointOnLine_of_residue` — **the engine**: a residue in the window
  `(c₀ - 2 ^ K₀ (q - p) j) % (q + p) < q`, at a multiplier `j` with `(q - p) j < q + p`, gives late
  disjoint pairs on the line, for `0 < p < q` of odd sum.
* `lateOnLineSlow` — late disjoint pairs on every line of odd sum with `3 p < q`.
* `exists_mul_residue_lt`, `exists_pow_residue_lt_of_two_mul_lt`, `lateOnLineFast` — a residue in
  the window among the multiples (`q ≤ 2 p`) and among the powers of two (`2 p < q + 3`), and
  from them late disjoint pairs on every line of odd sum with `q < 3 p`.
* `exists_disjoint_value_in_window` — **the gap lemma**: for coprime `0 < D < P` with `P + D` odd,
  a window `[x, x + L)` with `P + D ≤ 2 L + 1` contains a value `P b - D a` of a pair with no
  shared binary digit, except exactly when `P = D + 1` is a power of two, `x = 1` and `L = D`
  (`not_exists_disjoint_value_at_exception` shows the exception is real).
* `lateOnLineOdd` — late disjoint pairs on every line of two odd coprime terms off the zero
  lines, from the gap lemma and a high copy of a zero pair.
* `exists_late_one_f90_single_onLine_iff` — **the main equivalence**: for
  coprime `0 < p < q`, the single seed's orbit reads a `1` past every step along the line of
  slope `p / q` and offset `c` exactly when that line is not a zero line.
* `observedRationalRay_f90_iterate_single_eq_line` — a ray from the single seed's orbit advanced
  by `k` steps is a line read from step `k`.
* `exists_late_one_f90_single_onLine_iff_nonvacuous`, `zeroLine_one_three` — the equivalence's
  hypotheses are met at slope `1 / 2`, and the line of slope `1 / 3` and offset `-1` is a zero
  line; `exists_disjoint_value_in_window_nonvacuous` meets the gap lemma's hypotheses.
-/

@[expose] public section

namespace ECA

open LocalRule

/-- **On the line**: the cell `a - b` is the one the line of slope `p / q` and offset `c` reads at
step `a + b`. -/
def OnLine (p q : ℕ) (c : ℤ) (a b : ℕ) : Prop :=
  (a : ℤ) - b = ((p : ℤ) * ((a : ℤ) + b) + c) / q

/-- The line of slope `p / q` and offset `c` is the strip
`0 ≤ (q + p) b - (q - p) a + c < q`. -/
theorem onLine_iff (p q : ℕ) (hq : 0 < q) (c : ℤ) (a b : ℕ) :
    OnLine p q c a b ↔
      0 ≤ ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + c ∧
        ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + c < q := by
  unfold OnLine
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set N : ℤ := (p : ℤ) * ((a : ℤ) + b) + c with hN
  have key : ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + c = N - q * ((a : ℤ) - b) := by
    rw [hN]; ring
  rw [key]
  constructor
  · intro h
    rw [h]
    have h1 := Int.emod_add_mul_ediv N q
    have h2 := Int.emod_nonneg N hq'.ne'
    have h3 := Int.emod_lt_of_pos N hq'
    have h4 : N - q * (N / q) = N % q := by linarith
    rw [h4]; exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩
    have l1 : ((a : ℤ) - b) ≤ N / q := (Int.le_ediv_iff_mul_le hq').2 (by nlinarith)
    have l2 : N / q < ((a : ℤ) - b) + 1 := (Int.ediv_lt_iff_lt_mul hq').2 (by nlinarith)
    omega

/-- **Late disjoint pairs on the line**: past every step some pair of naturals with no shared
binary digit lies on the line. -/
def LateDisjointOnLine (p q : ℕ) (c : ℤ) : Prop :=
  ∀ T : ℕ, ∃ a b : ℕ, a &&& b = 0 ∧ T ≤ a + b ∧ OnLine p q c a b

/-- **A zero line**: slope `1 / (2 ^ m - 1)` with `2 ≤ m`, and offset `-1`. -/
def ZeroLine (p q : ℕ) (c : ℤ) : Prop :=
  p = 1 ∧ c = -1 ∧ ∃ m : ℕ, 2 ≤ m ∧ q = 2 ^ m - 1

/-- **Late disjoint pairs on every line of odd sum with `3 p < q`**. -/
def LateOnLineSlow : Prop :=
  ∀ (p q : ℕ) (c : ℤ), 0 < p → 3 * p < q → (p + q) % 2 = 1 → LateDisjointOnLine p q c

/-- **Late disjoint pairs on every line of odd sum with `q < 3 p`**, for `p < q`. -/
def LateOnLineFast : Prop :=
  ∀ (p q : ℕ) (c : ℤ), 0 < p → p < q → q < 3 * p → (p + q) % 2 = 1 → LateDisjointOnLine p q c

/-- **Late disjoint pairs on every line of two odd terms that is not a zero line**, coprime,
for `p < q`. -/
def LateOnLineOdd : Prop :=
  ∀ (p q : ℕ) (c : ℤ), p % 2 = 1 → q % 2 = 1 → p < q → Nat.Coprime p q → ¬ ZeroLine p q c →
    LateDisjointOnLine p q c

/-! ## The engine: a residue in the window gives late pairs on the line -/

/-- **A family of pairs on the line**: pairs whose first member is a multiple `j * 2 ^ K` of a
power of two. When the line's offset `c₀` puts `c + c₀` in `[0, q)` and the number
`c + 2 ^ K (q - p) j` is divisible by the sum of the line's terms and lies in
`[0, 2 ^ K (q + p))`, some `b` with no binary digit shared with `j * 2 ^ K` makes the pair lie on
the line. -/
theorem onLine_of_dvd (p q : ℕ) (hpq : p < q) (c₀ : ℤ) (j K : ℕ) (c : ℤ)
    (h0 : 0 ≤ c + c₀) (h1 : c + c₀ < q)
    (hdvd : ((q : ℤ) + p) ∣ c + 2 ^ K * (((q : ℤ) - p) * j))
    (hlo : 0 ≤ c + 2 ^ K * (((q : ℤ) - p) * j))
    (hhi : c + 2 ^ K * (((q : ℤ) - p) * j) < 2 ^ K * ((q : ℤ) + p)) :
    ∃ b : ℕ, (j * 2 ^ K) &&& b = 0 ∧ OnLine p q c₀ (j * 2 ^ K) b := by
  have hq0 : 0 < q := by omega
  have hs : (0 : ℤ) < (q : ℤ) + p := by positivity
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 ≤ m := by
    by_contra h
    push Not at h
    nlinarith
  have hm1 : m < 2 ^ K := by
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, m = b := ⟨m.toNat, by omega⟩
  have hb : b < 2 ^ K := by exact_mod_cast hm1
  refine ⟨b, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < K
    · have : (j * 2 ^ K).testBit i = false := by
        rw [Nat.mul_comm]
        rw [Nat.testBit_two_pow_mul]
        simp [hi]
      simp [this]
    · have : b.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num)
          (by omega)))
      simp [this]
  · rw [onLine_iff p q hq0]
    push_cast
    constructor <;> nlinarith

/-- **A residue in the window among the multiples**: for `0 < p < q ≤ 2 p`, some multiplier `j`
with `(q - p) j < q + p` has `(x - (q - p) j) % (q + p)` below `q`. The multiplier is found by
stepping down from the residue at `j = 1` in steps of `q - p`, which land in `[p, q)` before the
residue leaves the range `[0, q + p)`. -/
theorem exists_mul_residue_lt (p q : ℕ) (hp : 0 < p) (hpq : p < q) (h2 : q ≤ 2 * p) (x : ℤ) :
    ∃ j : ℕ, 1 ≤ j ∧ ((q : ℤ) - p) * j < (q : ℤ) + p ∧
      (x - ((q : ℤ) - p) * j) % ((q : ℤ) + p) < q := by
  set D : ℤ := (q : ℤ) - p with hD
  set P : ℤ := (q : ℤ) + p with hP
  have hD0 : 0 < D := by omega
  have hDp : D ≤ p := by omega
  have hP0 : 0 < P := by omega
  set r : ℤ := (x - D) % P with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hP0.ne'
  have hr1 : r < P := Int.emod_lt_of_pos _ hP0
  have hxr : x - D = P * ((x - D) / P) + r := (Int.mul_ediv_add_emod _ _).symm
  by_cases hrq : r < q
  · refine ⟨1, le_rfl, ?_, ?_⟩
    · push_cast; omega
    · push_cast
      rw [mul_one]
      exact hrq
  · push Not at hrq
    set m : ℤ := (r - q) / D with hm
    have hm0 : 0 ≤ m := Int.ediv_nonneg (by omega) hD0.le
    have hm1 : D * m ≤ r - q := Int.mul_ediv_self_le hD0.ne' |>.trans' le_rfl
    have hm2 : r - q < D * m + D := by
      have := Int.emod_lt_of_pos (r - q) hD0
      have := Int.mul_ediv_add_emod (r - q) D
      rw [← hm] at this
      omega
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = m := ⟨m.toNat, by omega⟩
    rw [← hi] at hm1 hm2
    refine ⟨i + 2, by omega, ?_, ?_⟩
    · push_cast
      nlinarith
    · push_cast
      have e : x - D * ((i : ℤ) + 2) = (r - D * ((i : ℤ) + 1)) + P * ((x - D) / P) := by
        linear_combination hxr
      rw [e, Int.add_mul_emod_self_left]
      have hlo : 0 ≤ r - D * ((i : ℤ) + 1) := by nlinarith
      have hhi : r - D * ((i : ℤ) + 1) < q := by nlinarith
      rw [Int.emod_eq_of_lt hlo (by omega)]
      exact hhi

/-- **A residue in the window gives late pairs on the line**: for `0 < p < q` with `p + q` odd,
a multiplier `j` with `(q - p) j < q + p` and a power of two `2 ^ K₀` that puts the residue
`(c₀ - 2 ^ K₀ (q - p) j) % (q + p)` below `q`, every step is passed by a pair with no shared
binary digit on the line of slope `p / q` and offset `c₀`. The exponent is advanced by multiples
of the totient of the odd sum `q + p`, which keeps the divisibility and lets the bounds hold. -/
theorem lateDisjointOnLine_of_residue (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hodd : (p + q) % 2 = 1) (c₀ : ℤ) (j K₀ : ℕ) (hj : 1 ≤ j)
    (hjlt : ((q : ℤ) - p) * j < (q : ℤ) + p)
    (hres : (c₀ - 2 ^ K₀ * (((q : ℤ) - p) * j)) % ((q : ℤ) + p) < q) :
    LateDisjointOnLine p q c₀ := by
  intro T
  have hq0 : 0 < q := by omega
  set s : ℤ := (q : ℤ) + p with hs
  set t : ℤ := (q : ℤ) - p with ht
  set ρ : ℤ := (c₀ - 2 ^ K₀ * (t * j)) % s with hρ
  have hs0 : 0 < s := by omega
  have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ hs0.ne'
  set c : ℤ := -c₀ + ρ with hc
  have hcop : Nat.Coprime 2 (q + p) := by
    apply Nat.coprime_two_left.mpr
    rw [Nat.odd_iff]; omega
  have hmod := Nat.ModEq.pow_totient hcop
  set n := Nat.totient (q + p) with hn
  have hn0 : 0 < n := Nat.totient_pos.mpr (by omega)
  have hmodZ : (2 : ℤ) ^ n ≡ 1 [ZMOD s] := by
    have := (Nat.modEq_iff_dvd.mp hmod)
    rw [Int.modEq_iff_dvd]
    simpa [hs] using this
  set i := T + c.natAbs + 1 with hi
  set K := K₀ + n * i with hK
  have hKi : i ≤ K := by nlinarith
  have hbig : i < 2 ^ K := lt_of_le_of_lt hKi (Nat.lt_two_pow_self (n := K))
  have hbigZ : (i : ℤ) < 2 ^ K := by exact_mod_cast hbig
  have hdvd0 : s ∣ c + 2 ^ K₀ * (t * j) := by
    refine ⟨-((c₀ - 2 ^ K₀ * (t * j)) / s), ?_⟩
    have := Int.mul_ediv_add_emod (c₀ - 2 ^ K₀ * (t * j)) s
    rw [hc]
    linarith
  have hpowK : (2 : ℤ) ^ K ≡ 2 ^ K₀ [ZMOD s] := by
    have h1 := (hmodZ.pow i).mul_left (2 ^ K₀)
    rw [one_pow, mul_one, ← pow_mul, ← pow_add] at h1
    exact h1
  have hdvd : s ∣ c + 2 ^ K * (t * j) := by
    have : s ∣ 2 ^ K * (t * j) - 2 ^ K₀ * (t * j) := by
      have := (Int.modEq_iff_dvd.mp hpowK.symm)
      obtain ⟨k, hk⟩ := this
      exact ⟨k * (t * j), by linear_combination (t * j) * hk⟩
    have h2 := dvd_add hdvd0 this
    convert h2 using 1; ring
  have habs : (c.natAbs : ℤ) = |c| := Int.natCast_natAbs c
  have hcle : -(c.natAbs : ℤ) ≤ c := by rw [habs]; exact neg_abs_le c
  have hcle' : c ≤ c.natAbs := by rw [habs]; exact le_abs_self c
  have hi' : (i : ℤ) = T + c.natAbs + 1 := by rw [hi]; push_cast; ring
  have htj : (1 : ℤ) ≤ t * j := by
    have : (1 : ℤ) ≤ t := by omega
    have : (1 : ℤ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hlo : 0 ≤ c + 2 ^ K * (t * j) := by nlinarith
  have hhi : c + 2 ^ K * (t * j) < 2 ^ K * s := by nlinarith
  obtain ⟨b, hb1, hb2⟩ := onLine_of_dvd p q hpq c₀ j K c (by rw [hc]; linarith)
    (by rw [hc]; linarith) hdvd hlo hhi
  refine ⟨j * 2 ^ K, b, hb1, ?_, hb2⟩
  have h1 : 2 ^ K ≤ j * 2 ^ K := Nat.le_mul_of_pos_left _ hj
  have h2 : i < 2 ^ K := hbig
  omega

/-- The hypotheses of `lateDisjointOnLine_of_residue` are met at slope `1 / 4`, offset `0`,
multiplier `1` and exponent `0`. -/
theorem lateDisjointOnLine_of_residue_nonvacuous :
    0 < 1 ∧ 1 < 4 ∧ (1 + 4) % 2 = 1 ∧ 1 ≤ 1 ∧ ((4 : ℤ) - 1) * 1 < 4 + 1 ∧
      ((0 : ℤ) - 2 ^ 0 * ((4 - 1) * 1)) % (4 + 1) < 4 := by
  decide +kernel

/-- The slow case: late disjoint pairs on every line of odd sum with `3 p < q`. A residue in the
window comes from a power of two, and the engine is applied at multiplier `1`. -/
theorem lateOnLineSlow : LateOnLineSlow := by
  intro p q c hp h3 hodd
  obtain ⟨K₀, hK₀⟩ := exists_pow_residue_lt p q hp h3 c
  refine lateDisjointOnLine_of_residue p q hp (by omega) hodd c 1 K₀ le_rfl ?_ ?_
  · push_cast; omega
  · simpa using hK₀

/-- **A residue in the window among the powers of two, from speed just above one half down**: for
`0 < p < q` with `2 p < q + 3`, some power of two `2 ^ K` has `(x - 2 ^ K (q - p)) % (q + p)`
below `q`. Otherwise every residue lies in `[q, q + p)`, the successive differences are doubled at
each step, hence bounded only if zero, and then the sum of the speed's terms would divide their
difference. -/
theorem exists_pow_residue_lt_of_two_mul_lt (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (h2 : 2 * p < q + 3) (x : ℤ) :
    ∃ K : ℕ, (x - 2 ^ K * ((q : ℤ) - p)) % ((q : ℤ) + p) < q := by
  by_contra hcon
  push Not at hcon
  set s : ℤ := (q : ℤ) + p with hs
  set t : ℤ := (q : ℤ) - p with ht
  have hs0 : 0 < s := by omega
  have ht0 : 0 < t := by omega
  have hts : t < s := by omega
  set ρ : ℕ → ℤ := fun K => (x - 2 ^ K * t) % s with hρ
  set u : ℕ → ℤ := fun K => (x - 2 ^ K * t) / s with hu
  have hdec : ∀ K, x - 2 ^ K * t = s * u K + ρ K := fun K =>
    (Int.mul_ediv_add_emod _ _).symm
  have hρlo : ∀ K, (q : ℤ) ≤ ρ K := fun K => hcon K
  have hρhi : ∀ K, ρ K < s := fun K => Int.emod_lt_of_pos _ hs0
  set D : ℕ → ℤ := fun K => ρ (K + 1) - ρ K with hD
  have hDb : ∀ K, -(p : ℤ) < D K ∧ D K < p := fun K => by
    have := hρlo K; have := hρhi K; have := hρlo (K + 1); have := hρhi (K + 1)
    simp only [hD]
    omega
  have hDe : ∀ K, D K = -(2 ^ K * t) - s * (u (K + 1) - u K) := fun K => by
    have h1 := hdec K
    have h2 := hdec (K + 1)
    simp only [hD]
    rw [pow_succ] at h2
    linarith
  have hdbl : ∀ K, D (K + 1) = 2 * D K := fun K => by
    have e1 := hDe K
    have e2 := hDe (K + 1)
    have b1 := hDb K
    have b2 := hDb (K + 1)
    set m : ℤ := u (K + 2) - u (K + 1) - 2 * (u (K + 1) - u K) with hm
    have hm' : D (K + 1) - 2 * D K = -(s * m) := by
      rw [e1, e2, hm]; rw [pow_succ]; ring
    have : m = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · nlinarith
      · nlinarith
    rw [this] at hm'
    linarith
  have hpow : ∀ K, D K = 2 ^ K * D 0 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih => rw [hdbl, ih, pow_succ]; ring
  have hD0 : D 0 = 0 := by
    by_contra hne
    have hb := hDb p
    rw [hpow p] at hb
    have hp2 : (p : ℤ) < 2 ^ p := by exact_mod_cast Nat.lt_two_pow_self (n := p)
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith [hb.1]
    · nlinarith [hb.2]
  have h0 := hDe 0
  rw [hD0] at h0
  simp only [pow_zero, one_mul] at h0
  set w := u 1 - u 0
  have : s * w = -t := by linarith
  rcases lt_trichotomy w 0 with h | h | h
  · nlinarith
  · rw [h] at this; omega
  · nlinarith

/-- The hypotheses of `exists_mul_residue_lt` are met at `p = 2`, `q = 3`. -/
theorem exists_mul_residue_lt_nonvacuous : 0 < 2 ∧ 2 < 3 ∧ 3 ≤ 2 * 2 := by decide

/-- The hypotheses of `exists_pow_residue_lt_of_two_mul_lt` are met at `p = 2`, `q = 5`. -/
theorem exists_pow_residue_lt_of_two_mul_lt_nonvacuous : 0 < 2 ∧ 2 < 5 ∧ 2 * 2 < 5 + 3 := by
  decide

/-- The fast case: late disjoint pairs on every line of odd sum with `q < 3 p`. From speed at
least one half the residue comes from a multiple, and below it from a power of two. -/
theorem lateOnLineFast : LateOnLineFast := by
  intro p q c hp hpq h3 hodd
  by_cases h2 : q ≤ 2 * p
  · obtain ⟨j, hj, hjlt, hres⟩ := exists_mul_residue_lt p q hp hpq h2 c
    exact lateDisjointOnLine_of_residue p q hp hpq hodd c j 0 hj hjlt (by simpa using hres)
  · obtain ⟨K₀, hK₀⟩ := exists_pow_residue_lt_of_two_mul_lt p q hp hpq (by omega) c
    refine lateDisjointOnLine_of_residue p q hp hpq hodd c 1 K₀ le_rfl ?_ ?_
    · push_cast; omega
    · simpa using hK₀

/-! ## The gap lemma and the case of two odd terms -/

/-- **A pair on the line of the residue**: for `p + D = P` with `0 < p`, `0 < D`, and a power of two
`2 ^ n` with `P ≤ p * 2 ^ n`, the residue of `p * 2 ^ n` modulo `P` is the value
`P b - D a` of a pair `(a, b)` with no shared binary digit, namely `a = 2 ^ n` and
`b = 2 ^ n - p * 2 ^ n / P`. -/
private theorem pair_of_residue (P D p : ℕ) (hpD : p + D = P) (hp : 0 < p) (hD : 0 < D) (n : ℕ)
    (hn : P ≤ p * 2 ^ n) :
    ∃ a b : ℕ, a &&& b = 0 ∧ (P : ℤ) * b - (D : ℤ) * a = ((p * 2 ^ n % P : ℕ) : ℤ) := by
  have hP : 0 < P := by omega
  set Q := p * 2 ^ n / P with hQ
  set R := p * 2 ^ n % P with hR
  have hdm : P * Q + R = p * 2 ^ n := Nat.div_add_mod _ _
  have hQ1 : 1 ≤ Q := Nat.div_pos hn hP
  have hlt : p * 2 ^ n < P * 2 ^ n := by
    have : 0 < 2 ^ n := by positivity
    nlinarith
  have hQ2 : Q < 2 ^ n := by
    by_contra h
    push Not at h
    have : P * 2 ^ n ≤ P * Q := Nat.mul_le_mul_left _ h
    omega
  refine ⟨2 ^ n, 2 ^ n - Q, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
    by_cases hi : n = i
    · subst hi
      have : (2 ^ n - Q).testBit n = false :=
        Nat.testBit_lt_two_pow (by omega)
      simp [this]
    · simp [hi]
  · have e : (((2 ^ n - Q : ℕ)) : ℤ) = 2 ^ n - Q := by
      rw [Nat.cast_sub hQ2.le]; push_cast; ring
    rw [e]
    have hdmZ : (P : ℤ) * Q + R = p * 2 ^ n := by exact_mod_cast hdm
    have hpDZ : (p : ℤ) + D = P := by exact_mod_cast hpD
    push_cast
    rw [← hpDZ] at hdmZ ⊢
    linear_combination (-1 : ℤ) * hdmZ

/-- **The long case of the gap lemma**: a window `[x, x + L)` with `1 ≤ x` and `x + L ≤ P`,
among the values `P b - D a` of pairs with no shared binary digit. If no power of two reaches
it, the reduced residues of `p * 2 ^ n` stay in the strip `[-(P - x - L), x - 1]`, successive ones
double and so vanish, `P` divides a power of two, and the exception follows. -/
private theorem window_main (P D : ℕ) (hD : 0 < D) (hDP : D < P)
    (hodd : (P + D) % 2 = 1) (hcop : Nat.Coprime P D) (x : ℤ) (L : ℕ) (hL : P + D ≤ 2 * L + 1)
    (hx1 : 1 ≤ x) (hxL : x + L ≤ P)
    (hex : ¬ (P = D + 1 ∧ (∃ t : ℕ, P = 2 ^ t) ∧ x = 1 ∧ L = D)) :
    ∃ a b : ℕ, a &&& b = 0 ∧ x ≤ (P : ℤ) * b - (D : ℤ) * a ∧
      (P : ℤ) * b - (D : ℤ) * a < x + L := by
  obtain ⟨p, hpD⟩ : ∃ p, p + D = P := ⟨P - D, by omega⟩
  have hp0 : 0 < p := by omega
  have hpodd : p % 2 = 1 := by omega
  have hcopp : Nat.Coprime P p := by
    have : Nat.Coprime P D := hcop
    rw [← hpD] at this ⊢
    simpa [Nat.coprime_add_self_left, Nat.coprime_comm] using this
  by_contra hno
  have hno' : ∀ n : ℕ, P ≤ p * 2 ^ n →
      ¬ (x ≤ ((p * 2 ^ n % P : ℕ) : ℤ) ∧ ((p * 2 ^ n % P : ℕ) : ℤ) < x + L) := by
    intro n hn ⟨h1, h2⟩
    obtain ⟨a, b, hab, hv⟩ := pair_of_residue P D p hpD hp0 hD n hn
    exact hno ⟨a, b, hab, by rw [hv]; exact h1, by rw [hv]; exact h2⟩
  have hPpos : 0 < P := by omega
  have hpZ : (p : ℤ) + D = P := by exact_mod_cast hpD
  -- the sequence of reduced residues
  have hbig : ∀ n : ℕ, P ≤ n → P ≤ p * 2 ^ n := fun n hn => by
    have := Nat.lt_two_pow_self (n := n)
    have : 2 ^ n ≤ p * 2 ^ n := Nat.le_mul_of_pos_left _ hp0
    omega
  have hex_t : ∀ n : ℕ, P ≤ n → ∃ t : ℤ, -((P : ℤ) - (x + L)) ≤ t ∧ t ≤ x - 1 ∧
      (P : ℤ) ∣ t - p * 2 ^ n := by
    intro n hn
    have hnn := hno' n (hbig n hn)
    set ρ : ℕ := p * 2 ^ n % P with hρ
    have hρlt : ρ < P := Nat.mod_lt _ hPpos
    have hρZ : (P : ℤ) ∣ (ρ : ℤ) - p * 2 ^ n := by
      have : (p * 2 ^ n : ℤ) = P * ((p * 2 ^ n / P : ℕ) : ℤ) + ρ := by
        have := Nat.div_add_mod (p * 2 ^ n) P
        exact_mod_cast this.symm
      exact ⟨-((p * 2 ^ n / P : ℕ) : ℤ), by linarith⟩
    have hρlt' : (ρ : ℤ) < P := by exact_mod_cast hρlt
    by_cases h : (ρ : ℤ) < x
    · refine ⟨ρ, by omega, by omega, hρZ⟩
    · have h' : x + L ≤ (ρ : ℤ) := by
        by_contra h2
        exact hnn ⟨by omega, by omega⟩
      refine ⟨(ρ : ℤ) - P, by omega, by omega, ?_⟩
      have : (ρ : ℤ) - P - p * 2 ^ n = ((ρ : ℤ) - p * 2 ^ n) - P := by ring
      rw [this]
      exact dvd_sub hρZ dvd_rfl
  have hLZ : (P : ℤ) + D ≤ 2 * L + 1 := by exact_mod_cast hL
  have hsum : 2 * ((x - 1) + ((P : ℤ) - (x + L))) ≤ p - 1 := by omega
  obtain ⟨t0, ht0a, ht0b, ht0d⟩ := hex_t P le_rfl
  have hseq : ∀ i : ℕ, ∃ t : ℤ, t = 2 ^ i * t0 ∧ -((P : ℤ) - (x + L)) ≤ t ∧ t ≤ x - 1 ∧
      (P : ℤ) ∣ t - p * 2 ^ (P + i) := by
    intro i
    induction i with
    | zero => exact ⟨t0, by simp, ht0a, ht0b, by simpa using ht0d⟩
    | succ i ih =>
      obtain ⟨t, he, ha, hb, hd⟩ := ih
      obtain ⟨t', ha', hb', hd'⟩ := hex_t (P + (i + 1)) (by omega)
      have hdd : (P : ℤ) ∣ t' - 2 * t := by
        have := dvd_sub hd' (dvd_mul_of_dvd_right hd 2)
        convert this using 1
        rw [← add_assoc, pow_succ]; ring
      obtain ⟨k, hk⟩ := hdd
      have hk0 : k = 0 := by
        by_contra hne
        have hPZ : (0 : ℤ) < P := by exact_mod_cast hPpos
        rcases lt_or_gt_of_ne hne with h | h
        · nlinarith
        · nlinarith
      rw [hk0] at hk
      refine ⟨t', ?_, ha', hb', hd'⟩
      rw [pow_succ]
      have : t' = 2 * t := by linarith
      rw [this, he]; ring
  have ht0 : t0 = 0 := by
    obtain ⟨t, he, ha, hb, -⟩ := hseq (x - 1 + ((P : ℤ) - (x + L))).toNat
    have h2 : (x - 1 + ((P : ℤ) - (x + L))).toNat < 2 ^ (x - 1 + ((P : ℤ) - (x + L))).toNat :=
      Nat.lt_two_pow_self
    have h2' : (x - 1 + ((P : ℤ) - (x + L))) < 2 ^ (x - 1 + ((P : ℤ) - (x + L))).toNat := by
      have : ((x - 1 + ((P : ℤ) - (x + L))).toNat : ℤ) <
          2 ^ (x - 1 + ((P : ℤ) - (x + L))).toNat := by
        exact_mod_cast h2
      omega
    set E : ℤ := 2 ^ (x - 1 + ((P : ℤ) - (x + L))).toNat with hE
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · nlinarith
  have hdvdN : P ∣ p * 2 ^ P := by
    rw [ht0] at ht0d
    have : (P : ℤ) ∣ ((p * 2 ^ P : ℕ) : ℤ) := by
      have := dvd_neg.mpr ht0d
      simpa using this
    exact_mod_cast this
  have hdvd2 : P ∣ 2 ^ P := hcopp.dvd_of_dvd_mul_left hdvdN
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  by_cases hp3 : 3 ≤ p
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := by
      rcases t with _ | u
      · simp at ht; omega
      · exact ⟨u, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
    have hPE : P = 2 * 2 ^ u := by rw [ht, pow_succ]; ring
    have hE : 0 < 2 ^ u := by positivity
    have hpe : p * 2 ^ u = 2 ^ u + P * k := by rw [hk, hPE]; ring
    have hres : p * 2 ^ u % P = 2 ^ u := by
      rw [hpe, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have hbg : P ≤ p * 2 ^ u := by
      have : 3 * 2 ^ u ≤ p * 2 ^ u := Nat.mul_le_mul_right _ hp3
      omega
    apply hno' u hbg
    rw [hres]
    have hEZ : (P : ℤ) = 2 * ((2 ^ u : ℕ) : ℤ) := by exact_mod_cast hPE
    constructor <;> omega
  · have hp1 : p = 1 := by omega
    apply hex
    have hpZ1 : (p : ℤ) = 1 := by exact_mod_cast hp1
    refine ⟨by omega, ⟨t, ht⟩, by omega, by omega⟩

/-- **A single-bit hit over the integers**: for `0 < D < P` and `D < w`, a pair with no shared
binary digit has value `P b - D a` in `[w, w + D)`. -/
private theorem bit_hit_int (P D w : ℕ) (hD : 0 < D) (hPD : D < P) (hw : D < w) :
    ∃ a b : ℕ, a &&& b = 0 ∧ (w : ℤ) ≤ (P : ℤ) * b - (D : ℤ) * a ∧
      (P : ℤ) * b - (D : ℤ) * a < w + D := by
  obtain ⟨r, a, hdis, h1, h2, h3⟩ := exists_single_bit_hit P D w hD hPD hw
  refine ⟨a, 2 ^ r, hdis, ?_, ?_⟩
  · have e : ((P * 2 ^ r - D * a : ℕ) : ℤ) = (P : ℤ) * 2 ^ r - D * a := by
      rw [Nat.cast_sub h1]; push_cast; ring
    have : (w : ℤ) ≤ ((P * 2 ^ r - D * a : ℕ) : ℤ) := by exact_mod_cast h2
    push_cast; linarith
  · have e : ((P * 2 ^ r - D * a : ℕ) : ℤ) = (P : ℤ) * 2 ^ r - D * a := by
      rw [Nat.cast_sub h1]; push_cast; ring
    have : ((P * 2 ^ r - D * a : ℕ) : ℤ) < w + D := by exact_mod_cast h3
    push_cast; linarith

/-- **A gap lemma on the values of pairs with no shared binary digit**: for coprime `0 < D < P`
with `P + D` odd, every window `[x, x + L)` of length `L` with `P + D ≤ 2 L + 1` contains a value
`P b - D a` of a pair of naturals with no shared binary digit, except exactly when `P = D + 1` is a
power of two, `x = 1` and `L = D`. -/
theorem exists_disjoint_value_in_window (P D : ℕ) (hD : 0 < D) (hDP : D < P)
    (hodd : (P + D) % 2 = 1) (hcop : Nat.Coprime P D) (x : ℤ) (L : ℕ) (hL : P + D ≤ 2 * L + 1)
    (hex : ¬ (P = D + 1 ∧ (∃ t : ℕ, P = 2 ^ t) ∧ x = 1 ∧ L = D)) :
    ∃ a b : ℕ, a &&& b = 0 ∧ x ≤ (P : ℤ) * b - (D : ℤ) * a ∧
      (P : ℤ) * b - (D : ℤ) * a < x + L := by
  have hLD : D ≤ L := by omega
  by_cases h1 : x ≤ 0 ∧ 0 < x + L
  · exact ⟨0, 0, by simp, by simp; omega, by simp; omega⟩
  by_cases h2 : x + L ≤ 0
  · set y : ℤ := -(x + L) with hy
    have hy0 : 0 ≤ y := by omega
    have hDZ : (0 : ℤ) < D := by exact_mod_cast hD
    have hdm := Int.mul_ediv_add_emod y D
    have hm0 := Int.emod_nonneg y hDZ.ne'
    have hm1 := Int.emod_lt_of_pos y hDZ
    have hq0 : 0 ≤ y / D := Int.ediv_nonneg hy0 hDZ.le
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = y / D + 1 := ⟨(y / D + 1).toNat, by omega⟩
    have hLZ : (D : ℤ) ≤ L := by exact_mod_cast hLD
    refine ⟨a, 0, by simp, ?_, ?_⟩
    · push_cast; rw [ha]; nlinarith
    · push_cast; rw [ha]; nlinarith
  have hx : 0 < x ∨ ¬ 0 < x + L := by omega
  by_cases h3 : (D : ℤ) < x
  · obtain ⟨a, b, hab, hv1, hv2⟩ := bit_hit_int P D x.toNat hD hDP (by omega)
    refine ⟨a, b, hab, ?_, ?_⟩
    · have : ((x.toNat : ℕ) : ℤ) = x := by omega
      rw [this] at hv1; exact hv1
    · have : ((x.toNat : ℕ) : ℤ) = x := by omega
      rw [this] at hv2; have : (D : ℤ) ≤ L := by exact_mod_cast hLD
      omega
  have hx1 : 1 ≤ x := by omega
  by_cases h4 : 2 * (D : ℤ) < x + L
  · obtain ⟨a, b, hab, hv1, hv2⟩ := bit_hit_int P D (D + 1) hD hDP (by omega)
    push_cast at hv1 hv2
    exact ⟨a, b, hab, by omega, by omega⟩
  by_cases h5 : (P : ℤ) < x + L
  · exact ⟨0, 1, by simp, by simp; omega, by simp; omega⟩
  exact window_main P D hD hDP hodd hcop x L hL hx1 (by omega) hex

/-- **A pair on the line**: on every line of two odd coprime terms with `p < q` that is not a zero
line, some pair of naturals with no shared binary digit lies on the line. The line is the strip
`0 ≤ 2 (P b - D a) + c < q` for `P = (q + p) / 2` and `D = (q - p) / 2`, and the window of values
is `[-(c / 2), -(c / 2) + L)`. -/
private theorem exists_disjoint_onLine_of_odd (p q : ℕ) (c : ℤ) (hp : p % 2 = 1) (hq : q % 2 = 1)
    (hpq : p < q) (hcop : Nat.Coprime p q) (hnz : ¬ ZeroLine p q c) :
    ∃ a b : ℕ, a &&& b = 0 ∧ OnLine p q c a b := by
  have hq0 : 0 < q := by omega
  obtain ⟨P, hP⟩ : ∃ P, P = (q + p) / 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (q - p) / 2 := ⟨_, rfl⟩
  have hPD : P + D = q := by omega
  have hPD' : P = p + D := by omega
  have hD0 : 0 < D := by omega
  have hDP : D < P := by omega
  have hcopPD : Nat.Coprime P D := by
    have h1 : Nat.gcd P D ∣ q := by
      rw [← hPD]; exact dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    have h2 : Nat.gcd P D ∣ p := by
      have := Nat.dvd_sub (Nat.gcd_dvd_left P D) (Nat.gcd_dvd_right P D)
      have e : P - D = p := by omega
      rwa [e] at this
    have := Nat.dvd_gcd h2 h1
    rw [hcop] at this
    exact Nat.eq_one_of_dvd_one this
  have hrel : ∀ (a b : ℕ), OnLine p q c a b ↔
      0 ≤ 2 * ((P : ℤ) * b - (D : ℤ) * a) + c ∧ 2 * ((P : ℤ) * b - (D : ℤ) * a) + c < q := by
    intro a b
    rw [onLine_iff p q hq0]
    have h1 : ((q : ℤ) + p) = 2 * P := by omega
    have h2 : ((q : ℤ) - p) = 2 * D := by omega
    rw [h1, h2]
    constructor <;> rintro ⟨u, v⟩ <;> constructor <;> linarith
  by_cases hc : c % 2 = 1
  · obtain ⟨a, b, hab, h1, h2⟩ := exists_disjoint_value_in_window P D hD0 hDP (by omega) hcopPD
      (-(c / 2)) ((q - 1) / 2) (by omega) (by
        rintro ⟨hP1, ⟨t, ht⟩, hx, hLD⟩
        have ht1 : 1 ≤ t := by
          rcases t with _ | t
          · simp at ht; omega
          · omega
        apply hnz
        refine ⟨by omega, by omega, t + 1, by omega, ?_⟩
        have : (2 : ℕ) ^ (t + 1) = 2 * P := by rw [pow_succ, ← ht]; ring
        omega)
    refine ⟨a, b, hab, (hrel a b).2 ⟨by omega, by omega⟩⟩
  · obtain ⟨a, b, hab, h1, h2⟩ := exists_disjoint_value_in_window P D hD0 hDP (by omega) hcopPD
      (-(c / 2)) ((q + 1) / 2) (by omega) (by
        rintro ⟨hP1, ⟨t, ht⟩, hx, hLD⟩
        omega)
    refine ⟨a, b, hab, (hrel a b).2 ⟨by omega, by omega⟩⟩

/-- The case of two odd terms: late disjoint pairs on every line of two odd coprime terms that
is not a zero line. A pair on the line is pushed past every step by adding a high copy of a
zero pair, which leaves the strip's quantity unchanged. -/
theorem lateOnLineOdd : LateOnLineOdd := by
  intro p q c hp hq hpq hcop hnz T
  obtain ⟨a, b, hab, hon⟩ := exists_disjoint_onLine_of_odd p q c hp hq hpq hcop hnz
  obtain ⟨A, B, hA, hAB, hz⟩ := exists_zero_pair p q hp hq hpq
  have hq0 : 0 < q := by omega
  set M := a + b + T with hM
  have haM : a < 2 ^ M := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := M))
  have hbM : b < 2 ^ M := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := M))
  have hTM : T ≤ 2 ^ M := le_trans (by omega) (Nat.lt_two_pow_self (n := M)).le
  refine ⟨a + 2 ^ M * A, b + 2 ^ M * B, and_add_shift_eq_zero a b A B M haM hbM hab hAB, ?_, ?_⟩
  · have : 2 ^ M * 1 ≤ 2 ^ M * A := Nat.mul_le_mul_left _ hA
    omega
  · rw [onLine_iff p q hq0] at hon ⊢
    have key : ((q : ℤ) + p) * ((b + 2 ^ M * B : ℕ) : ℤ)
        - ((q : ℤ) - p) * ((a + 2 ^ M * A : ℕ) : ℤ) + c =
          ((q : ℤ) + p) * b - ((q : ℤ) - p) * a + c := by
      push_cast
      linear_combination (2 ^ M : ℤ) * hz
    rw [key]
    exact hon

/-- The hypotheses of `exists_disjoint_value_in_window` are met at `(P, D) = (2, 1)`, window
`[2, 3)`: only the window starting at `1` is excepted. -/
theorem exists_disjoint_value_in_window_nonvacuous :
    0 < 1 ∧ 1 < 2 ∧ (2 + 1) % 2 = 1 ∧ Nat.Coprime 2 1 ∧ 2 + 1 ≤ 2 * 1 + 1 ∧
      ¬ (2 = 1 + 1 ∧ (∃ t : ℕ, 2 = 2 ^ t) ∧ (2 : ℤ) = 1 ∧ 1 = 1) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨-, -, h, -⟩
  omega

/-- **The exception is load-bearing**: at `(P, D) = (2, 1)` no pair with no shared binary digit has
value `2 b - a` equal to `1`. -/
theorem not_exists_disjoint_value_at_exception :
    ¬ ∃ a b : ℕ, a &&& b = 0 ∧ (1 : ℤ) ≤ (2 : ℤ) * b - (1 : ℤ) * a ∧
      (2 : ℤ) * b - (1 : ℤ) * a < 1 + 1 := by
  rintro ⟨a, b, hab, h1, h2⟩
  have hb : 2 * b = a + 1 := by omega
  have ha : a % 2 ^ 1 ≠ 0 := by omega
  have hd : a - a / 2 ^ 1 = b := by omega
  rw [← hd] at hab
  exact and_sub_div_two_pow_ne_zero 1 a ha hab

/-- **The lines of rule `90` from the single seed**, the converse of
`[RuleSpace] §5 Proposition 5.3` at the single seed: for coprime `0 < p < q`, the single seed's
orbit reads a `1` past every step along the line of slope `p / q` and offset `c` exactly when the
line is not a zero line. -/
theorem exists_late_one_f90_single_onLine_iff (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hcop : Nat.Coprime p q) (c : ℤ) :
    (∀ T : ℕ, ∃ s : ℕ, T ≤ s ∧
      ((finRule f90 hq90)^[s] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (((p : ℤ) * s + c) / q) = 1) ↔ ¬ ZeroLine p q c := by
  constructor
  · rintro H ⟨rfl, rfl, m, hm, rfl⟩
    obtain ⟨s, hs1, hv⟩ := H 1
    have hz := f90_single_apply_zeroLine m s hm hs1
    have hq : ((2 ^ m - 1 : ℕ) : ℤ) ≠ 0 := by
      have : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
      exact_mod_cast (by omega : 2 ^ m - 1 ≠ 0)
    have hc : (((s - 1) / (2 ^ m - 1) : ℕ) : ℤ)
        = (((1 : ℕ) : ℤ) * s + -1) / ((2 ^ m - 1 : ℕ) : ℤ) := by
      rw [Int.natCast_ediv]
      congr 1
      push_cast [Nat.cast_sub hs1]
      ring
    rw [← hc, hz] at hv
    exact absurd hv (by decide)
  · intro hnz T
    have hld : LateDisjointOnLine p q c := by
      have hp2 : p % 2 = 0 → q % 2 = 0 → False := by
        intro h1 h2
        have : 2 ∣ Nat.gcd p q := Nat.dvd_gcd (by omega) (by omega)
        rw [hcop] at this
        omega
      by_cases hodd : p % 2 = 1 ∧ q % 2 = 1
      · exact lateOnLineOdd p q c hodd.1 hodd.2 hpq hcop hnz
      · have hsum : (p + q) % 2 = 1 := by
          by_contra hne
          have h3 : ¬ (p % 2 = 0 ∧ q % 2 = 0) := fun h => hp2 h.1 h.2
          apply hodd
          omega
        rcases lt_trichotomy q (3 * p) with h | h | h
        · exact lateOnLineFast p q c hp hpq h hsum
        · omega
        · exact lateOnLineSlow p q c hp h hsum
    obtain ⟨a, b, hab, hT, hon⟩ := hld T
    refine ⟨a + b, hT, ?_⟩
    have := oneOfDisjoint a b hab
    unfold OnLine at hon
    push_cast
    rw [← hon]
    exact this

/-- A ray from the single seed's orbit advanced by `k` steps is a line read from step `k`. -/
theorem observedRationalRay_f90_iterate_single_eq_line (p q k : ℕ) (hq : 0 < q) (e : ℤ) (t : ℕ) :
    observedRationalRay (finRule f90 hq90)
        ((finRule f90 hq90)^[k] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) p q e t
      = ((finRule f90 hq90)^[t + k] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
          (((p : ℤ) * ((t + k : ℕ) : ℤ) + ((q : ℤ) * e - (p : ℤ) * k)) / q) := by
  unfold observedRationalRay
  rw [Function.iterate_add_apply]
  congr 1
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have : (p : ℤ) * ((t + k : ℕ) : ℤ) + ((q : ℤ) * e - (p : ℤ) * k) = (p : ℤ) * t + e * q := by
    push_cast; ring
  rw [this, Int.add_mul_ediv_right _ _ hq', Int.natCast_ediv]
  push_cast
  ring

/-- The statement of `exists_late_one_f90_single_onLine_iff` is satisfiable at slope `1 / 2`
and offset `0`. -/
theorem exists_late_one_f90_single_onLine_iff_nonvacuous :
    0 < 1 ∧ 1 < 2 ∧ Nat.Coprime 1 2 ∧ ¬ ZeroLine 1 2 0 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro ⟨-, h, -⟩
  omega

/-- The line of slope `1 / 3` and offset `-1` is a zero line. -/
theorem zeroLine_one_three : ZeroLine 1 3 (-1) :=
  ⟨rfl, rfl, 2, le_rfl, by norm_num⟩

end ECA

/-- info: 'ECA.onLine_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.onLine_iff

/-- info: 'ECA.exists_late_one_f90_single_onLine_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_late_one_f90_single_onLine_iff

/-- info: 'ECA.observedRationalRay_f90_iterate_single_eq_line' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.observedRationalRay_f90_iterate_single_eq_line

/-- info: 'ECA.exists_late_one_f90_single_onLine_iff_nonvacuous' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_late_one_f90_single_onLine_iff_nonvacuous

/-- info: 'ECA.zeroLine_one_three' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.zeroLine_one_three

/-- info: 'ECA.lateDisjointOnLine_of_residue' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.lateDisjointOnLine_of_residue

/-- info: 'ECA.lateOnLineSlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.lateOnLineSlow

/-- info: 'ECA.lateDisjointOnLine_of_residue_nonvacuous' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.lateDisjointOnLine_of_residue_nonvacuous

/-- info: 'ECA.exists_mul_residue_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_mul_residue_lt

/-- info: 'ECA.exists_pow_residue_lt_of_two_mul_lt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_pow_residue_lt_of_two_mul_lt

/-- info: 'ECA.lateOnLineFast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.lateOnLineFast

/-- info: 'ECA.exists_disjoint_value_in_window' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_disjoint_value_in_window

/-- info: 'ECA.lateOnLineOdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.lateOnLineOdd

/-- info: 'ECA.exists_disjoint_value_in_window_nonvacuous' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ECA.exists_disjoint_value_in_window_nonvacuous

/-- info: 'ECA.not_exists_disjoint_value_at_exception' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_exists_disjoint_value_at_exception
