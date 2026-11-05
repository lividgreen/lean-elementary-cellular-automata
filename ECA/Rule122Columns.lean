module

public import ECA.EdgeColumns
public import ECA.ReproducedPatterns
public import ECA.Doubling
import all ECA.EdgeColumns
import all ECA.EdgeWindow
import all ECA.EndpointClasses
import all ECA.Growth

/-!
# Rule `122` reproduces exactly the nonzero translates of doubled patterns
([RuleSpace] §5)

A rule agreeing with rule `90` at equal adjacent cells reproduces every nonzero doubled pattern and
every translate of one. Rule `122` is such a rule, and the question is whether it reproduces
anything else. At a quiescent rule with `f 0 0 1 = 1` the window read from the leftmost set cell of
a reproduced pattern `p` is purely periodic in time at every gap, so the window of width
`diam p + 2` of the orbit of `p` is a family of purely periodic columns obeying the window
recurrence, with its first cell set. Rule `122` is its own mirror, so reflection carries a
reproduced pattern to a reproduced pattern, and the same holds read from the right end. The
statement that at rule `122` such a family is at time `0` a run of pairs `10`, then a set cell, then
equal pairs is stated here as a proposition, `PeriodicColumnsPaired122`, and proved by a column
induction. From it, read at both ends of `p`, the cells of `p` come in equal pairs, so `p` is a
translate of a doubled pattern.

## Main results

* `PeriodicColumnsPaired122` — the column statement, as a proposition: a family of purely periodic
  columns obeying rule `122`'s window recurrence below a width, with its first cell set, is at time
  `0` a run of `r` pairs `10`, then a set cell `2 r`, then equal pairs.
* `periodicColumnsPaired122` / `periodicColumnsPaired122_nonvacuous` /
  `not_periodicColumnsPaired122_without_period` — that proposition is true, its hypotheses meet at
  width `6`, and without pure periodicity it fails at width `4`.
* `reproduces_iff_dbl_f122_of` — from that proposition, rule `122` reproduces a pattern exactly
  when it is nonzero and a translate of a doubled pattern.
* `reproduces_iff_dbl_f122` — rule `122` reproduces a pattern exactly when it is nonzero and a
  translate of a doubled pattern, with no hypothesis.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- **A family of purely periodic columns at rule `122` is a run of pairs, then equal pairs**: a
family `e n j` obeying the window recurrence of rule `122` below the width `W`, with `e 0 0 = 1`
and every column of period `t`, is at time `0` a run of `r` pairs `10`, then a set cell `2 r`, then
equal pairs `2 k`, `2 k + 1`: every even cell up to `2 r` is set, every odd cell below `2 r` is
clear, and every pair from `r` on is equal. -/
def PeriodicColumnsPaired122 : Prop :=
  ∀ (e : ℕ → ℕ → ZMod 2) (W t : ℕ),
    (∀ n j, j < W → e (n + 1) j =
      f122 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) →
    e 0 0 = 1 → 0 < t →
    (∀ n j, j < W → e (n + t) j = e n j) →
    ∃ r, (∀ k, k ≤ r → 2 * k < W → e 0 (2 * k) = 1) ∧
      (∀ k, k < r → 2 * k + 1 < W → e 0 (2 * k + 1) = 0) ∧
      (∀ k, r ≤ k → 2 * k + 1 < W → e 0 (2 * k) = e 0 (2 * k + 1))

/-- The window recurrence of rule `122` at a column with two columns to its left. -/
private theorem rec2_122 (e : ℕ → ℕ → ZMod 2) (W : ℕ)
    (hrec : ∀ n j, j < W → e (n + 1) j =
      f122 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j))
    (n j a b : ℕ) (hj : j < W) (ha : a + 2 = j) (hb : b + 1 = j) :
    e (n + 1) j = f122 (e n a) (e n b) (e n j) := by
  have h2 : 2 ≤ j := by omega
  have h1 : 1 ≤ j := by omega
  rw [hrec n j hj]
  simp only [h2, h1, ↓reduceIte, show j - 2 = a by omega, show j - 1 = b by omega]

/-- A property of two columns that holds from some time on holds at every time, by periodicity. -/
private theorem lift_122 (e : ℕ → ℕ → ZMod 2) (W t : ℕ) (ht : 0 < t)
    (hper : ∀ n j, j < W → e (n + t) j = e n j) {j₁ j₂ : ℕ} (h₁ : j₁ < W) (h₂ : j₂ < W)
    (Q : ZMod 2 → ZMod 2 → Prop) (n₁ : ℕ) (h : ∀ m, n₁ ≤ m → Q (e m j₁) (e m j₂)) :
    ∀ n, Q (e n j₁) (e n j₂) := by
  have hperk : ∀ s n j, j < W → e (n + s * t) j = e n j := by
    intro s
    induction s with
    | zero => intro n j _; simp
    | succ s ih =>
      intro n j hj
      rw [Nat.succ_mul, ← add_assoc, hper _ _ hj, ih n j hj]
  intro n
  have hle : n₁ ≤ n₁ * t := Nat.le_mul_of_pos_right _ ht
  have := h (n + n₁ * t) (by omega)
  rwa [hperk n₁ n j₁ h₁, hperk n₁ n j₂ h₂] at this

/-- The cells `0, …, k - 1` of a run of pairs `10` at every time. -/
private def Run122 (e : ℕ → ℕ → ZMod 2) (W k : ℕ) : Prop :=
  ∀ i, i < k → (2 * i < W → ∀ n, e n (2 * i) = 1) ∧ (2 * i + 1 < W → ∀ n, e n (2 * i + 1) = 0)

/-- Past a run of `k` pairs `10`, the column `2 k` is set at every time. -/
private theorem runSet122 (e : ℕ → ℕ → ZMod 2) (W t : ℕ) (ht : 0 < t)
    (hrec : ∀ n j, j < W → e (n + 1) j =
      f122 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j))
    (hper : ∀ n j, j < W → e (n + t) j = e n j) (he0 : e 0 0 = 1) (k : ℕ)
    (hk : Run122 e W k) (hW : 2 * k < W) : ∀ n, e n (2 * k) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · intro n
    induction n with
    | zero => simpa using he0
    | succ n ih =>
      have := hrec n 0 (by omega)
      simp only [Nat.mul_zero, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, ↓reduceIte] at this ih ⊢
      rw [this, ih]
      decide
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨h1, h2⟩ := hk k' (by omega)
    have h1' := h1 (by omega)
    have h2' := h2 (by omega)
    refine lift_122 e W t ht hper hW hW (fun a _ => a = 1) 1 ?_
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    show e (m' + 1) (2 * (k' + 1)) = 1
    rw [rec2_122 e W hrec m' (2 * (k' + 1)) (2 * k') (2 * k' + 1) hW (by omega) (by omega),
      h1' m', h2' m']
    generalize e m' (2 * (k' + 1)) = x
    revert x
    decide

/-- Past a run of `k` pairs `10`, the column `2 k + 1` is constant in time. -/
private theorem runConst122 (e : ℕ → ℕ → ZMod 2) (W t : ℕ) (ht : 0 < t)
    (hrec : ∀ n j, j < W → e (n + 1) j =
      f122 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j))
    (hper : ∀ n j, j < W → e (n + t) j = e n j) (he0 : e 0 0 = 1) (k : ℕ)
    (hk : Run122 e W k) (hW : 2 * k + 1 < W) (n : ℕ) : e (n + 1) (2 * k + 1) = e n (2 * k + 1) := by
  have hset := runSet122 e W t ht hrec hper he0 k hk (by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have := hrec n 1 (by omega)
    simp only [Nat.mul_zero, Nat.zero_add] at this ⊢
    rw [this]
    simp only [Nat.not_ofNat_le_one, ↓reduceIte, Std.le_refl, tsub_self]
    have h0 := hset n
    simp only [Nat.mul_zero] at h0
    rw [h0]
    generalize e n 1 = x
    revert x
    decide
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h2 := (hk k' (by omega)).2 (by omega) n
    rw [rec2_122 e W hrec n (2 * (k' + 1) + 1) (2 * k' + 1) (2 * (k' + 1)) hW (by omega)
      (by omega), h2, hset n]
    generalize e n (2 * (k' + 1) + 1) = x
    revert x
    decide


/-- **A family of purely periodic columns at rule `122` is a run of pairs, then equal pairs.** A
column induction in two phases. While the lower columns are pairs `10`, the next even column reads
`f 1 0 x = 1` and is set, and the next odd column reads `f 0 1 x = x` and is constant; the run ends
at the first odd column not clear. From there a pair that is unequal at some time has the sum of its
two cells never rising and, periodically, equal to `1` at every time, which forces the lower even
column clear at every time and, through the equal pairs below, every even column down to the end of
the run, against the set cell there. -/
theorem periodicColumnsPaired122 : PeriodicColumnsPaired122 := by
  intro e W t hrec he0 ht hper
  have fid : ∀ a c : ZMod 2, f122 a a c = a + c := by decide
  have f1 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  -- the end of the run of pairs `10`
  classical
  have hex : ∃ k, W ≤ 2 * k + 1 ∨ ∃ n, e n (2 * k + 1) ≠ 0 := ⟨W, Or.inl (by omega)⟩
  obtain ⟨r, hr_spec, hr_min⟩ : ∃ r, (W ≤ 2 * r + 1 ∨ ∃ n, e n (2 * r + 1) ≠ 0) ∧
      ∀ i, i < r → ¬ (W ≤ 2 * i + 1 ∨ ∃ n, e n (2 * i + 1) ≠ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hrun : ∀ k, k ≤ r → Run122 e W k := by
    intro k
    induction k with
    | zero => intro _ i hi; omega
    | succ k ih =>
      intro hk i hi
      have ihk := ih (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact ihk i hlt
      · have hmin := hr_min i (by omega)
        push Not at hmin
        refine ⟨fun hW => runSet122 e W t ht hrec hper he0 i ihk hW, fun hW n => ?_⟩
        exact hmin.2 n
  have hrr := hrun r le_rfl
  have hset : ∀ k, k ≤ r → 2 * k < W → ∀ n, e n (2 * k) = 1 := fun k hk hW =>
    runSet122 e W t ht hrec hper he0 k (hrun k hk) hW
  -- the pair `r` is set at every time
  have hbase : 2 * r + 1 < W → ∀ n, e n (2 * r) = e n (2 * r + 1) := by
    intro hW n
    obtain ⟨n0, hn0⟩ : ∃ n, e n (2 * r + 1) ≠ 0 := by
      rcases hr_spec with h | h
      · omega
      · exact h
    have hc : ∀ m, e m (2 * r + 1) = e 0 (2 * r + 1) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [runConst122 e W t ht hrec hper he0 r hrr hW m, ih]
    rw [hset r le_rfl (by omega) n, hc n]
    have h1 : e 0 (2 * r + 1) ≠ 0 := by rw [← hc n0]; exact hn0
    rw [f1 _ h1]
  -- equal pairs from `r` on
  have hP : ∀ K, r ≤ K → 2 * K + 1 < W → ∀ n, e n (2 * K) = e n (2 * K + 1) := by
    intro K
    induction K using Nat.strong_induction_on with
    | _ K IH =>
      intro hrK hKW
      rcases Nat.eq_or_lt_of_le hrK with hK | hK
      · rw [← hK] at hKW ⊢
        exact hbase hKW
      · by_contra hne
        push Not at hne
        obtain ⟨n0, hn0⟩ := hne
        obtain ⟨L, rfl⟩ : ∃ L, K = L + 1 := ⟨K - 1, by omega⟩
        have hlow : ∀ n, e n (2 * L) = e n (2 * L + 1) := fun n =>
          IH L (by omega) (by omega) (by omega) n
        have hx : ∀ n, e (n + 1) (2 * L + 2) = e n (2 * L) + e n (2 * L + 2) := by
          intro n
          rw [rec2_122 e W hrec n (2 * L + 2) (2 * L) (2 * L + 1) (by omega) (by omega)
            (by omega), ← hlow n, fid]
        have hy : ∀ n, e (n + 1) (2 * L + 3) =
            f122 (e n (2 * L)) (e n (2 * L + 2)) (e n (2 * L + 3)) := by
          intro n
          rw [rec2_122 e W hrec n (2 * L + 3) (2 * L + 1) (2 * L + 2) (by omega) (by omega)
            (by omega), ← hlow n]
        have hn0' : e n0 (2 * L + 2) ≠ e n0 (2 * L + 3) := hn0
        -- the sum of the pair never rises
        have hnr : ∀ n, e n (2 * L + 2) + e n (2 * L + 3) = 0 →
            e (n + 1) (2 * L + 2) + e (n + 1) (2 * L + 3) = 0 := by
          intro n h
          rw [hx n, hy n]
          generalize e n (2 * L) = u at *
          generalize e n (2 * L + 2) = x at *
          generalize e n (2 * L + 3) = y at *
          revert u x y
          decide
        have hD : ∀ n, e n (2 * L + 2) + e n (2 * L + 3) ≠ 0 := by
          intro n1 h1
          have hall : ∀ m, n1 ≤ m → e m (2 * L + 2) + e m (2 * L + 3) = 0 := by
            intro m hm
            induction m, hm using Nat.le_induction with
            | base => exact h1
            | succ m hm ih => exact hnr m ih
          have := lift_122 e W t ht hper (j₁ := 2 * L + 2) (j₂ := 2 * L + 3) (by omega)
            (by omega) (fun a b => a + b = 0) n1 hall n0
          revert this hn0'
          generalize e n0 (2 * L + 2) = x
          generalize e n0 (2 * L + 3) = y
          revert x y
          decide
        -- the lower even column is clear at every time
        have hA : ∀ n, e n (2 * L + 2) = 0 → e n (2 * L) = 0 ∧ e (n + 1) (2 * L + 2) = 0 := by
          intro n hxn
          have h1 := hD n
          have h2 := hD (n + 1)
          rw [hx n, hy n] at h2
          rw [hx n]
          generalize e n (2 * L) = u at *
          generalize e n (2 * L + 2) = x at *
          generalize e n (2 * L + 3) = y at *
          revert u x y
          decide
        have hu : ∀ n, e n (2 * L) = 0 := by
          by_cases hz : ∃ n1, e n1 (2 * L + 2) = 0
          · obtain ⟨n1, hn1⟩ := hz
            have hall : ∀ m, n1 ≤ m → e m (2 * L + 2) = 0 := by
              intro m hm
              induction m, hm using Nat.le_induction with
              | base => exact hn1
              | succ m hm ih => exact (hA m ih).2
            intro n
            exact (hA n (lift_122 e W t ht hper (j₁ := 2 * L + 2) (j₂ := 2 * L + 2) (by omega)
              (by omega) (fun a _ => a = 0) n1 (fun m hm => hall m hm) n)).1
          · push Not at hz
            intro n
            have h1 := f1 _ (hz n)
            have h3 := f1 _ (hz (n + 1))
            have h2 := hx n
            rw [h3, h1] at h2
            revert h2
            generalize e n (2 * L) = u
            revert u
            decide
        -- the equal pairs below pass it down to the end of the run
        have hdown : ∀ d i, i + d = L → r ≤ i → ∀ n, e n (2 * i) = 0 := by
          intro d
          induction d with
          | zero => intro i hi _; rw [Nat.add_zero] at hi; subst hi; exact hu
          | succ d ihd =>
            intro i hi hri n
            have hup := ihd (i + 1) (by omega) (by omega) (n + 1)
            have hpair := IH i (by omega) hri (by omega) n
            have := rec2_122 e W hrec n (2 * i + 2) (2 * i) (2 * i + 1) (by omega) (by omega)
              (by omega)
            rw [show 2 * (i + 1) = 2 * i + 2 by ring] at hup
            have h0 := ihd (i + 1) (by omega) (by omega) n
            rw [show 2 * (i + 1) = 2 * i + 2 by ring] at h0
            rw [hup, ← hpair, h0, fid, add_zero] at this
            exact this.symm
        have h0 := hdown (L - r) r (by omega) le_rfl 0
        rw [hset r le_rfl (by omega) 0] at h0
        exact absurd h0 (by decide)
  refine ⟨r, fun k hk hW => hset k hk hW 0, fun k hk hW => hrr k hk |>.2 hW 0,
    fun k hk hW => hP k hk hW 0⟩


/-- **The hypotheses of the column statement meet**: at width `6`, period `2`, the family whose
columns `0, 1, 2, 3` read `1, 0, 1, 1` at every time and whose columns `4` and `5` read `0` at even
times and `1` at odd times (the windows `101100` and `101111`, a run of one pair `10`) obeys the
window recurrence of rule `122`, with its first cell set and every column of period `2`. -/
theorem periodicColumnsPaired122_nonvacuous (e : ℕ → ℕ → ZMod 2)
    (he : ∀ n j, e n j =
      if j = 1 then 0 else if j < 4 then 1 else if n % 2 = 0 then 0 else 1) :
    (∀ n j, j < 6 → e (n + 1) j =
      f122 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) ∧
    e 0 0 = 1 ∧ 0 < 2 ∧ (∀ n j, j < 6 → e (n + 2) j = e n j) := by
  refine ⟨?_, by simp [he], by decide, ?_⟩
  · intro n j hj
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
    · have h' : (n + 1) % 2 = 0 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
  · intro n j hj
    have h' : (n + 2) % 2 = n % 2 := by omega
    simp only [he, h']

/-- **Pure periodicity is needed**: at width `4`, the family reading `1101` at time `0`, `1111` at
odd times and `1100` at even times from `2` on obeys the window recurrence of rule `122`, with its
first cell set and every column of period `2` from time `2` on, yet no `r` makes it at time `0` a
run of `r` pairs `10`, then a set cell, then equal pairs. -/
theorem not_periodicColumnsPaired122_without_period (e : ℕ → ℕ → ZMod 2)
    (he : ∀ n j, e n j = if j < 2 then 1 else if n = 0 then (if j = 2 then 0 else 1)
      else if n % 2 = 1 then 1 else 0) :
    (∀ n j, j < 4 → e (n + 1) j =
      f122 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) ∧
    e 0 0 = 1 ∧ 0 < 2 ∧ (∀ n j, j < 4 → 2 ≤ n → e (n + 2) j = e n j) ∧
    ¬ ∃ r, (∀ k, k ≤ r → 2 * k < 4 → e 0 (2 * k) = 1) ∧
      (∀ k, k < r → 2 * k + 1 < 4 → e 0 (2 * k + 1) = 0) ∧
      (∀ k, r ≤ k → 2 * k + 1 < 4 → e 0 (2 * k) = e 0 (2 * k + 1)) := by
  refine ⟨?_, by simp [he], by decide, ?_, ?_⟩
  · intro n j hj
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · interval_cases j <;> (simp only [he]; decide)
    · have h1 : n ≠ 0 := hn.ne'
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have h' : (n + 1) % 2 = 1 := by omega
        interval_cases j <;>
          simp only [he, h, h', h1, Nat.add_one_ne_zero, Nat.reduceLT, Nat.reduceLeDiff,
            Nat.reduceSub, ↓reduceIte, zero_ne_one] <;>
          decide
      · have h' : (n + 1) % 2 = 0 := by omega
        interval_cases j <;>
          simp only [he, h, h', h1, Nat.add_one_ne_zero, Nat.reduceLT, Nat.reduceLeDiff,
            Nat.reduceSub, ↓reduceIte, zero_ne_one] <;>
          decide
  · intro n j hj hn
    have h' : (n + 2) % 2 = n % 2 := by omega
    have h1 : n ≠ 0 := by omega
    simp only [he, h', h1, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte]
  · rintro ⟨r, h1, -, h3⟩
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have := h3 1 (by omega) (by omega)
      simp [he] at this
    · have := h1 1 (by omega) (by omega)
      simp [he] at this

/-- Every set cell of a nonzero state sits at the leftmost set cell plus an offset below the
diameter. -/
private theorem exists_offset_of_ne122 {p : FiniteConfiguration} (hp : p ≠ 0) {i : ℤ}
    (hi : p i ≠ 0) : ∃ a : ℕ, a < p.diam ∧ i = p.leftEnd + a := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmem : i ∈ p.support := Finsupp.mem_support_iff.mpr hi
  have h1 : p.support.min' hne ≤ i := Finset.min'_le _ _ hmem
  have h2 : i ≤ p.support.max' hne := Finset.le_max' _ _ hmem
  rw [FiniteConfiguration.leftEnd_eq hne]
  rw [FiniteConfiguration.diam_eq' hne]
  refine ⟨(i - p.support.min' hne).toNat, by omega, by omega⟩

/-- The value of a translate at a cell. -/
private theorem translate_apply_sub122 (i : ℤ) (p : FiniteConfiguration) (x : ℤ) :
    translate i p x = p (x - i) := by
  have h := Finsupp.mapDomain_apply_of_injective (add_left_injective i) p (x - i)
  rw [sub_add_cancel] at h
  exact h

/-- The cells at and past the diameter, read from the leftmost set cell, are clear. -/
private theorem cell_zero_of_diam_le122 {p : FiniteConfiguration} (hp : p ≠ 0) (b : ℕ)
    (hb : p.diam ≤ b) : p (p.leftEnd + (b : ℤ)) = 0 := by
  by_contra hne
  obtain ⟨a, ha, hab⟩ := exists_offset_of_ne122 hp hne
  have : a = b := by omega
  omega

/-- The cell at the diameter minus one, read from the leftmost set cell, is set. -/
private theorem cell_last_eq_one122 {p : FiniteConfiguration} (hp : p ≠ 0) :
    p (p.leftEnd + ((p.diam - 1 : ℕ) : ℤ)) = 1 := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmem : p.support.max' hne ∈ p.support := Finset.max'_mem _ _
  have hmm := Finset.min'_le_max' p.support hne
  have hc : p.leftEnd + ((p.diam - 1 : ℕ) : ℤ) = p.support.max' hne := by
    rw [FiniteConfiguration.leftEnd_eq hne, FiniteConfiguration.diam_eq' hne]
    omega
  rw [hc]
  have h0 : p (p.support.max' hne) ≠ 0 := Finsupp.mem_support_iff.mp hmem
  generalize p (p.support.max' hne) = x at h0
  revert x
  decide

/-- **The window of a reproduced pattern at rule `122` is a run of pairs, then equal pairs**: read
from the leftmost set cell, the cells of the pattern up to its diameter plus two are at time `0` a
run of `r` pairs `10`, then a set cell, then equal pairs, given the column statement. -/
private theorem leftEnd_pairs122 (h : PeriodicColumnsPaired122) {p : FiniteConfiguration}
    (hrep : Reproduces (finRule f122 hq122) p) :
    ∃ r : ℕ, (∀ k, k ≤ r → 2 * k < p.diam + 2 → p (p.leftEnd + ((2 * k : ℕ) : ℤ)) = 1) ∧
      (∀ k, k < r → 2 * k + 1 < p.diam + 2 → p (p.leftEnd + ((2 * k + 1 : ℕ) : ℤ)) = 0) ∧
      (∀ k, r ≤ k → 2 * k + 1 < p.diam + 2 →
        p (p.leftEnd + ((2 * k : ℕ) : ℤ)) = p (p.leftEnd + ((2 * k + 1 : ℕ) : ℤ))) := by
  have hp : p ≠ 0 := hrep.1
  have h001 : f122 0 0 1 = 1 := by decide
  obtain ⟨t, ht, htp⟩ := leftWindowPeriodic f122 hq122 h001 p hrep 2
  obtain ⟨r, h1, h2, h3⟩ :=
    h (fun n j => ((finRule f122 hq122)^[n] p).leftWindow (p.diam + 2) j) (p.diam + 2) t
      (by
        intro n j hj
        rw [Function.iterate_succ_apply']
        exact FiniteConfiguration.leftWindow_finRule h001 (iterate_ne_zero hq122 h001 hp n) hj)
      (leftWindow_zero_ne hp (by omega)) ht (fun n j _ => congrFun (htp n) j)
  have hw : ∀ j : ℕ, j < p.diam + 2 →
      ((finRule f122 hq122)^[0] p).leftWindow (p.diam + 2) j = p (p.leftEnd + (j : ℤ)) := by
    intro j hj
    simp [FiniteConfiguration.leftWindow, hj]
  refine ⟨r, fun k hk hk2 => ?_, fun k hk hk2 => ?_, fun k hk hk2 => ?_⟩
  · have := h1 k hk hk2
    rwa [hw _ hk2] at this
  · have := h2 k hk hk2
    rwa [hw _ hk2] at this
  · have := h3 k hk hk2
    rwa [hw _ (by omega), hw _ hk2] at this

/-- **Rule `122` reproduces exactly the nonzero translates of doubled patterns**, from the statement
that purely periodic window columns are a run of pairs and then equal pairs as a hypothesis: the
window of width `diam p + 2` read from the leftmost set cell is such a family along the orbit, and
so is the window of the reflected pattern, since rule `122` is its own mirror. -/
theorem reproduces_iff_dbl_f122_of (h : PeriodicColumnsPaired122) (p : FiniteConfiguration) :
    Reproduces (finRule f122 hq122) p ↔ p ≠ 0 ∧ ∃ x c, p = translate c (dbl x) := by
  constructor
  · intro hrep
    have hp : p ≠ 0 := hrep.1
    have hw1 : 1 ≤ p.diam := FiniteConfiguration.one_le_diam hp
    have hzero := cell_zero_of_diam_le122 hp
    have hlast := cell_last_eq_one122 hp
    obtain ⟨r, h1, h2, h3⟩ := leftEnd_pairs122 h hrep
    have heven : p.diam % 2 = 0 := by
      by_contra hodd
      obtain ⟨m, hm⟩ : ∃ m, p.diam = 2 * m + 1 := ⟨p.diam / 2, by omega⟩
      rcases le_or_gt r m with hr | hr
      · have := h3 m hr (by omega)
        rw [hzero (2 * m + 1) (by omega)] at this
        have hl : p (p.leftEnd + ((2 * m : ℕ) : ℤ)) = 1 := by
          rw [← show p.diam - 1 = 2 * m by omega]
          exact hlast
        rw [hl] at this
        exact absurd this (by decide)
      · have := h1 (m + 1) hr (by omega)
        rw [hzero (2 * (m + 1)) (by omega)] at this
        exact absurd this (by decide)
    have hq2 : p (p.leftEnd + ((p.diam - 2 : ℕ) : ℤ)) = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, p.diam = 2 * k + 2 := ⟨p.diam / 2 - 1, by omega⟩
      have hkr : r ≤ k := by
        by_contra hlt
        push Not at hlt
        have := h2 k hlt (by omega)
        rw [show 2 * k + 1 = p.diam - 1 by omega, hlast] at this
        exact absurd this (by decide)
      have := h3 k hkr (by omega)
      rw [show 2 * k + 1 = p.diam - 1 by omega, hlast, show 2 * k = p.diam - 2 by omega] at this
      exact this
    have hrefl : Reproduces (finRule f122 hq122) (reflect p) := by
      have hm : mirrorRule f122 = f122 := by
        funext a b c
        revert a b c
        decide
      exact reproduces_congr hm _ hq122 (reproducesReflect _ hq122 p hrep)
    have hLr : (reflect p).leftEnd = -(p.leftEnd + ((p.diam - 1 : ℕ) : ℤ)) := by
      have hne' : (reflect p).support.Nonempty :=
        Finsupp.support_nonempty_iff.mpr (reflect_ne_zero hp)
      rw [FiniteConfiguration.leftEnd_eq hne']
      apply le_antisymm
      · apply Finset.min'_le
        rw [Finsupp.mem_support_iff, FiniteConfiguration.reflect_apply, neg_neg, hlast]
        decide
      · by_contra hlt
        push Not at hlt
        have hmem := Finset.min'_mem _ hne'
        rw [Finsupp.mem_support_iff, FiniteConfiguration.reflect_apply] at hmem
        generalize (reflect p).support.min' hne' = m at hlt hmem
        apply hmem
        have := hzero (-m - p.leftEnd).toNat (by omega)
        rwa [show p.leftEnd + ((-m - p.leftEnd).toNat : ℤ) = -m by omega] at this
    have hrc : ∀ j : ℕ, j < p.diam → reflect p ((reflect p).leftEnd + (j : ℤ)) =
        p (p.leftEnd + ((p.diam - 1 - j : ℕ) : ℤ)) := by
      intro j hj
      rw [FiniteConfiguration.reflect_apply, hLr]
      congr 1
      omega
    obtain ⟨r', g1, g2, g3⟩ := leftEnd_pairs122 h hrefl
    rw [FiniteConfiguration.diam_reflect] at g1 g2 g3
    have hr0 : r' = 0 := by
      by_contra hne
      have := g2 0 (by omega) (by omega)
      rw [hrc (2 * 0 + 1) (by omega),
        show p.diam - 1 - (2 * 0 + 1) = p.diam - 2 by omega, hq2] at this
      exact absurd this (by decide)
    subst hr0
    have hpair : ∀ i : ℕ, 2 * i + 1 < p.diam →
        p (p.leftEnd + ((2 * i : ℕ) : ℤ)) = p (p.leftEnd + ((2 * i + 1 : ℕ) : ℤ)) := by
      intro i hi
      have := g3 (p.diam / 2 - 1 - i) (Nat.zero_le _) (by omega)
      rw [hrc (2 * (p.diam / 2 - 1 - i)) (by omega),
        hrc (2 * (p.diam / 2 - 1 - i) + 1) (by omega),
        show p.diam - 1 - 2 * (p.diam / 2 - 1 - i) = 2 * i + 1 by omega,
        show p.diam - 1 - (2 * (p.diam / 2 - 1 - i) + 1) = 2 * i by omega] at this
      exact this.symm
    let g : ℤ → ℤ := fun i => p.leftEnd + 2 * i
    have hginj : Set.InjOn g (g ⁻¹' (p.support : Set ℤ)) := by
      intro a _ b _ hab
      simp only [g] at hab
      omega
    let x : FiniteConfiguration := Finsupp.comapDomain g p hginj
    have hx : ∀ i, x i = p (p.leftEnd + 2 * i) := fun i => rfl
    refine ⟨hp, x, p.leftEnd, ?_⟩
    ext j
    rw [translate_apply_sub122, dbl_apply, hx]
    by_cases hj : j < p.leftEnd
    · rw [FiniteConfiguration.eq_zero_of_lt_leftEnd hp hj,
        FiniteConfiguration.eq_zero_of_lt_leftEnd hp (by omega)]
    · obtain ⟨a, ha⟩ : ∃ a : ℕ, j = p.leftEnd + a := ⟨(j - p.leftEnd).toNat, by omega⟩
      subst ha
      have hdiv : (p.leftEnd + (a : ℤ) - p.leftEnd) / 2 = ((a / 2 : ℕ) : ℤ) := by
        rw [add_sub_cancel_left]; omega
      rw [hdiv]
      rcases Nat.mod_two_eq_zero_or_one a with he | ho
      · congr 1
        omega
      · by_cases hlt : a < p.diam
        · have := hpair (a / 2) (by omega)
          rw [show p.leftEnd + 2 * ((a / 2 : ℕ) : ℤ) = p.leftEnd + ((2 * (a / 2) : ℕ) : ℤ) by
            push_cast; ring, this]
          congr 1
          omega
        · rw [hzero a (by omega),
            show p.leftEnd + 2 * ((a / 2 : ℕ) : ℤ) = p.leftEnd + ((2 * (a / 2) : ℕ) : ℤ) by
              push_cast; ring]
          exact (hzero _ (by omega)).symm
  · rintro ⟨hp, x, c, rfl⟩
    have hx : x ≠ 0 := by
      rintro rfl
      apply hp
      have h0 : dbl (0 : FiniteConfiguration) = 0 := by
        ext j; simp [dbl_apply]
      rw [h0]
      exact Finsupp.mapDomain_zero
    exact Reproduces.translate f122 hq122
      (LocalRule.DoubledAgree.reproduces_dbl f122 hq122 doubledAgree_f122 hx) c

/-- **Rule `122` reproduces exactly the nonzero translates of doubled patterns.** -/
theorem reproduces_iff_dbl_f122 (p : FiniteConfiguration) :
    Reproduces (finRule f122 hq122) p ↔ p ≠ 0 ∧ ∃ x c, p = translate c (dbl x) :=
  reproduces_iff_dbl_f122_of periodicColumnsPaired122 p

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_dbl_f122_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_dbl_f122_of

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsPaired122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsPaired122

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsPaired122_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsPaired122_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_periodicColumnsPaired122_without_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_periodicColumnsPaired122_without_period

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_dbl_f122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_dbl_f122
