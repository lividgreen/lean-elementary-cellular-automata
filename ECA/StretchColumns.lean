module

public import ECA.ObservedColumn
public import ECA.Doubling
public import ErgodicTheory.DrivenColumns

/-!
# A stretch at two seams makes every column eventually periodic
([RuleSpace] §4 Proposition 4.2 and Proposition 4.5)

A local rule acts on the finitely-supported configurations of the line. Suppose that after `T`
steps the state `c` is a configuration on which `P` further steps act as a **stretch** at two
seams: the part of `c` left of a cell `lo` is shifted left by `dL` cells, the part from a cell `hi`
on is shifted right by `dR` cells, and the part between is kept (`stretch`). Then, if `c` already
repeats itself under those shifts on a band of width `2 P` at each seam, the stretch is repeated
at every later period: the state at time `T + k P` is the `k`-th iterate of the stretch applied to
`c`. Each cell of the iterated stretch is constant from some `k` on, so every cell is read at times
`T + k P + j` with a pattern that has settled, and **every column is eventually periodic**, with
period `P`.

## Main results

* `stretch` — the configuration `c` shifted left by `dL` left of `lo`, kept on `[lo, hi)`, and
  shifted right by `dR` from `hi` on.
* `eventuallyPeriodic_observedColumn_of_stretch` — **the conditional theorem**: at a quiescent
  local rule, a finite seed whose state at time `T + P` is the stretch of its state at time `T`,
  with that state repeating under the two shifts on the bands of width `2 P` at the seams, has
  every observed column eventually periodic.
* `eventuallyPeriodic_observedColumn_wolframRule50_single` — the instance: rule `50` from the
  single seed, with `T = 16`, `P = 2`, seams `-4` and `5` and shifts `2` and `2`, so every column
  of that table is eventually periodic.
* `listSeed` and `stretchCheck` — the seed that reads a list from cell `0` on, and the decidable
  check of the conditional theorem's hypotheses on the lists that seed reaches at times `T` and
  `T + P`.
* `eventuallyPeriodic_observedColumn_of_stretchCheck` — **the decided theorem**: if the check
  accepts, every observed column of the seed is eventually periodic. Its instance is checked by
  kernel evaluation, here for rule `50` from the single seed
  (`eventuallyPeriodic_observedColumn_of_stretchCheck_nonvacuous`).
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## The stretch -/

/-- The configuration `c` shifted left by `dL` left of `lo`, kept on `[lo, hi)`, and shifted right
by `dR` from `hi` on. -/
def stretch (lo hi : ℤ) (dL dR : ℕ) (c : ℤ → ZMod 2) : ℤ → ZMod 2 :=
  fun x => if x < lo then c (x + dL) else if x < hi then c x else c (x - dR)

private theorem stretch_left {lo hi : ℤ} {dL dR : ℕ} {c : ℤ → ZMod 2} {x : ℤ} (h : x < lo) :
    stretch lo hi dL dR c x = c (x + dL) := by
  simp [stretch, h]

private theorem stretch_mid {lo hi : ℤ} {dL dR : ℕ} {c : ℤ → ZMod 2} {x : ℤ} (h1 : lo ≤ x)
    (h2 : x < hi) : stretch lo hi dL dR c x = c x := by
  simp [stretch, not_lt.mpr h1, h2]

private theorem stretch_right {lo hi : ℤ} {dL dR : ℕ} {c : ℤ → ZMod 2} {x : ℤ} (h1 : lo ≤ x)
    (h2 : hi ≤ x) : stretch lo hi dL dR c x = c (x - dR) := by
  simp [stretch, not_lt.mpr h1, not_lt.mpr h2]

private theorem stretch_iterate_succ_left {lo hi : ℤ} {dL dR : ℕ} {c : ℤ → ZMod 2} {y : ℤ}
    (h : y < lo) (k : ℕ) :
    (stretch lo hi dL dR)^[k + 1] c y = (stretch lo hi dL dR)^[k] c (y + dL) := by
  rw [Function.iterate_succ_apply', stretch_left h]

private theorem stretch_iterate_succ_right {lo hi : ℤ} {dL dR : ℕ} {c : ℤ → ZMod 2} {y : ℤ}
    (h1 : lo ≤ y) (h2 : hi ≤ y) (k : ℕ) :
    (stretch lo hi dL dR)^[k + 1] c y = (stretch lo hi dL dR)^[k] c (y - dR) := by
  rw [Function.iterate_succ_apply', stretch_right h1 h2]

/-! ## The locality of finitely many steps -/

/-- **`n` steps of a local rule read `n` cells either side**: if two configurations agree up to a
translation by `d` on the cells within `n` of `x`, then `n` steps of the rule keep them in
agreement at `x`. -/
private theorem iterate_step_local (f : LocalRule) (d : ℤ) (u v : ℤ → ZMod 2) :
    ∀ (n : ℕ) (x : ℤ), (∀ y, x - n ≤ y → y ≤ x + n → u y = v (y + d)) →
      (LocalRuleColumns.step f)^[n] u x = (LocalRuleColumns.step f)^[n] v (x + d) := by
  intro n
  induction n with
  | zero =>
    intro x h
    simpa using h x (by simp) (by simp)
  | succ n ih =>
    intro x h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := ih (x - 1) (fun y hy1 hy2 => h y (by push_cast; omega) (by push_cast; omega))
    have h2 := ih x (fun y hy1 hy2 => h y (by push_cast; omega) (by push_cast; omega))
    have h3 := ih (x + 1) (fun y hy1 hy2 => h y (by push_cast; omega) (by push_cast; omega))
    change f _ _ _ = f _ _ _
    rw [h1, h2, h3, show x - 1 + d = x + d - 1 by ring, show x + 1 + d = x + d + 1 by ring]

/-! ## The iterated stretch -/

/-- **The band is fixed**: if `c` repeats itself under the two shifts on the bands of width `2 P`
at the seams, every iterate of the stretch agrees with `c` on `[lo - 2 P, hi + 2 P)`. -/
private theorem stretch_iterate_band (lo hi : ℤ) (dL dR : ℕ) (c : ℤ → ZMod 2) (P : ℕ)
    (hdL : (dL : ℤ) ≤ hi - lo) (hdR : (dR : ℤ) ≤ hi - lo)
    (hL : ∀ y, lo - 2 * P ≤ y → y < lo → c y = c (y + dL))
    (hR : ∀ y, hi ≤ y → y < hi + 2 * P → c y = c (y - dR)) :
    ∀ (k : ℕ) (y : ℤ), lo - 2 * P ≤ y → y < hi + 2 * P →
      (stretch lo hi dL dR)^[k] c y = c y := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro y hy1 hy2
    by_cases h1 : y < lo
    · rw [stretch_iterate_succ_left h1, ih (y + dL) (by omega) (by omega), hL y hy1 h1]
    · by_cases h2 : y < hi
      · rw [Function.iterate_succ_apply', stretch_mid (not_lt.mp h1) h2, ih y hy1 hy2]
      · rw [stretch_iterate_succ_right (not_lt.mp h1) (not_lt.mp h2),
          ih (y - dR) (by omega) (by omega), hR y (not_lt.mp h2) hy2]

/-- **`P` steps act as the stretch at every iterate**: if `P` steps of the rule act on `c` as the
stretch does, they act on every iterate of the stretch applied to `c` as the stretch does. -/
private theorem step_iterate_stretch (f : LocalRule) (lo hi : ℤ) (dL dR : ℕ) (c : ℤ → ZMod 2)
    (P : ℕ) (hdL : (dL : ℤ) ≤ hi - lo) (hdR : (dR : ℤ) ≤ hi - lo)
    (hL : ∀ y, lo - 2 * P ≤ y → y < lo → c y = c (y + dL))
    (hR : ∀ y, hi ≤ y → y < hi + 2 * P → c y = c (y - dR))
    (hstep : ∀ x, (LocalRuleColumns.step f)^[P] c x = stretch lo hi dL dR c x) :
    ∀ k : ℕ, (LocalRuleColumns.step f)^[P] ((stretch lo hi dL dR)^[k] c) =
      (stretch lo hi dL dR)^[k + 1] c := by
  have hband := stretch_iterate_band lo hi dL dR c P hdL hdR hL hR
  intro k
  induction k with
  | zero => exact funext hstep
  | succ k ih =>
    funext x
    by_cases hx1 : x + P < lo
    · have hloc : (LocalRuleColumns.step f)^[P] ((stretch lo hi dL dR)^[k + 1] c) x =
          (LocalRuleColumns.step f)^[P] ((stretch lo hi dL dR)^[k] c) (x + dL) :=
        iterate_step_local f dL _ _ P x (fun y _ hy2 =>
          stretch_iterate_succ_left (by omega) k)
      rw [hloc, ih, stretch_iterate_succ_left (by omega : x < lo) (k + 1)]
    · by_cases hx2 : hi + P ≤ x
      · have hloc : (LocalRuleColumns.step f)^[P] ((stretch lo hi dL dR)^[k + 1] c) x =
            (LocalRuleColumns.step f)^[P] ((stretch lo hi dL dR)^[k] c) (x + -(dR : ℤ)) :=
          iterate_step_local f (-(dR : ℤ)) _ _ P x (fun y hy1 _ => by
            rw [← sub_eq_add_neg]
            exact stretch_iterate_succ_right (by omega) (by omega) k)
        rw [hloc, ih, ← sub_eq_add_neg,
          stretch_iterate_succ_right (by omega : lo ≤ x) (by omega : hi ≤ x) (k + 1)]
      · have hloc : (LocalRuleColumns.step f)^[P] ((stretch lo hi dL dR)^[k + 1] c) x =
            (LocalRuleColumns.step f)^[P] c (x + 0) :=
          iterate_step_local f 0 _ _ P x (fun y h1 h2 => by
            rw [add_zero]
            exact hband (k + 1) y (by omega) (by omega))
        have hb1 : (stretch lo hi dL dR)^[1] c x = c x := hband 1 x (by omega) (by omega)
        have hb2 : (stretch lo hi dL dR)^[k + 1 + 1] c x = c x :=
          hband (k + 1 + 1) x (by omega) (by omega)
        rw [hloc, add_zero, hstep x, hb2]
        exact hb1

/-- **The state at time `T + k P`** is the `k`-th iterate of the stretch applied to the state at
time `T`. -/
private theorem iterate_period_eq (f : LocalRule) (lo hi : ℤ) (dL dR : ℕ) (s : ℤ → ZMod 2)
    (T P : ℕ)
    (hb : ∀ k : ℕ, (LocalRuleColumns.step f)^[P]
      ((stretch lo hi dL dR)^[k] ((LocalRuleColumns.step f)^[T] s)) =
      (stretch lo hi dL dR)^[k + 1] ((LocalRuleColumns.step f)^[T] s)) :
    ∀ k : ℕ, (LocalRuleColumns.step f)^[T + k * P] s =
      (stretch lo hi dL dR)^[k] ((LocalRuleColumns.step f)^[T] s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show T + (k + 1) * P = P + (T + k * P) by ring, Function.iterate_add_apply, ih, hb k]

/-- **Every cell of the iterated stretch settles**: from some iterate on, the value at the cell no
longer changes. -/
private theorem stretch_iterate_settles (lo hi : ℤ) (dL dR : ℕ) (c : ℤ → ZMod 2) (P : ℕ)
    (hdL : (dL : ℤ) ≤ hi - lo) (hdR : (dR : ℤ) ≤ hi - lo)
    (hL : ∀ y, lo - 2 * P ≤ y → y < lo → c y = c (y + dL))
    (hR : ∀ y, hi ≤ y → y < hi + 2 * P → c y = c (y - dR)) (y : ℤ) :
    ∃ K : ℕ, ∀ k, K ≤ k →
      (stretch lo hi dL dR)^[k + 1] c y = (stretch lo hi dL dR)^[k] c y := by
  have hband := stretch_iterate_band lo hi dL dR c P hdL hdR hL hR
  have left : ∀ m : ℕ, ∀ y : ℤ, y < lo → lo - y ≤ m → ∃ K : ℕ, ∀ k, K ≤ k →
      (stretch lo hi dL dR)^[k + 1] c y = (stretch lo hi dL dR)^[k] c y := by
    intro m
    induction m with
    | zero => intro y hy hm; omega
    | succ m ih =>
      intro y hy hm
      rcases Nat.eq_zero_or_pos dL with hd | hd
      · refine ⟨0, fun k _ => ?_⟩
        rw [stretch_iterate_succ_left hy, hd]
        simp
      · by_cases hy' : y + dL < lo
        · obtain ⟨K', hK'⟩ := ih (y + dL) hy' (by omega)
          refine ⟨K' + 1, fun k hk => ?_⟩
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [stretch_iterate_succ_left hy (j + 1), stretch_iterate_succ_left hy j]
          exact hK' j (by omega)
        · refine ⟨1, fun k hk => ?_⟩
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [stretch_iterate_succ_left hy (j + 1), stretch_iterate_succ_left hy j,
            hband (j + 1) (y + dL) (by omega) (by omega),
            hband j (y + dL) (by omega) (by omega)]
  have right : ∀ m : ℕ, ∀ y : ℤ, hi ≤ y → y - hi ≤ m → ∃ K : ℕ, ∀ k, K ≤ k →
      (stretch lo hi dL dR)^[k + 1] c y = (stretch lo hi dL dR)^[k] c y := by
    intro m
    induction m with
    | zero =>
      intro y hy hm
      have hyh : y = hi := by omega
      by_cases hd : dR = 0
      · refine ⟨0, fun k _ => ?_⟩
        rw [stretch_iterate_succ_right (by omega) hy, hd]
        simp
      · refine ⟨1, fun k hk => ?_⟩
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [stretch_iterate_succ_right (by omega) hy (j + 1),
          stretch_iterate_succ_right (by omega) hy j,
          hband (j + 1) (y - dR) (by omega) (by omega),
          hband j (y - dR) (by omega) (by omega)]
    | succ m ih =>
      intro y hy hm
      rcases Nat.eq_zero_or_pos dR with hd | hd
      · refine ⟨0, fun k _ => ?_⟩
        rw [stretch_iterate_succ_right (by omega) hy, hd]
        simp
      · by_cases hy' : hi ≤ y - dR
        · obtain ⟨K', hK'⟩ := ih (y - dR) hy' (by omega)
          refine ⟨K' + 1, fun k hk => ?_⟩
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [stretch_iterate_succ_right (by omega) hy (j + 1),
            stretch_iterate_succ_right (by omega) hy j]
          exact hK' j (by omega)
        · refine ⟨1, fun k hk => ?_⟩
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [stretch_iterate_succ_right (by omega) hy (j + 1),
            stretch_iterate_succ_right (by omega) hy j,
            hband (j + 1) (y - dR) (by omega) (by omega),
            hband j (y - dR) (by omega) (by omega)]
  by_cases h1 : y < lo
  · exact left (lo - y).toNat y h1 (by omega)
  · by_cases h2 : y < hi
    · refine ⟨0, fun k _ => ?_⟩
      rw [Function.iterate_succ_apply', stretch_mid (not_lt.mp h1) h2,
        hband k y (by omega) (by omega)]
    · exact right (y - hi).toNat y (not_lt.mp h2) (by omega)

/-! ## The column -/

/-- **The column of a stretch**: the function-level form of the conditional theorem, for a local
rule on all configurations of the line. -/
private theorem eventuallyPeriodic_column_of_stretch (f : LocalRule) (s : ℤ → ZMod 2) (T P : ℕ)
    (hP : 0 < P) (lo hi : ℤ) (dL dR : ℕ) (hdL : (dL : ℤ) ≤ hi - lo) (hdR : (dR : ℤ) ≤ hi - lo)
    (hstep : ∀ x, (LocalRuleColumns.step f)^[T + P] s x =
      stretch lo hi dL dR ((LocalRuleColumns.step f)^[T] s) x)
    (hL : ∀ y, lo - 2 * P ≤ y → y < lo →
      (LocalRuleColumns.step f)^[T] s y = (LocalRuleColumns.step f)^[T] s (y + dL))
    (hR : ∀ y, hi ≤ y → y < hi + 2 * P →
      (LocalRuleColumns.step f)^[T] s y = (LocalRuleColumns.step f)^[T] s (y - dR))
    (i : ℤ) :
    DrivenColumns.EventuallyPeriodic (LocalRuleColumns.column f s i) := by
  set c := (LocalRuleColumns.step f)^[T] s with hc
  have hstep' : ∀ x, (LocalRuleColumns.step f)^[P] c x = stretch lo hi dL dR c x := by
    intro x
    rw [← hstep x, hc, ← Function.iterate_add_apply, add_comm]
  have hb := step_iterate_stretch f lo hi dL dR c P hdL hdR hL hR hstep'
  have hper := iterate_period_eq f lo hi dL dR s T P hb
  have hsettle := stretch_iterate_settles lo hi dL dR c P hdL hdR hL hR
  choose Ky hKy using hsettle
  set K : ℕ := (Finset.range (2 * P + 1)).sup (fun m => Ky (i - P + m)) with hK
  refine ⟨P, T + K * P, hP, fun u hu => ?_⟩
  have hTu : T ≤ u := by
    have : 0 ≤ K * P := Nat.zero_le _
    omega
  obtain ⟨k, hk⟩ : ∃ k, k = (u - T) / P := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = (u - T) % P := ⟨_, rfl⟩
  have hdm := Nat.div_add_mod' (u - T) P
  rw [← hk, ← hj] at hdm
  have hjP : j < P := by rw [hj]; exact Nat.mod_lt _ hP
  have hKk : K ≤ k := by
    rw [hk]
    exact (Nat.le_div_iff_mul_le hP).mpr (by omega)
  have hu1 : u = j + (T + k * P) := by omega
  have hu2 : u + P = j + (T + (k + 1) * P) := by
    rw [show j + (T + (k + 1) * P) = (j + (T + k * P)) + P by ring, ← hu1]
  change (LocalRuleColumns.step f)^[u + P] s i = (LocalRuleColumns.step f)^[u] s i
  have e : ∀ k' : ℕ, (LocalRuleColumns.step f)^[j + (T + k' * P)] s =
      (LocalRuleColumns.step f)^[j] ((stretch lo hi dL dR)^[k'] c) := fun k' => by
    rw [Function.iterate_add_apply, hper k']
  rw [hu2, hu1, e, e]
  have hloc := iterate_step_local f 0 ((stretch lo hi dL dR)^[k + 1] c)
    ((stretch lo hi dL dR)^[k] c) j i (fun y hy1 hy2 => by
      rw [add_zero]
      have hy : (y - (i - P)).toNat ∈ Finset.range (2 * P + 1) :=
        Finset.mem_range.mpr (by omega)
      have hyy : i - P + (((y - (i - P)).toNat : ℕ) : ℤ) = y := by omega
      have hle := Finset.le_sup (f := fun m : ℕ => Ky (i - P + m)) hy
      rw [hyy] at hle
      exact hKy y k (le_trans hle hKk))
  rw [hloc, add_zero]

/-- **A stretch at two seams makes every observed column eventually periodic.** At a quiescent
local rule, let `s₀` be a finite seed whose state at time `T + P` is the stretch of its state at
time `T`, the seams `lo` and `hi` being at least as far apart as each of the two shifts, with the
state at time `T` repeating itself under the left shift on the `2 P` cells left of `lo` and under
the right shift on the `2 P` cells from `hi` on. Then the column at every cell is eventually
periodic. The stretch is repeated at every later period, each cell of the repeated stretch
settles, and a cell is read through `P` steps, which see `P` cells either side. -/
theorem eventuallyPeriodic_observedColumn_of_stretch (f : LocalRule) (hq : f 0 0 0 = 0)
    (s₀ : FiniteConfiguration) (T P : ℕ) (hP : 0 < P) (lo hi : ℤ) (dL dR : ℕ)
    (hdL : (dL : ℤ) ≤ hi - lo) (hdR : (dR : ℤ) ≤ hi - lo)
    (hstep : ∀ x, ((finRule f hq)^[T + P] s₀) x =
      stretch lo hi dL dR ⇑((finRule f hq)^[T] s₀) x)
    (hL : ∀ y, lo - 2 * P ≤ y → y < lo →
      ((finRule f hq)^[T] s₀) y = ((finRule f hq)^[T] s₀) (y + dL))
    (hR : ∀ y, hi ≤ y → y < hi + 2 * P →
      ((finRule f hq)^[T] s₀) y = ((finRule f hq)^[T] s₀) (y - dR))
    (i : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) s₀ i) := by
  rw [observedColumn_finRule_eq_column]
  refine eventuallyPeriodic_column_of_stretch f ⇑s₀ T P hP lo hi dL dR hdL hdR ?_ ?_ ?_ i
  · intro x
    have h := hstep x
    rw [coe_finRule_iterate, coe_finRule_iterate] at h
    exact h
  · intro y h1 h2
    have h := hL y h1 h2
    rw [coe_finRule_iterate] at h
    exact h
  · intro y h1 h2
    have h := hR y h1 h2
    rw [coe_finRule_iterate] at h
    exact h

/-! ## Simulating a finite window -/

/-- The value at cell `i` of the list `L` read from cell `0` on: the entry at `i`, and `0` outside
the list. -/
def listVal (L : List (ZMod 2)) (i : ℤ) : ZMod 2 :=
  if 0 ≤ i then L.getD i.toNat 0 else 0

/-- One step of a local rule on a list read from some cell `a`: the list of the new values on the
cells `a - 1, …, a + L.length`, computed along the list by carrying the two cells before the
current one. -/
def simStep (f : LocalRule) (L : List (ZMod 2)) : List (ZMod 2) :=
  go 0 0 L
where
  /-- The new values along a list, given the two cells read before its head. -/
  go (p q : ZMod 2) : List (ZMod 2) → List (ZMod 2)
    | [] => [f p q 0, f q 0 0]
    | x :: xs => f p q x :: go q x xs

/-- The configuration of the line that reads the list `L` from cell `a` on and is `0` elsewhere. -/
def listConfig (L : List (ZMod 2)) (a : ℤ) : ℤ → ZMod 2 :=
  fun x => listVal L (x - a)

private theorem listVal_of_neg (L : List (ZMod 2)) {i : ℤ} (h : i < 0) : listVal L i = 0 := by
  simp [listVal, not_le.mpr h]

private theorem listVal_of_nonneg (L : List (ZMod 2)) {i : ℤ} (h : 0 ≤ i) :
    listVal L i = L.getD i.toNat 0 := by
  simp [listVal, h]

private theorem listVal_of_ge (L : List (ZMod 2)) {i : ℤ} (h : (L.length : ℤ) ≤ i) :
    listVal L i = 0 := by
  have h0 : 0 ≤ i := le_trans (Int.natCast_nonneg _) h
  rw [listVal_of_nonneg L h0, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- The values of a list read from cell `0` on, with the two cells before it replaced by `p`
and `q`. -/
private def listExt (p q : ZMod 2) (L : List (ZMod 2)) (i : ℤ) : ZMod 2 :=
  if i = -2 then p else if i = -1 then q else listVal L i

private theorem listExt_zero (L : List (ZMod 2)) (i : ℤ) : listExt 0 0 L i = listVal L i := by
  unfold listExt
  split_ifs with h1 h2
  · rw [listVal_of_neg L (by omega)]
  · rw [listVal_of_neg L (by omega)]
  · rfl

private theorem listVal_cons_succ (x : ZMod 2) (xs : List (ZMod 2)) {i : ℤ} (h : 0 ≤ i) :
    listVal (x :: xs) (i + 1) = listVal xs i := by
  rw [listVal_of_nonneg _ (by omega), listVal_of_nonneg _ h,
    show (i + 1).toNat = i.toNat + 1 by omega]
  rfl

private theorem listExt_cons (p q x : ZMod 2) (xs : List (ZMod 2)) {i : ℤ} (h : -2 ≤ i) :
    listExt p q (x :: xs) (i + 1) = listExt q x xs i := by
  unfold listExt
  by_cases h2 : i = -2
  · subst h2
    simp
  · by_cases h1 : i = -1
    · subst h1
      simp [listVal]
    · have h3 : ¬ i + 1 = -2 := by omega
      have h4 : ¬ i + 1 = -1 := by omega
      simp only [h1, h2, h3, h4, ↓reduceIte]
      exact listVal_cons_succ x xs (by omega)

private theorem simStep_go_getD (f : LocalRule) (hq : f 0 0 0 = 0) (L : List (ZMod 2))
    (p q : ZMod 2) (j : ℕ) :
    (simStep.go f p q L).getD j 0 =
      f (listExt p q L ((j : ℤ) - 2)) (listExt p q L ((j : ℤ) - 1)) (listExt p q L j) := by
  induction L generalizing p q j with
  | nil =>
    rcases j with _ | _ | j
    · simp [simStep.go, listExt, listVal]
    · simp [simStep.go, listExt, listVal]
    · have e : ∀ i : ℤ, 0 ≤ i → listExt p q [] i = 0 := by
        intro i hi
        have h1 : ¬ i = -2 := by omega
        have h2 : ¬ i = -1 := by omega
        simp only [listExt, h1, h2, ↓reduceIte]
        exact listVal_of_ge [] (by simpa using hi)
      rw [e _ (by omega), e _ (by omega), e _ (by omega), hq]
      simp [simStep.go, List.getD_eq_getElem?_getD]
  | cons x xs ih =>
    rcases j with _ | j
    · simp [simStep.go, listExt, listVal]
    · simp only [simStep.go, List.getD_cons_succ]
      rw [ih]
      have e1 := listExt_cons p q x xs (i := (j : ℤ) - 2) (by omega)
      have e2 := listExt_cons p q x xs (i := (j : ℤ) - 1) (by omega)
      have e3 := listExt_cons p q x xs (i := (j : ℤ)) (by omega)
      rw [show ((j : ℤ) - 2 + 1) = ((j + 1 : ℕ) : ℤ) - 2 by push_cast; ring] at e1
      rw [show ((j : ℤ) - 1 + 1) = ((j + 1 : ℕ) : ℤ) - 1 by push_cast; ring] at e2
      rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring] at e3
      rw [e1, e2, e3]

private theorem listVal_simStep (f : LocalRule) (hq : f 0 0 0 = 0) (L : List (ZMod 2)) (j : ℤ) :
    listVal (simStep f L) j =
      f (listVal L (j - 2)) (listVal L (j - 1)) (listVal L j) := by
  by_cases h0 : 0 ≤ j
  · rw [listVal_of_nonneg _ h0, simStep, simStep_go_getD f hq, listExt_zero, listExt_zero,
      listExt_zero]
    simp [Int.toNat_of_nonneg h0]
  · have h1 : j < 0 := not_le.mp h0
    rw [listVal_of_neg _ h1, listVal_of_neg L (by omega), listVal_of_neg L (by omega),
      listVal_of_neg L h1, hq]

/-- **One step of the rule on a list read from a cell** is `simStep` read from the cell before. -/
private theorem step_listConfig (f : LocalRule) (hq : f 0 0 0 = 0) (L : List (ZMod 2)) (a : ℤ) :
    LocalRuleColumns.step f (listConfig L a) = listConfig (simStep f L) (a - 1) := by
  funext x
  simp only [LocalRuleColumns.step, listConfig]
  rw [listVal_simStep f hq, show x - (a - 1) - 2 = x - 1 - a by ring,
    show x - (a - 1) - 1 = x - a by ring, show x - (a - 1) = x + 1 - a by ring]

private theorem iterate_step_listConfig (f : LocalRule) (hq : f 0 0 0 = 0) (L : List (ZMod 2))
    (a : ℤ) (t : ℕ) :
    (LocalRuleColumns.step f)^[t] (listConfig L a) =
      listConfig ((simStep f)^[t] L) (a - t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, step_listConfig f hq, Function.iterate_succ_apply']
    congr 1
    push_cast
    ring

/-! ## A seed read from a list, and the decided hypotheses -/

/-- The finite configuration that reads the list `L` from cell `0` on and is `0` elsewhere. -/
noncomputable def listSeed (L : List (ZMod 2)) : FiniteConfiguration :=
  ∑ i ∈ Finset.range L.length, Finsupp.single (i : ℤ) (L.getD i 0)

private theorem coe_listSeed (L : List (ZMod 2)) : ⇑(listSeed L) = listConfig L 0 := by
  funext x
  simp only [listSeed, listConfig, sub_zero, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply]
  by_cases h0 : 0 ≤ x
  · by_cases hl : x.toNat < L.length
    · rw [Finset.sum_eq_single_of_mem x.toNat (Finset.mem_range.mpr hl), listVal_of_nonneg L h0]
      · simp [Int.toNat_of_nonneg h0]
      · intro b _ hb
        rw [ite_eq_right_iff]
        intro h
        exfalso
        omega
    · rw [Finset.sum_eq_zero, listVal_of_ge L (by omega)]
      intro b hb
      rw [ite_eq_right_iff]
      intro h
      have := Finset.mem_range.mp hb
      exfalso
      omega
  · rw [Finset.sum_eq_zero, listVal_of_neg L (not_le.mp h0)]
    intro b _
    rw [ite_eq_right_iff]
    intro h
    exfalso
    omega

/-- The list `[1]` read from cell `0` is the single seed. -/
theorem listSeed_one : listSeed [1] = Finsupp.single 0 1 := by
  simp [listSeed]

private theorem coe_iterate_listSeed (f : LocalRule) (hq : f 0 0 0 = 0) (L : List (ZMod 2))
    (t : ℕ) :
    ⇑((finRule f hq)^[t] (listSeed L)) = listConfig ((simStep f)^[t] L) (0 - t) := by
  rw [coe_finRule_iterate, coe_listSeed, iterate_step_listConfig f hq]

/-- Proposition 4.6's hypotheses, decided on the lists the seed reaches at times `T` and
`T + P`: `0 < P`, `dL` and `dR` at most `hi - lo`, the stretch at every cell of a window that
covers both lists and both seams, and the two seam bands. -/
def stretchCheck (f : LocalRule) (seed : List (ZMod 2)) (T P : ℕ) (lo hi : ℤ) (dL dR : ℕ) :
    Bool :=
  decide (0 < P) && decide ((dL : ℤ) ≤ hi - lo) && decide ((dR : ℤ) ≤ hi - lo) &&
  (List.range (max (max (0 - (T : ℤ) + ((simStep f)^[T] seed).length)
        (0 - ((T + P : ℕ) : ℤ) + ((simStep f)^[T + P] seed).length)) hi + dR -
      (min (0 - ((T + P : ℕ) : ℤ)) lo - dL)).toNat).all (fun k =>
    decide (listConfig ((simStep f)^[T + P] seed) (0 - ((T + P : ℕ) : ℤ))
        (min (0 - ((T + P : ℕ) : ℤ)) lo - dL + k) =
      stretch lo hi dL dR (listConfig ((simStep f)^[T] seed) (0 - (T : ℤ)))
        (min (0 - ((T + P : ℕ) : ℤ)) lo - dL + k))) &&
  (List.range (2 * P)).all (fun k =>
    decide (listConfig ((simStep f)^[T] seed) (0 - (T : ℤ)) (lo - 2 * P + k) =
      listConfig ((simStep f)^[T] seed) (0 - (T : ℤ)) (lo - 2 * P + k + dL))) &&
  (List.range (2 * P)).all (fun k =>
    decide (listConfig ((simStep f)^[T] seed) (0 - (T : ℤ)) (hi + k) =
      listConfig ((simStep f)^[T] seed) (0 - (T : ℤ)) (hi + k - dR)))

private theorem listConfig_of_lt (L : List (ZMod 2)) (a x : ℤ) (h : x < a) :
    listConfig L a x = 0 :=
  listVal_of_neg L (by omega)

private theorem listConfig_of_ge (L : List (ZMod 2)) (a x : ℤ) (h : a + L.length ≤ x) :
    listConfig L a x = 0 :=
  listVal_of_ge L (by omega)

/-- **A decided stretch makes every observed column eventually periodic.** If `stretchCheck`
accepts the parameters at a seed list, the three hypotheses of the conditional theorem hold for
the seed it reads: the window check covers every cell where either list can be nonzero, and the
cells beyond it are zero on both sides of the stretch. -/
theorem eventuallyPeriodic_observedColumn_of_stretchCheck (f : LocalRule) (hq : f 0 0 0 = 0)
    (seed : List (ZMod 2)) (T P : ℕ) (lo hi : ℤ) (dL dR : ℕ)
    (h : stretchCheck f seed T P lo hi dL dR = true) (i : ℤ) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) (listSeed seed) i) := by
  simp only [stretchCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hP, hdL⟩, hdR⟩, hwin⟩, hbl⟩, hbr⟩ := h
  set w0 : ℤ := min (0 - ((T + P : ℕ) : ℤ)) lo - dL with hw0
  set w1 : ℤ := max (max (0 - (T : ℤ) + ((simStep f)^[T] seed).length)
    (0 - ((T + P : ℕ) : ℤ) + ((simStep f)^[T + P] seed).length)) hi + dR with hw1
  refine eventuallyPeriodic_observedColumn_of_stretch f hq (listSeed seed) T P hP lo hi dL dR
    hdL hdR ?_ ?_ ?_ i
  · intro x
    rw [coe_iterate_listSeed, coe_iterate_listSeed]
    by_cases hx0 : x < w0
    · rw [stretch_left (by omega), listConfig_of_lt _ _ _ (by omega),
        listConfig_of_lt _ _ _ (by omega)]
    · by_cases hx1 : x < w1
      · have := hwin (x - w0).toNat (by omega)
        rwa [show w0 + (((x - w0).toNat : ℕ) : ℤ) = x by omega] at this
      · rw [stretch_right (by omega) (by omega), listConfig_of_ge _ _ _ (by omega),
          listConfig_of_ge _ _ _ (by omega)]
  · intro y h1 h2
    rw [coe_iterate_listSeed]
    have := hbl (y - (lo - 2 * P)).toNat (by omega)
    rwa [show lo - 2 * (P : ℤ) + (((y - (lo - 2 * P)).toNat : ℕ) : ℤ) = y by omega] at this
  · intro y h1 h2
    rw [coe_iterate_listSeed]
    have := hbr (y - hi).toNat (by omega)
    rwa [show hi + (((y - hi).toNat : ℕ) : ℤ) = y by omega] at this

/-- **The check accepts at an instance**: rule `50` from the single seed with `T = 16`, `P = 2`,
seams `-4` and `5` and shifts `2` and `2`, so the decided theorem applies there. -/
theorem eventuallyPeriodic_observedColumn_of_stretchCheck_nonvacuous :
    stretchCheck (wolframRule 50) [1] 16 2 (-4) 5 2 2 = true := by
  decide +kernel

/-! ## Rule `50` from the single seed -/

private theorem coe_single_eq_listConfig :
    ⇑(Finsupp.single (0 : ℤ) (1 : ZMod 2)) = listConfig [1] 0 := by
  funext x
  simp only [listConfig, sub_zero, Finsupp.single_apply]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [listVal_of_neg _ h]
    simp [show ¬ (0 : ℤ) = x by omega]
  · subst h
    simp [listVal]
  · rw [listVal_of_ge _ (by simp; omega)]
    simp [show ¬ (0 : ℤ) = x by omega]

private theorem coe_iterate_single (f : LocalRule) (hq : f 0 0 0 = 0) (t : ℕ) :
    ⇑((finRule f hq)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) =
      listConfig ((simStep f)^[t] [1]) (0 - t) := by
  rw [coe_finRule_iterate, coe_single_eq_listConfig, iterate_step_listConfig f hq]

private theorem length_simStep_go (f : LocalRule) (p q : ZMod 2) (L : List (ZMod 2)) :
    (simStep.go f p q L).length = L.length + 2 := by
  induction L generalizing p q with
  | nil => rfl
  | cons x xs ih => simp [simStep.go, ih]

private theorem length_simStep (f : LocalRule) (L : List (ZMod 2)) :
    (simStep f L).length = L.length + 2 :=
  length_simStep_go f 0 0 L

private theorem length_iterate_simStep (f : LocalRule) (L : List (ZMod 2)) (t : ℕ) :
    ((simStep f)^[t] L).length = L.length + 2 * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', length_simStep, ih]
    ring

/-- The list the single seed reaches at time `16` under rule `50`. -/
private def row16 : List (ZMod 2) := (simStep (wolframRule 50))^[16] [1]

/-- The list the single seed reaches at time `18` under rule `50`. -/
private def row18 : List (ZMod 2) := (simStep (wolframRule 50))^[18] [1]

private theorem rule50_window :
    ∀ k : ℕ, k < 42 → listConfig row18 (0 - ((18 : ℕ) : ℤ)) ((k : ℤ) - 20) =
      stretch (-4) 5 2 2 (listConfig row16 (0 - ((16 : ℕ) : ℤ))) ((k : ℤ) - 20) := by
  decide +kernel

private theorem rule50_left_seam :
    ∀ k : ℕ, k < 4 → listConfig row16 (0 - ((16 : ℕ) : ℤ)) (-8 + (k : ℤ)) =
      listConfig row16 (0 - ((16 : ℕ) : ℤ)) (-8 + (k : ℤ) + ((2 : ℕ) : ℤ)) := by
  decide +kernel

private theorem rule50_right_seam :
    ∀ k : ℕ, k < 4 → listConfig row16 (0 - ((16 : ℕ) : ℤ)) (5 + (k : ℤ)) =
      listConfig row16 (0 - ((16 : ℕ) : ℤ)) (5 + (k : ℤ) - ((2 : ℕ) : ℤ)) := by
  decide +kernel

private theorem rule50_stretch (x : ℤ) :
    listConfig row18 (0 - ((18 : ℕ) : ℤ)) x =
      stretch (-4) 5 2 2 (listConfig row16 (0 - ((16 : ℕ) : ℤ))) x := by
  have hl16 : row16.length = 33 := by decide +kernel
  have hl18 : row18.length = 37 := by decide +kernel
  by_cases hx : -20 ≤ x ∧ x ≤ 21
  · have h := rule50_window (x + 20).toNat (by omega)
    have hk : (((x + 20).toNat : ℕ) : ℤ) - 20 = x := by omega
    rwa [hk] at h
  · rcases (by omega : x < -20 ∨ 21 < x) with h | h
    · rw [stretch_left (by omega)]
      simp only [listConfig]
      rw [listVal_of_neg _ (by simp; omega), listVal_of_neg _ (by simp; omega)]
    · rw [stretch_right (by omega) (by omega)]
      simp only [listConfig]
      rw [listVal_of_ge _ (by rw [hl18]; simp; omega), listVal_of_ge _ (by rw [hl16]; simp; omega)]

/-- **Every column of rule `50` from the single seed is eventually periodic.** The state at time
`18` is the stretch of the state at time `16` with seams `-4` and `5` and shifts `2` and `2`, and
the state at time `16` repeats itself under both shifts on the four cells at each seam; the
conditional theorem on the stretch then applies, with period `2`. The three hypotheses are
finite checks on the window `[-20, 21]` of the state's cells, by kernel evaluation of the rule on
the list the seed reaches. This instance meets every hypothesis of the conditional theorem at
once. -/
theorem eventuallyPeriodic_observedColumn_wolframRule50_single
    (hq : wolframRule 50 0 0 0 = 0) (i : ℤ) :
    DrivenColumns.EventuallyPeriodic
      (observedColumn (finRule (wolframRule 50) hq) (Finsupp.single 0 1) i) := by
  refine eventuallyPeriodic_observedColumn_of_stretch (wolframRule 50) hq _ 16 2 (by norm_num)
    (-4) 5 2 2 (by norm_num) (by norm_num) ?_ ?_ ?_ i
  · intro x
    rw [coe_iterate_single, coe_iterate_single]
    exact rule50_stretch x
  · intro y h1 h2
    rw [coe_iterate_single]
    have h := rule50_left_seam (y + 8).toNat (by omega)
    have hk : -8 + (((y + 8).toNat : ℕ) : ℤ) = y := by omega
    rw [hk] at h
    exact h
  · intro y h1 h2
    rw [coe_iterate_single]
    have h := rule50_right_seam (y - 5).toNat (by omega)
    have hk : 5 + (((y - 5).toNat : ℕ) : ℤ) = y := by omega
    rw [hk] at h
    exact h

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_of_stretch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_of_stretch

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_wolframRule50_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_wolframRule50_single

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_of_stretchCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_of_stretchCheck
