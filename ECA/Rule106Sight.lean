module

public import ECA.Rule106Hits
import all ECA.Rule106
import all ECA.Rule106Level
import all ECA.Rule106Hits

/-!
# Rule `106` against a hit: the level reading is not local
([RuleSpace] §5)

The pair `11` of rule `106` has a support bound at every scale: its orbit is clear from cell
`12 * 2 ^ a - 3` on through step `32 * 4 ^ a - 7`, and the bound is sharp. Two pair lattices
far apart then evolve independently while the left one is clear at the seam, and the hit at cell
`2` of the staying window `pairLattice {0, 2 ^ a}`, renormalized, is seen at level step
`8 * 4 ^ a + 1` at the sampled cell `renormCell (6 * 2 ^ a + 3)`, while at the lone pair the same
hit is unseen at every level step.

## Main results

* `window106_iterate_pair_eq_zero_of_le` — the orbit of the pair is clear from cell
  `12 * 2 ^ a - 3` on through step `32 * 4 ^ a - 7`;
  `window106_iterate_pair_eq_zero_of_le_nonvacuous` meets both hypotheses at their edge, and
  `window106_iterate_pair_sharp` shows the bound fails at the next step.
* `windowShift` / `window106_iterate_add_windowShift` — the window shifted right by `c` cells, and
  the evolution of a window plus a shifted window while the first stays clear at the seam.
* `window106_seen_hit_far` — the hit at cell `2` of the renormalized pair lattice on
  `{0, 2 ^ a}` is seen at level step `8 * 4 ^ a + 1` at cell `renormCell (6 * 2 ^ a + 3)`.
* `window106_unseen_hit_pair` — the same hit at the lone pair is unseen at every level step.
* `window106_sight_not_local` — the staying windows `pairLattice {0, 2 ^ a}` and the lone pair
  have renormalizations agreeing on every cell below `12 * 2 ^ a`, and the hit is seen at the
  first and unseen at the second.
-/

@[expose] public section

namespace ECA

/-! ## The support of the orbit of the pair -/

/-- The window is clear from cell `m` on. -/
private def ClearFrom (m : ℕ) (w : ℕ → ZMod 2) : Prop :=
  ∀ j, m ≤ j → w j = 0

private theorem ClearFrom.mono {m m' : ℕ} {w : ℕ → ZMod 2} (h : ClearFrom m w) (hm : m ≤ m') :
    ClearFrom m' w :=
  fun j hj => h j (hm.trans hj)

private theorem clearFrom_window106 {m : ℕ} {w : ℕ → ZMod 2} (h : ClearFrom m w) :
    ClearFrom (m + 1) (window106 w) := by
  intro j hj
  have h1 : w j = 0 := h j (by omega)
  have h2 : (if 1 ≤ j then w (j - 1) else 0) = 0 := by
    split_ifs with hh
    · exact h _ (by omega)
    · rfl
  simp only [window106, h1, h2, mul_zero, add_zero]

private theorem clearFrom_iterate {m : ℕ} {w : ℕ → ZMod 2} (h : ClearFrom m w) (r : ℕ) :
    ClearFrom (m + r) (window106^[r] w) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact clearFrom_window106 ih

private theorem clearFrom_renorm {m : ℕ} {w : ℕ → ZMod 2} (hm : 1 ≤ m) (h : ClearFrom m w) :
    ClearFrom (2 * m - 1) (renorm w) := by
  intro i hi
  unfold renorm
  split_ifs <;> first | rfl | exact h _ (by omega)

private theorem orbit_clear_base (t : ℕ) (ht : t ≤ 25) :
    ClearFrom 9 (window106^[t] (pairLattice {0})) := by
  have hS : ∀ k < 26, ∀ r ∈ (blockStep 12)^[k] ({0, 1} : Finset ℕ), r ≤ 8 := by decide +kernel
  rw [orbit_block t (fun k hk r hr => by have := hS k (by omega) r hr; omega)]
  intro j hj
  unfold blockLattice
  rw [ite_eq_right_iff]
  rintro ⟨h1, h2⟩
  have := hS t (by omega) _ h1
  simp only [Finset.mem_singleton] at h2
  omega

private theorem quadDigits_mersenne (b : ℕ) : 3 * quadDigits (2 ^ b - 1) + 1 = 4 ^ b := by
  induction b with
  | zero => simp [quadDigits_zero]
  | succ b ih =>
    have hp : 0 < 2 ^ b := Nat.two_pow_pos b
    have e : 2 ^ (b + 1) - 1 = 2 * (2 ^ b - 1) + 1 := by
      rw [pow_succ]
      omega
    rw [e, quadDigits_double_succ, pow_succ]
    omega

/-- The orbit of the pair at step `32 * 4 ^ b - 32` is the pairs at the cells `12 * x`,
`x < 2 ^ b`. -/
private theorem orbit_snapshot (b : ℕ) :
    window106^[32 * 4 ^ b - 32] (pairLattice {0}) =
      blockLattice 12 {0, 1} (Finset.range (2 ^ b)) := by
  have h := iterate_pairLattice rule106Renorm rule106Step24 (2 * (2 ^ b - 1))
  have hq := quadDigits_mersenne b
  rw [quadDigits_double, submasks_double, submasks_mersenne, pairLattice_double_eq] at h
  rw [← h]
  congr 1
  omega

private theorem blockLattice_twelve_twentyfour (N : ℕ) :
    blockLattice 12 {0, 1} (Finset.range (2 * N)) =
      blockLattice 24 {0, 1, 12, 13} (Finset.range N) := by
  funext i
  unfold blockLattice
  apply if_congr _ rfl rfl
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range]
  omega

/-- **The orbit of the pair is clear from cell `12 * 2 ^ a - 3` through step `32 * 4 ^ a - 7`**,
at every scale `a`. -/
theorem window106_iterate_pair_eq_zero_of_le (a t j : ℕ) (ht : t + 7 ≤ 32 * 4 ^ a)
    (hj : 12 * 2 ^ a ≤ j + 3) : window106^[t] (pairLattice {0}) j = 0 := by
  have key : ∀ a t : ℕ, t + 7 ≤ 32 * 4 ^ a →
      ClearFrom (12 * 2 ^ a - 3) (window106^[t] (pairLattice {0})) := by
    intro a
    induction a with
    | zero =>
      intro t ht
      simpa using orbit_clear_base t (by simpa using ht)
    | succ a ih =>
      intro t ht
      have hX : 0 < 4 ^ a := by positivity
      have hY : 0 < 2 ^ a := Nat.two_pow_pos a
      rw [pow_succ] at ht
      rw [pow_succ]
      by_cases hc : t / 4 + 7 ≤ 32 * 4 ^ a
      · have e : window106^[t] (pairLattice {0}) =
            window106^[t % 4] (renorm (window106^[t / 4] (pairLattice {0}))) := by
          rw [← rule106Renorm (t / 4), ← Function.iterate_add_apply]
          congr 1
          omega
        rw [e]
        have h2 := clearFrom_renorm (by omega) (ih (t / 4) hc)
        have h3 := clearFrom_iterate h2 (t % 4)
        exact h3.mono (by omega)
      · have hsnap := orbit_snapshot (a + 1)
        rw [show (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a from by ring,
          blockLattice_twelve_twentyfour (2 ^ a)] at hsnap
        have hS : ∀ k < 26, ∀ r ∈ (blockStep 24)^[k] ({0, 1, 12, 13} : Finset ℕ), r ≤ 20 := by
          decide +kernel
        have e : window106^[t] (pairLattice {0}) =
            window106^[t - (32 * 4 ^ (a + 1) - 32)]
              (window106^[32 * 4 ^ (a + 1) - 32] (pairLattice {0})) := by
          rw [← Function.iterate_add_apply]
          congr 1
          rw [pow_succ]
          omega
        rw [e, hsnap, window106_iterate_blockLattice (by norm_num) _ _ _
          (fun k hk r hr => by have := hS k (by rw [pow_succ] at *; omega) r hr; omega)]
        intro j hj
        unfold blockLattice
        rw [ite_eq_right_iff]
        rintro ⟨h1, h2⟩
        have := hS (t - (32 * 4 ^ (a + 1) - 32)) (by rw [pow_succ] at *; omega) _ h1
        simp only [Finset.mem_range] at h2
        omega
  exact key a t ht j (by omega)

private theorem pair_eq_winOfNat : pairLattice {0} = winOfNat 3 := by
  funext j
  by_cases hj : j < 12
  · interval_cases j <;> decide
  · rw [winOfNat_apply_of_lt (L := 2) (by norm_num) (by omega)]
    simp only [pairLattice, Finset.mem_singleton]
    exact ite_eq_right (fun h => by omega)

private theorem pair_iterate_apply (n j : ℕ) :
    window106^[n] (pairLattice {0}) j = if (stepNat^[n] 3).testBit j then 1 else 0 := by
  rw [pair_eq_winOfNat, iterate_winOfNat]
  rfl

/-- **The support bound has content**: at scale `1`, step `121` and cell `21`, both hypotheses
hold at their edge and the cell is clear. -/
theorem window106_iterate_pair_eq_zero_of_le_nonvacuous :
    121 + 7 ≤ 32 * 4 ^ 1 ∧ 12 * 2 ^ 1 ≤ 21 + 3 ∧ window106^[121] (pairLattice {0}) 21 = 0 :=
  ⟨by norm_num, by norm_num,
    window106_iterate_pair_eq_zero_of_le 1 121 21 (by norm_num) (by norm_num)⟩

/-- **The support bound is sharp in time**: at scale `1` the cell `21` is set at step `122`, the
step after the bound. -/
theorem window106_iterate_pair_sharp : window106^[122] (pairLattice {0}) 21 = 1 := by
  have h : (stepNat^[122] 3).testBit 21 = true := by decide +kernel
  rw [pair_iterate_apply, h]
  rfl

/-! ## A window beside a shifted window -/

/-- **A window shifted right by `c` cells**: cell `i` is cell `i - c` of `B` from `c` on and
clear below. -/
def windowShift (c : ℕ) (B : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  fun i => if c ≤ i then B (i - c) else 0

private theorem window106_add_windowShift {c : ℕ} (hc : 2 ≤ c) (A B : ℕ → ZMod 2)
    (hA : ClearFrom (c - 2) A) :
    window106 (A + windowShift c B) = window106 A + windowShift c (window106 B) := by
  funext j
  simp only [window106, windowShift, Pi.add_apply]
  rw [Nat.sub_right_comm j 2 c, Nat.sub_right_comm j 1 c]
  by_cases hjc : c ≤ j
  · have a0 : A j = 0 := hA j (by omega)
    have a2 : A (j - 2) = 0 := hA _ (by omega)
    have a1 : A (j - 1) = 0 := hA _ (by omega)
    simp only [a0, a1, a2, mul_zero, add_zero, zero_add, ite_self]
    split_ifs <;> first | rfl | (exfalso; omega)
  · split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- **A window plus a shifted window evolve apart while the first stays clear at the seam**:
for a cell `c ≥ 2`, if the first `n` iterates of `A` are clear from cell `c - 2` on, then `n`
steps on `A` plus `B` shifted by `c` are the `n`-th iterate of `A` plus the `n`-th iterate of `B`
shifted by `c`. -/
theorem window106_iterate_add_windowShift {c : ℕ} (hc : 2 ≤ c) (A B : ℕ → ZMod 2) (n : ℕ)
    (hA : ∀ m < n, ∀ i, c - 2 ≤ i → window106^[m] A i = 0) :
    window106^[n] (A + windowShift c B) =
      window106^[n] A + windowShift c (window106^[n] B) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun m hm => hA m (by omega)),
      window106_add_windowShift hc _ _ (hA n (by omega))]

private theorem window106_windowShift (c : ℕ) (B : ℕ → ZMod 2) :
    window106 (windowShift c B) = windowShift c (window106 B) := by
  funext j
  simp only [window106, windowShift]
  rw [Nat.sub_right_comm j 2 c, Nat.sub_right_comm j 1 c]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem window106_iterate_windowShift (c n : ℕ) (B : ℕ → ZMod 2) :
    window106^[n] (windowShift c B) = windowShift c (window106^[n] B) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, window106_windowShift]

/-- Cells read: `n` steps read the `2 * n` cells to the left. -/
private theorem window106_iterate_congr (V W : ℕ → ZMod 2) (n : ℕ) :
    ∀ j, (∀ i, j ≤ i + 2 * n → i ≤ j → V i = W i) →
      window106^[n] V j = window106^[n] W j := by
  induction n with
  | zero => intro j h; exact h j (by omega) le_rfl
  | succ n ih =>
    intro j h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [window106]
    have e0 : window106^[n] V j = window106^[n] W j :=
      ih j (fun i h1 h2 => h i (by omega) h2)
    have e2 : 2 ≤ j → window106^[n] V (j - 2) = window106^[n] W (j - 2) := fun hj =>
      ih _ (fun i h1 h2 => h i (by omega) (by omega))
    have e1 : 1 ≤ j → window106^[n] V (j - 1) = window106^[n] W (j - 1) := fun hj =>
      ih _ (fun i h1 h2 => h i (by omega) (by omega))
    rw [e0]
    by_cases h2 : 2 ≤ j <;> by_cases h1 : 1 ≤ j <;> simp [h1, h2, e1, e2]

/-! ## The seen hit at the far pair -/

private theorem pairLattice_two {N : ℕ} (hN : 1 ≤ N) :
    pairLattice {0, N} = pairLattice {0} + windowShift (6 * N) (pairLattice {0}) := by
  funext i
  simp only [pairLattice, windowShift, Pi.add_apply, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem renorm_pairLattice_two (a : ℕ) :
    renorm (pairLattice {0, 2 ^ a}) =
      pairLattice {0} + windowShift (12 * 2 ^ a) (pairLattice {0}) := by
  have hp : 0 < 2 ^ a := Nat.two_pow_pos a
  rw [renorm_pairLattice, show ({0, 2 ^ a} : Finset ℕ).image (2 * ·) = {0, 2 * 2 ^ a} from by simp,
    pairLattice_two (by omega), show 6 * (2 * 2 ^ a) = 12 * 2 ^ a by ring]

private theorem pairLattice_add_single :
    pairLattice {0} + Pi.single 2 1 = window106 (pairLattice {0}) := by
  funext j
  rw [window106_pair_apply]
  by_cases hj : j < 8
  · interval_cases j <;> decide +kernel
  · have h2 : j ≠ 2 := by omega
    have h3 : j ∉ ({0, 1, 2} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    simp [pairLattice_zero_ge (by omega : 2 ≤ j), h2, h3]

private theorem renorm_pairLattice_two_add_single (a : ℕ) :
    renorm (pairLattice {0, 2 ^ a}) + Pi.single 2 1 =
      window106 (pairLattice {0}) + windowShift (12 * 2 ^ a) (pairLattice {0}) := by
  have hp : 0 < 2 ^ a := Nat.two_pow_pos a
  rw [renorm_pairLattice_two, add_right_comm, pairLattice_add_single]

private theorem orbit_zero_seam (a : ℕ) (m : ℕ) (hm : m + 7 ≤ 32 * 4 ^ a) (i : ℕ)
    (hi : 12 * 2 ^ a - 2 ≤ i) : window106^[m] (pairLattice {0}) i = 0 :=
  window106_iterate_pair_eq_zero_of_le a m i hm (by omega)

private theorem evolve_base (a : ℕ) :
    window106^[32 * 4 ^ a - 32] (pairLattice {0} + windowShift (12 * 2 ^ a) (pairLattice {0})) =
      blockLattice 12 {0, 1} (Finset.range (2 ^ a)) +
        windowShift (12 * 2 ^ a) (blockLattice 12 {0, 1} (Finset.range (2 ^ a))) := by
  have hp : 0 < 2 ^ a := Nat.two_pow_pos a
  have hX : 0 < 4 ^ a := by positivity
  rw [window106_iterate_add_windowShift (by omega) _ _ _
    (fun m hm i hi => orbit_zero_seam a m (by omega) i hi), orbit_snapshot]

private theorem evolve_hit (a : ℕ) :
    window106^[32 * 4 ^ a - 32] (window106 (pairLattice {0}) +
        windowShift (12 * 2 ^ a) (pairLattice {0})) =
      blockLattice 12 {0, 1, 2} (Finset.range (2 ^ a)) +
        windowShift (12 * 2 ^ a) (blockLattice 12 {0, 1} (Finset.range (2 ^ a))) := by
  have hp : 0 < 2 ^ a := Nat.two_pow_pos a
  have hX : 0 < 4 ^ a := by positivity
  rw [window106_iterate_add_windowShift (by omega) _ _ _
    (fun m hm i hi => by
      rw [← Function.iterate_succ_apply]
      exact orbit_zero_seam a (m + 1) (by omega) i hi),
    ← Function.iterate_succ_apply, Function.iterate_succ_apply', orbit_snapshot,
    window106_blockLattice (by norm_num) (by decide)]
  rw [show blockStep 12 {0, 1} = {0, 1, 2} from by decide]

/-- The number whose base-two digits are the pattern `p` repeated at the cells `12 * x`,
`x < k`. -/
private def snapNat (p k : ℕ) : ℕ := (List.range k).foldl (fun acc x => acc + (p <<< (12 * x))) 0

/-- The hit window after the pairs have separated, as a number: `k` pieces `{0, 1, 2}` then `k`
pairs. -/
private def hitNat (k : ℕ) : ℕ := snapNat 7 k + (snapNat 3 k <<< (12 * k))

/-- The window without the hit after the pairs have separated, as a number: `2 * k` pairs. -/
private def baseNat (k : ℕ) : ℕ := snapNat 3 k + (snapNat 3 k <<< (12 * k))

/-- The hit window at the snapshot: pieces `{0, 1, 2}` in the blocks below `P` and pairs above. -/
private def hitWin (P : ℕ) : ℕ → ZMod 2 :=
  blockLattice 12 {0, 1, 2} (Finset.range P) +
    windowShift (12 * P) (blockLattice 12 {0, 1} (Finset.range P))

/-- The window without the hit at the snapshot: pairs in the blocks below `2 * P`. -/
private def baseWin (P : ℕ) : ℕ → ZMod 2 :=
  blockLattice 12 {0, 1} (Finset.range P) +
    windowShift (12 * P) (blockLattice 12 {0, 1} (Finset.range P))

private theorem core_small (P : ℕ) (hP : P = 1 ∨ P = 2 ∨ P = 4) :
    window106^[36] (hitWin P) (12 * P + 6) ≠ window106^[36] (baseWin P) (12 * P + 6) := by
  have h : (∀ i < 12 * P + 7, hitWin P i = winOfNat (hitNat P) i) ∧
      (∀ i < 12 * P + 7, baseWin P i = winOfNat (baseNat P) i) ∧
      winOfNat (stepNat^[36] (hitNat P)) (12 * P + 6) ≠
        winOfNat (stepNat^[36] (baseNat P)) (12 * P + 6) := by
    rcases hP with rfl | rfl | rfl <;> decide +kernel
  obtain ⟨h1, h2, h3⟩ := h
  rw [window106_iterate_congr (hitWin P) (winOfNat (hitNat P)) 36 _
      (fun i _ hi => h1 i (by omega)),
    window106_iterate_congr (baseWin P) (winOfNat (baseNat P)) 36 _
      (fun i _ hi => h2 i (by omega)),
    iterate_winOfNat, iterate_winOfNat]
  exact h3

private theorem ref_table : ∀ i < 103, 30 ≤ i →
    (winOfNat (hitNat 8) i =
      if i < 96 then (if i % 12 ≤ 2 then 1 else 0) else (if i % 12 ≤ 1 then 1 else 0)) ∧
    winOfNat (baseNat 8) i = if i % 12 ≤ 1 then 1 else 0 := by
  decide +kernel

private theorem ref_values :
    winOfNat (stepNat^[36] (hitNat 8)) 102 ≠ winOfNat (stepNat^[36] (baseNat 8)) 102 := by
  decide +kernel

private theorem core_large (P : ℕ) (hP : 8 ≤ P) :
    window106^[36] (hitWin P) (12 * P + 6) ≠ window106^[36] (baseWin P) (12 * P + 6) := by
  have hh : ∀ i, 12 * P + 6 ≤ i + 2 * 36 → i ≤ 12 * P + 6 →
      hitWin P i = windowShift (12 * (P - 8)) (winOfNat (hitNat 8)) i := by
    intro i h1 h2
    obtain ⟨i', rfl⟩ : ∃ i', i = 12 * (P - 8) + i' := ⟨i - 12 * (P - 8), by omega⟩
    have t := (ref_table i' (by omega) (by omega)).1
    simp only [hitWin, windowShift, Pi.add_apply, blockLattice, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_range]
    rw [ite_eq_left (by omega : 12 * (P - 8) ≤ 12 * (P - 8) + i'), Nat.add_sub_cancel_left, t]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hb : ∀ i, 12 * P + 6 ≤ i + 2 * 36 → i ≤ 12 * P + 6 →
      baseWin P i = windowShift (12 * (P - 8)) (winOfNat (baseNat 8)) i := by
    intro i h1 h2
    obtain ⟨i', rfl⟩ : ∃ i', i = 12 * (P - 8) + i' := ⟨i - 12 * (P - 8), by omega⟩
    have t := (ref_table i' (by omega) (by omega)).2
    simp only [baseWin, windowShift, Pi.add_apply, blockLattice, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_range]
    rw [ite_eq_left (by omega : 12 * (P - 8) ≤ 12 * (P - 8) + i'), Nat.add_sub_cancel_left, t]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [window106_iterate_congr _ _ 36 _ hh, window106_iterate_congr _ _ 36 _ hb,
    window106_iterate_windowShift, window106_iterate_windowShift]
  simp only [windowShift]
  rw [ite_eq_left (by omega), ite_eq_left (by omega), show 12 * P + 6 - 12 * (P - 8) = 102 by omega,
    iterate_winOfNat, iterate_winOfNat]
  exact ref_values

private theorem core (a : ℕ) :
    window106^[36] (hitWin (2 ^ a)) (12 * 2 ^ a + 6) ≠
      window106^[36] (baseWin (2 ^ a)) (12 * 2 ^ a + 6) := by
  by_cases ha : a < 3
  · apply core_small
    interval_cases a <;> simp
  · apply core_large
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The hit is seen at the far pair**: on the renormalized pair lattice `{0, 2 ^ a}`, the hit
at cell `2` is seen at level step `8 * 4 ^ a + 1`, at the sampled cell
`renormCell (6 * 2 ^ a + 3)`. -/
theorem window106_seen_hit_far (a : ℕ) :
    window106^[4 * (8 * 4 ^ a + 1)] (renorm (pairLattice {0, 2 ^ a}) + Pi.single 2 1)
        (renormCell (6 * 2 ^ a + 3)) ≠
      window106^[4 * (8 * 4 ^ a + 1)] (renorm (pairLattice {0, 2 ^ a}))
        (renormCell (6 * 2 ^ a + 3)) := by
  have hX : 0 < 4 ^ a := by positivity
  have hc : renormCell (6 * 2 ^ a + 3) = 12 * 2 ^ a + 6 := by
    have h3 : ¬ (6 * 2 ^ a + 3) % 3 = 1 := by omega
    unfold renormCell
    rw [ite_eq_right h3]
    ring
  have he : 4 * (8 * 4 ^ a + 1) = 36 + (32 * 4 ^ a - 32) := by omega
  rw [hc, he, renorm_pairLattice_two_add_single, renorm_pairLattice_two,
    Function.iterate_add_apply, Function.iterate_add_apply, evolve_hit, evolve_base]
  exact core a

/-- **The hit at the lone pair is unseen at every level step**: the pair with a hit at cell `2`,
and without it, read at the sampled cells after `4 * k` steps, agree. -/
theorem window106_unseen_hit_pair (k j : ℕ) :
    window106^[4 * k] (pairLattice {0} + Pi.single 2 1) (renormCell j) =
      window106^[4 * k] (pairLattice {0}) (renormCell j) := by
  have h := window106_iterate_renorm_renormCell (window106^[k] (pairLattice {0}))
    (r := 1) (by norm_num) j
  rw [Function.iterate_one] at h
  rw [pairLattice_add_single, ← Function.iterate_succ_apply, Function.iterate_succ_apply',
    (orbit_joint k).2, h, renorm_renormCell]

private theorem quadDigits_pow (a : ℕ) : quadDigits (2 ^ a) = 4 ^ a := by
  induction a with
  | zero => simpa [quadDigits_zero] using quadDigits_double_succ 0
  | succ a ih => rw [pow_succ', quadDigits_double, ih, pow_succ']

/-- **The level reading of the hit is not local**: the staying window `pairLattice {0, 2 ^ a}`
agrees, once renormalized, with the renormalized lone pair on every cell below `12 * 2 ^ a`, and
the hit at cell `2` of the first is seen at level step `8 * 4 ^ a + 1` at the sampled cell
`renormCell (6 * 2 ^ a + 3)`. -/
theorem window106_sight_not_local (a : ℕ) :
    Rule106Stays (pairLattice {0, 2 ^ a}) ∧
      (∀ i < 12 * 2 ^ a, renorm (pairLattice {0, 2 ^ a}) i = renorm (pairLattice {0}) i) ∧
      window106^[4 * (8 * 4 ^ a + 1)] (renorm (pairLattice {0, 2 ^ a}) + Pi.single 2 1)
          (renormCell (6 * 2 ^ a + 3)) ≠
        window106^[4 * (8 * 4 ^ a + 1)] (renorm (pairLattice {0, 2 ^ a}))
          (renormCell (6 * 2 ^ a + 3)) := by
  refine ⟨?_, ?_, window106_seen_hit_far a⟩
  · have h := iterate_pairLattice rule106Renorm rule106Step24 (2 ^ a * 1)
    have s1 : submasks 1 = {0, 1} := by simpa [submasks_zero] using submasks_double_succ 0
    rw [submasks_pow, mul_one, quadDigits_pow, s1] at h
    have e : (({0, 1} : Finset ℕ).image (2 ^ a * ·)) = {0, 2 ^ a} := by simp
    rw [e] at h
    rw [← h]
    intro n
    rw [← Function.iterate_add_apply]
    exact rule106Stays_pair _
  · intro i hi
    have hp : 0 < 2 ^ a := Nat.two_pow_pos a
    rw [renorm_pairLattice_two, renorm_pair]
    simp only [Pi.add_apply, windowShift]
    have hn : ¬ 12 * 2 ^ a ≤ i := by omega
    simp only [hn, ite_false, add_zero]

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_pair_eq_zero_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_pair_eq_zero_of_le

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_pair_eq_zero_of_le_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_pair_eq_zero_of_le_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_pair_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_pair_sharp

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_add_windowShift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_add_windowShift

set_option linter.style.longLine false in
/-- info: 'ECA.window106_seen_hit_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_seen_hit_far

set_option linter.style.longLine false in
/-- info: 'ECA.window106_unseen_hit_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_unseen_hit_pair

set_option linter.style.longLine false in
/-- info: 'ECA.window106_sight_not_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_sight_not_local

end ECA
