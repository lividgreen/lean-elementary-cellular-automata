module

public import ECA.Rule106
import all ECA.Rule106
import all ECA.EdgeWindow
import all ECA.EdgeColumns

/-!
# Rules `106` and `120` reproduce every state on the orbit of the pair
([RuleSpace] §5)

Write `p n` for the `n`-th iterate of rule `106` at the pair `11`. The block superposition of rule
`106`'s window map reproduces the pair after `24 * g s` steps, and the same lattice of pairs, read
`n` steps further, is a lattice of copies of the window of `p n`, as long as the blocks are wide
enough to keep neighbouring windows apart. So every state on the orbit of the pair is reproduced,
not only the pattern of cells `0`, `1` and `3`, and rule `120`, the mirror of rule `106`, reproduces
every state on the orbit of the reflected pair.

## Main results

* `window106_iterate_eq_zero` — the width bound: `k` steps of rule `106`'s window map clear every
  cell from `m + 2 * k` on when the window is clear from `m` on.
* `copies_of_fullWindow_blockLattice` — a state whose full window is a lattice of blocks of a
  piece, the piece being the full window of a nonzero state `q` with room to spare, is that many
  copies of `q`.
* `reproduces_wolfram106_orbit` / `reproduces_wolfram120_orbit` — every state on the orbit of the
  pair under rule `106`, and of the reflected pair under rule `120`, is reproduced.
* `copies_window106_orbit_nonvacuous` — the statement at the third iterate of the pair: its full
  window is the cells `0` to `3`, and the full window of its `27`-th iterate the cells `0` to `3`
  and `6` to `9`, two copies at gap `2`.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The width bound -/

/-- **The width bound**: if a window is clear from cell `m` on, then `k` steps of rule `106`'s
window map leave it clear from cell `m + 2 * k` on, since cell `j` of the image reads cells
`j - 2` to `j`. -/
theorem window106_iterate_eq_zero {w : ℕ → ZMod 2} {m : ℕ} (hw : ∀ j, m ≤ j → w j = 0) (k : ℕ) :
    ∀ j, m + 2 * k ≤ j → window106^[k] w j = 0 := by
  induction k generalizing w m with
  | zero => intro j hj; exact hw j (by omega)
  | succ k ih =>
    intro j hj
    rw [Function.iterate_succ_apply]
    refine ih (w := window106 w) (m := m + 2) (fun i hi => ?_) j (by omega)
    have h0 : w i = 0 := hw i (by omega)
    have h2 : w (i - 2) = 0 := hw (i - 2) (by omega)
    unfold window106
    rw [h0, ite_eq_left (by omega : 2 ≤ i), h2]
    simp

/-! ## Copies from a lattice of blocks -/

private theorem blockLattice_singleton {L : ℕ} {S : Finset ℕ} (hS : ∀ r ∈ S, r < L) (n : ℕ) :
    blockLattice L S {0} n = if n ∈ S then 1 else 0 := by
  unfold blockLattice
  apply if_congr _ rfl rfl
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    have hL : 0 < L := by
      have := hS _ h1
      omega
    have h3 : n < L := by
      by_contra hc
      have := Nat.div_pos (not_lt.1 hc) hL
      omega
    rwa [Nat.mod_eq_of_lt h3] at h1
  · intro h
    have h3 := hS _ h
    exact ⟨by rwa [Nat.mod_eq_of_lt h3], Nat.div_eq_of_lt h3⟩

private theorem sum_indicator_set (m B : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r < m) (i : ℤ) :
    (∑ j ∈ Finset.range B,
      if 0 ≤ i - (m : ℤ) * j ∧ (i - (m : ℤ) * j).toNat ∈ S then (1 : ZMod 2) else 0) =
    if 0 ≤ i ∧ i.toNat % m ∈ S ∧ i.toNat / m < B then 1 else 0 := by
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    simp only [Int.toNat_natCast, hi, true_and]
    have key : ∀ j : ℕ, (0 ≤ (n : ℤ) - (m : ℤ) * j ∧ ((n : ℤ) - (m : ℤ) * j).toNat ∈ S) →
        n / m = j ∧ n % m ∈ S := by
      rintro j ⟨h0, hmem⟩
      have hr := hS _ hmem
      have hmj : ((m * j : ℕ) : ℤ) = (m : ℤ) * j := by push_cast; rfl
      have := div_mod_of_eq (m := m) (j := j) (k := ((n : ℤ) - (m : ℤ) * j).toNat) (n := n) hr
        (by omega)
      exact ⟨this.1, by rw [this.2]; exact hmem⟩
    by_cases hc : n % m ∈ S ∧ n / m < B
    · rw [ite_eq_left hc, Finset.sum_eq_single_of_mem (n / m) (Finset.mem_range.2 hc.2)]
      · rw [ite_eq_left]
        have hd := Nat.div_add_mod n m
        have hmj : ((m * (n / m) : ℕ) : ℤ) = (m : ℤ) * ((n / m : ℕ) : ℤ) := by push_cast; rfl
        have hlt := hS _ hc.1
        have e : (n : ℤ) - (m : ℤ) * ((n / m : ℕ) : ℤ) = ((n % m : ℕ) : ℤ) := by omega
        rw [e, Int.toNat_natCast]
        exact ⟨by omega, hc.1⟩
      · intro j _ hj
        rw [ite_eq_right]
        intro h
        exact hj (key j h).1.symm
    · rw [ite_eq_right hc]
      apply Finset.sum_eq_zero
      intro j hj
      rw [ite_eq_right]
      intro h
      obtain ⟨h1, h2⟩ := key j h
      exact hc ⟨h2, by rw [h1]; exact Finset.mem_range.1 hj⟩
  · rw [ite_eq_right (fun h => hi h.1)]
    apply Finset.sum_eq_zero
    intro j _
    have : 0 ≤ (m : ℤ) * j := by positivity
    rw [ite_eq_right]
    omega

/-- **Copies from a lattice of blocks**: let `q` be a nonzero state whose full window is the piece
`S` in the block `0` of width `L`, with every cell of `S` below `L`; a state `u` whose full window
is the piece `S` in each of the blocks `0` to `B - 1` is `B` copies of `q` at gap `G`, as long as
the diameter of `q` and `G` fit in `L`. -/
theorem copies_of_fullWindow_blockLattice {q u : FiniteConfiguration} (hq : q ≠ 0) (hu : u ≠ 0)
    {L B G : ℕ} {S : Finset ℕ} (hSL : ∀ r ∈ S, r < L) (hL : q.diam + G ≤ L)
    (hqS : q.fullWindow = blockLattice L S {0})
    (huS : u.fullWindow = blockLattice L S (Finset.range B)) : Copies q u B G := by
  have hq_apply : ∀ x : ℤ, q x =
      if 0 ≤ x - q.leftEnd ∧ (x - q.leftEnd).toNat ∈ S then 1 else 0 := by
    intro x
    by_cases hx : x < q.leftEnd
    · rw [eq_zero_of_lt_leftEnd hq hx, ite_eq_right]
      omega
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x - q.leftEnd by omega)
      have hxn : x = q.leftEnd + n := by omega
      have h1 : q x = q.fullWindow n := by rw [hxn]; rfl
      rw [h1, hqS, blockLattice_singleton hSL, hn, Int.toNat_natCast]
      simp only [Int.natCast_nonneg, true_and]
  refine ⟨fun j => u.leftEnd - q.leftEnd + ((L * j : ℕ) : ℤ), ?_, ?_⟩
  · intro j _
    have : L * (j + 1) = L * j + L := by ring
    push_cast [this]
    omega
  · ext x
    rw [Finsupp.finsetSum_apply]
    simp only [translate_apply', hq_apply]
    have e : ∀ j : ℕ, x - (u.leftEnd - q.leftEnd + ((L * j : ℕ) : ℤ)) - q.leftEnd =
        (x - u.leftEnd) - (L : ℤ) * j := by
      intro j
      push_cast
      ring
    simp only [e]
    rw [sum_indicator_set L B S hSL (x - u.leftEnd)]
    by_cases hx : x < u.leftEnd
    · rw [eq_zero_of_lt_leftEnd hu hx, ite_eq_right]
      omega
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x - u.leftEnd by omega)
      have hxn : x = u.leftEnd + n := by omega
      have h1 : u x = u.fullWindow n := by rw [hxn]; rfl
      rw [h1, huS, hn]
      unfold blockLattice
      simp only [Int.toNat_natCast, Int.natCast_nonneg, true_and, Finset.mem_range]

/-! ## The pair and its orbit -/

/-- The pair `11` at cells `0` and `1`. -/
private noncomputable abbrev pairCfg : FiniteConfiguration :=
  Finsupp.single 0 1 + Finsupp.single 1 1

private theorem pairCfg_apply (x : ℤ) : pairCfg x = if x = 0 ∨ x = 1 then 1 else 0 := by
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> first | omega | decide

private theorem pairCfg_ne_zero : pairCfg ≠ 0 := by
  intro h
  have := pairCfg_apply 0
  rw [h] at this
  simp at this

private theorem pairCfg_support : pairCfg.support = {0, 1} := by
  ext x
  rw [Finsupp.mem_support_iff, pairCfg_apply]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  split_ifs with h <;> simp [h]

private theorem pairCfg_leftEnd : pairCfg.leftEnd = 0 := by
  have hne : pairCfg.support.Nonempty := by
    rw [pairCfg_support]; exact ⟨0, by simp⟩
  rw [leftEnd_eq hne]
  apply le_antisymm
  · exact Finset.min'_le _ _ (by rw [pairCfg_support]; simp)
  · exact Finset.le_min' _ _ _ (fun y hy => by
      rw [pairCfg_support] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      omega)

private theorem pairCfg_fullWindow : pairCfg.fullWindow = pairLattice {0} := by
  funext j
  simp only [fullWindow, pairCfg_leftEnd, zero_add, pairCfg_apply, pairLattice,
    Finset.mem_singleton]
  split_ifs <;> first | rfl | omega

/-- A state whose full window is clear from cell `m` on has diameter at most `m`. -/
private theorem diam_le_of_fullWindow {q : FiniteConfiguration} (hq : q ≠ 0) {m : ℕ}
    (h : ∀ j, m ≤ j → q.fullWindow j = 0) : q.diam ≤ m := by
  have hne : q.support.Nonempty := Finsupp.support_nonempty_iff.mpr hq
  rw [diam_eq' hne]
  by_contra hc
  have hmin := Finset.min'_le_max' q.support hne
  have hmem := Finset.max'_mem q.support hne
  have hz := h (q.support.max' hne - q.support.min' hne).toNat (by omega)
  simp only [fullWindow, leftEnd_eq hne] at hz
  rw [show q.support.min' hne + ((q.support.max' hne - q.support.min' hne).toNat : ℤ) =
    q.support.max' hne by omega] at hz
  exact (Finsupp.mem_support_iff.1 hmem) hz

private theorem pairLattice_zero_eq_block {L : ℕ} (hL : 2 ≤ L) :
    pairLattice {0} = blockLattice L {0, 1} {0} := by
  funext i
  unfold pairLattice blockLattice
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply if_congr _ rfl rfl
  rcases Nat.lt_or_ge i L with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
    omega
  · have := Nat.div_pos h (by omega : 0 < L)
    constructor <;> intro hh <;> omega

/-- The lattice of pairs at the multiples of `A`, as a lattice of blocks of width `6 * A`. -/
private theorem pairLattice_image_eq_block (A B : ℕ) (hA : 0 < A) :
    pairLattice ((Finset.range B).image (A * ·)) =
      blockLattice (6 * A) {0, 1} (Finset.range B) := by
  funext n
  have hmod : n % (6 * A) = n % 6 + 6 * (n / 6 % A) := Nat.mod_mul
  have hdiv : n / (6 * A) = n / 6 / A := (Nat.div_div_eq_div_mul n 6 A).symm
  have hmem : n / 6 ∈ (Finset.range B).image (A * ·) ↔ n / 6 % A = 0 ∧ n / 6 / A < B := by
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨y, hy, hyn⟩
      rw [← hyn]
      exact ⟨Nat.mul_mod_right A y, by rw [Nat.mul_div_cancel_left y hA]; exact hy⟩
    · rintro ⟨h1, h2⟩
      exact ⟨n / 6 / A, h2, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h1)⟩
  unfold pairLattice blockLattice
  rw [hmod, hdiv]
  apply if_congr _ rfl rfl
  rw [hmem]
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range]
  have := Nat.mod_lt n (show 0 < 6 by omega)
  generalize n / 6 % A = q
  generalize n / 6 / A = r
  generalize n % 6 = t at *
  constructor
  · rintro ⟨h1, h2, h3⟩
    subst h2
    exact ⟨by omega, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨?_, ?_, h3⟩ <;> omega

/-- The pieces of the orbit of the pair in blocks of width `L`: the first `n` stages keep their
last two cells clear, and the stage `k` lies below cell `2 * k + 2`. -/
private theorem orbit_pieces {L : ℕ} (n : ℕ) (hL : 2 * n + 4 ≤ L) :
    ∀ k ≤ n, window106^[k] (blockLattice L {0, 1} {0}) =
        blockLattice L ((blockStep L)^[k] {0, 1}) {0} ∧
      ∀ r ∈ (blockStep L)^[k] ({0, 1} : Finset ℕ), r < 2 * k + 2 := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [Function.iterate_zero, id_eq, Finset.mem_insert, Finset.mem_singleton] at hr
    omega
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hS : ∀ r ∈ (blockStep L)^[k] ({0, 1} : Finset ℕ), r + 2 < L := fun r hr => by
      have := h2 r hr
      omega
    have e : window106^[k + 1] (blockLattice L {0, 1} {0}) =
        blockLattice L (blockStep L ((blockStep L)^[k] {0, 1})) {0} := by
      rw [Function.iterate_succ_apply', h1, window106_blockLattice (by omega) hS]
    have eS : (blockStep L)^[k + 1] ({0, 1} : Finset ℕ) =
        blockStep L ((blockStep L)^[k] {0, 1}) := Function.iterate_succ_apply' _ _ _
    rw [eS]
    refine ⟨e, fun r hr => ?_⟩
    by_contra hlt
    have hrL : r < L := Finset.mem_range.1 (Finset.mem_filter.1 hr).1
    have hz := window106_iterate_eq_zero (w := blockLattice L {0, 1} {0}) (m := 2)
      (fun j hj => by
        unfold blockLattice
        rw [ite_eq_right]
        simp only [Finset.mem_singleton, Finset.mem_insert, not_and]
        intro h
        rcases Nat.lt_or_ge j L with h' | h'
        · rw [Nat.mod_eq_of_lt h'] at h
          omega
        · have := Nat.div_pos h' (by omega : 0 < L)
          omega) (k + 1) r (by omega)
    rw [e] at hz
    unfold blockLattice at hz
    rw [Nat.mod_eq_of_lt hrL, Nat.div_eq_of_lt hrL,
      ite_eq_left ⟨hr, Finset.mem_singleton_self 0⟩] at hz
    exact absurd hz (by decide)

/-! ## Rule `106` -/

/-- **Every state on the orbit of the pair is reproduced**: rule `106` reproduces the `n`-th
iterate of the pair `11`, for every `n`. -/
theorem reproduces_wolfram106_orbit (hq : wolframRule 106 0 0 0 = 0) (n : ℕ) :
    Reproduces (finRule (wolframRule 106) hq)
      ((finRule (wolframRule 106) hq)^[n] (Finsupp.single 0 1 + Finsupp.single 1 1)) := by
  obtain ⟨hne, hfw⟩ := iterate_fullWindow hq pairCfg_ne_zero n
  refine ⟨hne, fun N G => ?_⟩
  have hpow : ∀ x : ℕ, x < 2 ^ x := fun x => Nat.lt_two_pow_self
  have hpos : ∀ x : ℕ, 0 < 2 ^ x := fun x => Nat.two_pow_pos x
  set a := G + 2 * n + 4 with ha
  have hLn : 2 * n + 4 ≤ 6 * 2 ^ a := by have := hpow a; omega
  have hz : ∀ j, 2 + 2 * n ≤ j →
      ((finRule (wolframRule 106) hq)^[n] pairCfg).fullWindow j = 0 := by
    intro j hj
    rw [hfw, pairCfg_fullWindow]
    exact window106_iterate_eq_zero (w := pairLattice {0}) (m := 2)
      (fun i hi => by
        unfold pairLattice
        rw [ite_eq_right]
        simp only [Finset.mem_singleton, not_and]
        intro _
        omega) n j hj
  have hdiam := diam_le_of_fullWindow hne hz
  have hLd : ((finRule (wolframRule 106) hq)^[n] pairCfg).diam + G ≤ 6 * 2 ^ a := by
    have := hpow a
    omega
  obtain ⟨hpieces, hbound⟩ := orbit_pieces (L := 6 * 2 ^ a) n hLn n le_rfl
  have hS : ∀ k < n, ∀ r ∈ (blockStep (6 * 2 ^ a))^[k] ({0, 1} : Finset ℕ), r + 2 < 6 * 2 ^ a :=
    fun k hk r hr => by
      have := (orbit_pieces (L := 6 * 2 ^ a) n hLn k hk.le).2 r hr
      omega
  have hSL : ∀ r ∈ (blockStep (6 * 2 ^ a))^[n] ({0, 1} : Finset ℕ), r < 6 * 2 ^ a :=
    fun r hr => by
      have := hbound r hr
      omega
  set g := quadDigits ((2 ^ N - 1) * 2 ^ a) with hg
  have hB : N ≤ 2 ^ N := (hpow N).le
  refine ⟨24 * g, 2 ^ N, hB, ?_⟩
  rw [← Function.iterate_add_apply]
  obtain ⟨hune, hfu⟩ := iterate_fullWindow hq pairCfg_ne_zero (24 * g + n)
  refine copies_of_fullWindow_blockLattice hne hune hSL hLd ?_ ?_
  · rw [hfw, pairCfg_fullWindow,
      pairLattice_zero_eq_block (L := 6 * 2 ^ a) (by have := hpos a; omega)]
    exact hpieces
  · rw [hfu, pairCfg_fullWindow, add_comm, Function.iterate_add_apply,
      iterate_pairLattice rule106Renorm rule106Step24, mul_comm, submasks_pow, submasks_mersenne,
      pairLattice_image_eq_block _ _ (hpos a),
      window106_iterate_blockLattice (L := 6 * 2 ^ a) (by have := hpos a; omega) _ _ n hS]

/-! ## Rule `120` -/

/-- **Every state on the orbit of the reflected pair is reproduced by rule `120`**: the pair
reflected is the pair at cells `-1` and `0`, and rule `120` is the mirror of rule `106`. -/
theorem reproduces_wolfram120_orbit (hq : wolframRule 120 0 0 0 = 0) (n : ℕ) :
    Reproduces (finRule (wolframRule 120) hq)
      ((finRule (wolframRule 120) hq)^[n] (Finsupp.single 0 1 + Finsupp.single (-1) 1)) := by
  have hq106 : wolframRule 106 0 0 0 = 0 := by decide
  have hm : mirrorRule (wolframRule 106) = wolframRule 120 := by
    funext a b c
    revert a b c
    decide
  have e : FiniteConfiguration.reflect (Finsupp.single 0 1 + Finsupp.single 1 1) =
      Finsupp.single 0 1 + Finsupp.single (-1) 1 := by
    simp [FiniteConfiguration.reflect, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  have key : ∀ g : LocalRule, mirrorRule (wolframRule 106) = g → ∀ hg : g 0 0 0 = 0,
      Reproduces (finRule g hg) ((finRule g hg)^[n]
        (FiniteConfiguration.reflect (Finsupp.single 0 1 + Finsupp.single 1 1))) := by
    rintro g rfl hg
    rw [iterate_mirror_reflect' (wolframRule 106) hq106]
    exact reproducesReflect _ hq106 _ (reproduces_wolfram106_orbit hq106 n)
  have := key _ hm hq
  rwa [e] at this

/-! ## The statement at the third iterate -/

private theorem pairLattice_zero_eq_bits : pairLattice {0} = winOfNat 3 := by
  funext j
  by_cases hj : j < 12
  · interval_cases j <;> decide
  · rw [winOfNat_apply_of_lt (L := 2) (by norm_num) (by omega)]
    simp only [pairLattice, Finset.mem_singleton]
    exact ite_eq_right (fun h => by omega)

private theorem stepNat_iterate_3 : stepNat^[3] 3 = 15 := by decide +kernel

private theorem stepNat_iterate_27 : stepNat^[27] 3 = 975 := by decide +kernel

/-- **The statement at the third iterate of the pair**: the full window of the third iterate of
rule `106` from the pair `11` is the cells `0`, `1`, `2` and `3`, the full window of its
twenty-seventh iterate is the cells `0` to `3` and `6` to `9`, and the twenty-seventh iterate is two
copies of the third at gap `2`. -/
theorem copies_window106_orbit_nonvacuous (hq : wolframRule 106 0 0 0 = 0) :
    ((finRule (wolframRule 106) hq)^[3]
        (Finsupp.single 0 1 + Finsupp.single 1 1) ≠ 0 ∧
      ∀ j : ℕ, ((finRule (wolframRule 106) hq)^[3]
        (Finsupp.single 0 1 + Finsupp.single 1 1)).fullWindow j =
        if j ∈ ({0, 1, 2, 3} : Finset ℕ) then 1 else 0) ∧
    ((finRule (wolframRule 106) hq)^[27]
        (Finsupp.single 0 1 + Finsupp.single 1 1) ≠ 0 ∧
      ∀ j : ℕ, ((finRule (wolframRule 106) hq)^[27]
        (Finsupp.single 0 1 + Finsupp.single 1 1)).fullWindow j =
        if j ∈ ({0, 1, 2, 3, 6, 7, 8, 9} : Finset ℕ) then 1 else 0) ∧
    Copies ((finRule (wolframRule 106) hq)^[3] (Finsupp.single 0 1 + Finsupp.single 1 1))
      ((finRule (wolframRule 106) hq)^[27] (Finsupp.single 0 1 + Finsupp.single 1 1)) 2 2 := by
  obtain ⟨hne3, hfw3⟩ := iterate_fullWindow hq pairCfg_ne_zero 3
  obtain ⟨hne27, hfw27⟩ := iterate_fullWindow hq pairCfg_ne_zero 27
  rw [pairCfg_fullWindow, pairLattice_zero_eq_bits, iterate_winOfNat, stepNat_iterate_3] at hfw3
  rw [pairCfg_fullWindow, pairLattice_zero_eq_bits, iterate_winOfNat, stepNat_iterate_27] at hfw27
  have c3 : ∀ j : ℕ, ((finRule (wolframRule 106) hq)^[3] pairCfg).fullWindow j =
      if j ∈ ({0, 1, 2, 3} : Finset ℕ) then 1 else 0 := by
    intro j
    rw [hfw3]
    by_cases hj : j < 4
    · interval_cases j <;> decide
    · rw [winOfNat_apply_of_lt (L := 4) (by norm_num) (by omega)]
      have hn : j ∉ ({0, 1, 2, 3} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (ite_eq_right hn).symm
  have c27 : ∀ j : ℕ, ((finRule (wolframRule 106) hq)^[27] pairCfg).fullWindow j =
      if j ∈ ({0, 1, 2, 3, 6, 7, 8, 9} : Finset ℕ) then 1 else 0 := by
    intro j
    rw [hfw27]
    by_cases hj : j < 10
    · interval_cases j <;> decide
    · rw [winOfNat_apply_of_lt (L := 10) (by norm_num) (by omega)]
      have hn : j ∉ ({0, 1, 2, 3, 6, 7, 8, 9} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (ite_eq_right hn).symm
  refine ⟨⟨hne3, c3⟩, ⟨hne27, c27⟩, ?_⟩
  have hdiam : ((finRule (wolframRule 106) hq)^[3] pairCfg).diam ≤ 4 :=
    diam_le_of_fullWindow hne3 (fun j hj => by
      rw [c3, ite_eq_right]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega)
  refine copies_of_fullWindow_blockLattice (S := {0, 1, 2, 3}) (L := 6) hne3 hne27
    (fun r hr => by simp only [Finset.mem_insert, Finset.mem_singleton] at hr; omega)
    (by omega) ?_ ?_
  · funext j
    rw [c3]
    unfold blockLattice
    simp only [Finset.mem_insert, Finset.mem_singleton]
    apply if_congr _ rfl rfl
    omega
  · funext j
    rw [c27]
    unfold blockLattice
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range]
    apply if_congr _ rfl rfl
    omega

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_eq_zero

set_option linter.style.longLine false in
/-- info: 'ECA.copies_of_fullWindow_blockLattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.copies_of_fullWindow_blockLattice

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram106_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram106_orbit

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram120_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram120_orbit

set_option linter.style.longLine false in
/-- info: 'ECA.copies_window106_orbit_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.copies_window106_orbit_nonvacuous
