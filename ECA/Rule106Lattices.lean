module

public import ECA.Rule106Splice
import all ECA.Rule106
import all ECA.Rule106Sight
import all ECA.Rule106Shadow
import all ECA.Rule106Splice

/-!
# Rule `106` at the lattices of pairs at a common spacing
([RuleSpace] §5)

Rule `106` acts on the window of a state, read from its leftmost set cell, by `window106`: cell
`j` of the image is `w j + w (j - 2) * w (j - 1)`. Write `C m` for the window with a pair `11` at
each of the cells `3 * y`, `y < m`. Four facts classify the lattices of pairs.

The chain `C m` of an odd number of pairs keeps the run condition at every step: its first two
steps are a run and then the pair with one set cell, and the pair with one set cell at the
residue `3` modulo `6` has, at every step, the cells below the lone cell of the pair's orbit, the
lone cell complemented, and the cells past it of the orbit two steps ahead. The run condition
across the lone cell is two local conditions on the window of width eleven of the pair's orbit,
which the finite language of those windows decides.

The cell map of the renormalization carries a shadow: if a staying window agrees with the pair's
orbit at every step from a cell `B` on, its renormalization agrees with it at every step from the
cell `2 * B + 6` on. Each step splits as `4 * u + r`, the first part commuting with the
renormalization on both windows and the last `r < 4` steps reading `2 * r` cells to the left.

The renormalization of `C m` is the lattice of `m` pairs six cells apart, and six steps from the
lattice of `m` pairs six cells apart are `C (2 * m)`: the blocks of six steps interact, but a cell
after six steps reads the twelve cells to its left, so the image past the last pair depends on
the three last pairs alone. Hence `C (2 ^ j * m)` is `2 * (4 ^ j - 1)` steps from the `j`-fold
renormalization of `C m`.

So the lattice of `m = 2 ^ j * m'` pairs at the spacing `3 * 2 ^ k`, `m'` odd, is a number of
steps from the `(k + j)`-fold renormalization of `C m'`; that is the pair when `m' = 1`, which
rule `106` reproduces, and a state shadowed by the pair, wider than it, when `m' ≥ 3`, which it
does not. The lattice is reproduced exactly when `m` is a power of two.

## Main results

* `rule106Stays_pairChain` — the chain of an odd number of pairs keeps the run condition at every
  step.
* `window106_iterate_renorm_eq_of_shadow` — the renormalization of a staying window that agrees
  with the pair's orbit from a cell on agrees with it from twice that cell plus six on;
  `window106_iterate_renorm_eq_of_shadow_nonvacuous` meets it at the chain of three pairs.
* `renorm_pairChain` / `window106_iterate_six_pairLattice_range` — the renormalization of the
  chain of `m` pairs is the pair lattice of `{0, ..., m - 1}`, and six steps from that lattice are
  the chain of `2 * m` pairs.
* `window106_iterate_renorm_pow_pairChain` — the chain of `2 ^ j * m` pairs is
  `2 * (4 ^ j - 1)` steps from the `j`-fold renormalization of the chain of `m`.
* `pairChainAt` / `renorm_iterate_pairChain` / `pairChainAtCells` — the window with a pair at each
  cell `3 * 2 ^ k * y`, `y < m`, the `k`-fold renormalization of the chain, and the cells of the
  window as a state.
* `reproduces_wolfram106_pairChainAt_iff` — **the lattices classified**: the lattice of `m ≥ 1`
  pairs at the spacing `3 * 2 ^ k` is reproduced exactly when `m` is a power of two;
  `reproduces_wolfram106_pairChainAt_iff_nonvacuous` meets both sides, the lattice of four pairs
  at spacing `6` reproduced and the lattices of three pairs at spacing `6` and six pairs at
  spacing `3` not.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## Windows read as numbers -/

/-- A window clear from cell `L` on that agrees with the bits of `N` below it is the window of
`N`. -/
private theorem eq_winOfNat_of_bits (f : ℕ → ZMod 2) (N L : ℕ) (hN : N < 2 ^ L)
    (hlow : ∀ j < L, f j = if N.testBit j = true then 1 else 0)
    (hhigh : ∀ j, L ≤ j → f j = 0) : f = winOfNat N := by
  funext j
  by_cases hj : j < L
  · rw [hlow j hj]
    rfl
  · rw [hhigh j (by omega), winOfNat_apply_of_lt hN (by omega)]

/-! ## The renormalization of the chain, and six steps from the lattice -/

/-- **The renormalization of the chain of pairs** is the lattice of the pairs at the cells `6 * y`,
`y < m`: the cell map sends `3 * y` to `6 * y` and `3 * y + 1` to `6 * y + 1`. -/
theorem renorm_pairChain (m : ℕ) : renorm (pairChain m) = pairLattice (Finset.range m) := by
  funext i
  simp only [renorm, pairChain, pairLattice, Finset.mem_range]
  split_ifs <;> first | rfl | omega

private theorem pairLattice_range_three :
    pairLattice (Finset.range 3) = winOfNat 12483 := by
  refine eq_winOfNat_of_bits _ _ 14 (by norm_num) (fun j hj => ?_) (fun j hj => ?_)
  · interval_cases j <;> decide
  · simp only [pairLattice, Finset.mem_range]
    exact ite_eq_right (fun h => by omega)

private theorem pairChain_six :
    pairChain 6 = winOfNat (stepNat^[6] 12483) := by
  have h : stepNat^[6] 12483 = 112347 := by decide +kernel
  rw [h]
  refine eq_winOfNat_of_bits _ _ 17 (by norm_num) (fun j hj => ?_) (fun j hj => ?_)
  · interval_cases j <;> decide
  · simp only [pairChain]
    exact ite_eq_right (fun h => by omega)

private theorem window106_iterate_six_three :
    window106^[6] (pairLattice (Finset.range 3)) = pairChain 6 := by
  rw [pairLattice_range_three, iterate_winOfNat, pairChain_six]

private theorem window106_iterate_six_one :
    window106^[6] (pairLattice (Finset.range 1)) = pairChain 2 := by
  have e : pairLattice (Finset.range 1) = winOfNat 3 := by
    rw [← pairLattice_zero_eq_winOfNat]
    simp
  have h : pairChain 2 = winOfNat (stepNat^[6] 3) := by
    have h : stepNat^[6] 3 = 27 := by decide +kernel
    rw [h]
    refine eq_winOfNat_of_bits _ _ 5 (by norm_num) (fun j hj => ?_) (fun j hj => ?_)
    · interval_cases j <;> decide
    · simp only [pairChain]
      exact ite_eq_right (fun h => by omega)
  rw [e, iterate_winOfNat, h]

private theorem window106_iterate_six_two :
    window106^[6] (pairLattice (Finset.range 2)) = pairChain 4 := by
  have e : pairLattice (Finset.range 2) = winOfNat 195 := by
    refine eq_winOfNat_of_bits _ _ 8 (by norm_num) (fun j hj => ?_) (fun j hj => ?_)
    · interval_cases j <;> decide
    · simp only [pairLattice, Finset.mem_range]
      exact ite_eq_right (fun h => by omega)
  have h : pairChain 4 = winOfNat (stepNat^[6] 195) := by
    have h : stepNat^[6] 195 = 1755 := by decide +kernel
    rw [h]
    refine eq_winOfNat_of_bits _ _ 11 (by norm_num) (fun j hj => ?_) (fun j hj => ?_)
    · interval_cases j <;> decide
    · simp only [pairChain]
      exact ite_eq_right (fun h => by omega)
  rw [e, iterate_winOfNat, h]

/-- **Six steps from the pair lattice give the chain of twice the pairs**: the pairs at the cells
`6 * y`, `y < m`, become after six steps of rule `106`'s window map the pairs at the cells
`3 * y`, `y < 2 * m`. The blocks interact, but the image at a cell reads the twelve cells left of
it, so the cells right of the first `m - 1` pairs depend on the last three pairs alone, a
translate of the case of three pairs ([RuleSpace] §5). -/
theorem window106_iterate_six_pairLattice_range (m : ℕ) :
    window106^[6] (pairLattice (Finset.range m)) = pairChain (2 * m) := by
  induction m with
  | zero =>
    have h0 : pairLattice (Finset.range 0) = 0 := by
      funext i
      simp [pairLattice]
    have h1 : pairChain (2 * 0) = 0 := by
      funext i
      simp [pairChain]
    rw [h0, h1]
    have : ∀ n, window106^[n] (0 : ℕ → ZMod 2) = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        funext j
        simp [window106]
    exact this 6
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · exact window106_iterate_six_one
      · exact window106_iterate_six_two
    · funext j
      by_cases hj : j < 6 * m
      · have hagree : ∀ i < 6 * m, pairLattice (Finset.range (m + 1)) i =
            pairLattice (Finset.range m) i := by
          intro i hi
          simp only [pairLattice, Finset.mem_range]
          split_ifs <;> first | rfl | omega
        rw [window106_iterate_congr_lt hagree 6 j hj, ih]
        simp only [pairChain]
        split_ifs <;> first | rfl | omega
      · have hshift : window106^[6] (pairLattice (Finset.range (m + 1))) j =
            window106^[6] (windowShift (6 * (m - 2)) (pairLattice (Finset.range 3))) j := by
          apply window106_iterate_congr
          intro i h1 h2
          simp only [windowShift, pairLattice, Finset.mem_range]
          split_ifs <;> first | rfl | omega
        rw [hshift, window106_iterate_windowShift, window106_iterate_six_three]
        simp only [windowShift, pairChain]
        split_ifs <;> first | rfl | omega

/-- **The chain of `2 ^ j * m` pairs is a number of steps from the `j`-fold renormalization of the
chain of `m`**: when the chain of `m` pairs keeps the run condition, `2 * (4 ^ j - 1)` steps of
rule `106`'s window map from the `j`-fold renormalization of it give the chain of `2 ^ j * m` pairs.
At each scale the renormalization of a staying window commutes with four steps, so the previous
count of steps is multiplied by `4`, and the six steps from the lattice of pairs six cells apart add
six more ([RuleSpace] §5). -/
theorem window106_iterate_renorm_pow_pairChain (j m : ℕ) (hm : Rule106Stays (pairChain m)) :
    window106^[2 * (4 ^ j - 1)] (renorm^[j] (pairChain m)) = pairChain (2 ^ j * m) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs : Rule106Stays (renorm^[j] (pairChain m)) := (renorm_pow_window106_iterate hm j 0).1
    have h1 := (renorm_pow_window106_iterate hs 1 (2 * (4 ^ j - 1))).2
    simp only [pow_one, Function.iterate_one] at h1
    rw [ih, renorm_pairChain] at h1
    have hpos : 1 ≤ 4 ^ j := Nat.one_le_pow j 4 (by norm_num)
    have hcount : 2 * (4 ^ (j + 1) - 1) = 6 + 4 * (2 * (4 ^ j - 1)) := by
      rw [pow_succ]
      omega
    rw [hcount, Function.iterate_add_apply, Function.iterate_succ_apply' renorm j (pairChain m),
      h1, window106_iterate_six_pairLattice_range, pow_succ]
    congr 1
    ring

/-! ## The odd chains keep the run condition -/

private theorem runs_pairChain_zero (m : ℕ) : Rule106Runs (pairChain m) := by
  intro j h0 h1 h2
  simp only [pairChain] at h1 h2
  split_ifs at h1 h2 with ha hb <;> first | omega | exact absurd h1 (by decide) |
    exact absurd h2 (by decide)

private theorem runs_pairChain_one (m : ℕ) : Rule106Runs (window106 (pairChain m)) := by
  rw [window106_pairChain]
  intro j h0 h1 h2
  simp only at h0 h1
  split_ifs at h0 h1 with ha hb <;> first | omega | exact absurd h0 (by decide) |
    exact absurd h1 (by decide)

/-- The value at the lone cell of the pair with one more set cell: the complement of the pair's. -/
private theorem spliced_cell_c (c : ℕ) (hc : c % 6 = 3) (n : ℕ) :
    window106^[n] (pairLattice {0} + Pi.single c 1) c = 1 + window106^[n] (pairLattice {0}) c := by
  have hc3 : 3 ≤ c := by omega
  set X : ℕ → ZMod 2 := pairLattice {0} + Pi.single c 1 with hX
  have ha : ∀ n, ∀ j < c, window106^[n] X j = window106^[n] (pairLattice {0}) j := by
    intro n
    refine window106_iterate_congr_lt (fun j hj => ?_) n
    simp [hX, show j ≠ c by omega]
  rw [window106_iterate_apply_sum X (by omega) n,
    window106_iterate_apply_sum (pairLattice {0}) (by omega) n]
  have hXc : X c = 1 + pairLattice {0} c := by simp [hX, add_comm]
  have hsum : ∑ i ∈ Finset.range n, window106^[i] X (c - 2) * window106^[i] X (c - 1) =
      ∑ i ∈ Finset.range n,
        window106^[i] (pairLattice {0}) (c - 2) * window106^[i] (pairLattice {0}) (c - 1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [ha i (c - 2) (by omega), ha i (c - 1) (by omega)]
  rw [hXc, hsum]
  ring

/-- The two local conditions on the window of width eleven that the run condition across the lone
cell rests on, read at a position of class `4` modulo `6`: the bits `3`, `4`, `5` are not
`0`, `1`, `0`, and the bit `5` with the bits `6`, `7` of the window two steps on are not `1`,
`1`, `1`. -/
private def spliceRunOK (w : ℕ) : Bool :=
  !(!w.testBit 3 && w.testBit 4 && !w.testBit 5) &&
    !(w.testBit 5 && (stepNat^[2] w).testBit 6 && (stepNat^[2] w).testBit 7)

private theorem spliceRunOK_language : (pairWindowLanguage.getD 4 []).all spliceRunOK = true := by
  decide +kernel

private theorem splice_run_bool (a b c d e : Bool)
    (h : (!(!a && b && !c) && !(c && d && e)) = true) :
    ¬ (bz a = 0 ∧ bz b = 1 ∧ bz c = 0) ∧ ¬ (bz c = 1 ∧ bz d = 1 ∧ bz e = 1) := by
  revert a b c d e
  decide

private theorem splice_run_local (c : ℕ) (hc : c % 6 = 3) (n : ℕ) :
    ¬ (window106^[n] (pairLattice {0}) (c - 2) = 0 ∧ window106^[n] (pairLattice {0}) (c - 1) = 1 ∧
        window106^[n] (pairLattice {0}) c = 0) ∧
      ¬ (window106^[n] (pairLattice {0}) c = 1 ∧
        window106^[n + 2] (pairLattice {0}) (c + 1) = 1 ∧
        window106^[n + 2] (pairLattice {0}) (c + 2) = 1) := by
  have hA2 : window106^[n + 2] (pairLattice {0}) =
      window106^[2] (window106^[n] (pairLattice {0})) := by
    rw [← Function.iterate_add_apply, add_comm]
  have hmem := pairWindow_mem_language n ((c : ℤ) - 5)
  have e4 : (((c : ℤ) - 5) % 6).toNat = 4 := by omega
  rw [e4] at hmem
  have hok : spliceRunOK (pairWindow (window106^[n] (pairLattice {0})) ((c : ℤ) - 5)) = true :=
    List.all_eq_true.mp spliceRunOK_language _ hmem
  rw [hA2]
  generalize window106^[n] (pairLattice {0}) = A at hok ⊢
  set w := pairWindow A ((c : ℤ) - 5) with hw
  have hc0 : ∀ k : ℕ, k < 11 → ex A ((c : ℤ) - 5 + (k : ℤ)) = bz (w.testBit k) :=
    fun k hk => ex_pairWindow A _ k hk
  have hc2 : ∀ k : ℕ, 4 ≤ k → k < 11 →
      ex (window106^[2] A) ((c : ℤ) - 5 + (k : ℤ)) = bz ((stepNat^[2] w).testBit k) := by
    intro k h4 h11
    rw [ex_iterate]
    exact stepZ_iterate_bits (ex A) w ((c : ℤ) - 5) 11 hc0 2 k (by omega) h11
  have x0 : A (c - 2) = bz (w.testBit 3) := by
    have := hc0 3 (by omega)
    rwa [ex_cell A c 3 (by omega), show c + 3 - 5 = c - 2 by omega] at this
  have x1 : A (c - 1) = bz (w.testBit 4) := by
    have := hc0 4 (by omega)
    rwa [ex_cell A c 4 (by omega), show c + 4 - 5 = c - 1 by omega] at this
  have x2 : A c = bz (w.testBit 5) := by
    have := hc0 5 (by omega)
    rwa [ex_cell A c 5 (by omega), show c + 5 - 5 = c by omega] at this
  have y1 : window106^[2] A (c + 1) = bz ((stepNat^[2] w).testBit 6) := by
    have := hc2 6 (by omega) (by omega)
    rwa [ex_cell _ c 6 (by omega), show c + 6 - 5 = c + 1 by omega] at this
  have y2 : window106^[2] A (c + 2) = bz ((stepNat^[2] w).testBit 7) := by
    have := hc2 7 (by omega) (by omega)
    rwa [ex_cell _ c 7 (by omega), show c + 7 - 5 = c + 2 by omega] at this
  rw [x0, x1, x2, y1, y2]
  exact splice_run_bool _ _ _ _ _ hok

/-- The pair with one more set cell keeps the run condition at every step. -/
private theorem runs_spliced (c : ℕ) (hc : c % 6 = 3) (n : ℕ) :
    Rule106Runs (window106^[n] (pairLattice {0} + Pi.single c 1)) := by
  have hc3 : 3 ≤ c := by omega
  have hX := window106_iterate_pair_add_single c hc n
  have hXc := spliced_cell_c c hc n
  obtain ⟨hl1, hl2⟩ := splice_run_local c hc n
  intro j h0 h1 h2
  by_cases hjc : j + 2 < c
  · rw [(hX j).1 (by omega)] at h0
    rw [(hX (j + 1)).1 (by omega)] at h1
    rw [(hX (j + 2)).1 (by omega)] at h2
    exact rule106Stays_pair n j h0 h1 h2
  · by_cases hcj : c < j
    · rw [(hX j).2 hcj] at h0
      rw [(hX (j + 1)).2 (by omega)] at h1
      rw [(hX (j + 2)).2 (by omega)] at h2
      exact rule106Stays_pair (n + 2) j h0 h1 h2
    · have hj : j = c - 2 ∨ j = c - 1 ∨ j = c := by omega
      rcases hj with hj | hj | hj
      · subst hj
        rw [(hX (c - 2)).1 (by omega)] at h0
        rw [show c - 2 + 1 = c - 1 by omega, (hX (c - 1)).1 (by omega)] at h1
        rw [show c - 2 + 2 = c by omega, hXc] at h2
        exfalso
        refine hl1 ⟨h0, h1, ?_⟩
        have : (1 : ZMod 2) + window106^[n] (pairLattice {0}) c = 1 := h2
        have h3 : ∀ z : ZMod 2, 1 + z = 1 → z = 0 := by decide
        exact h3 _ this
      · subst hj
        omega
      · subst hj
        rw [hXc] at h0
        rw [(hX (j + 1)).2 (by omega)] at h1
        rw [(hX (j + 2)).2 (by omega)] at h2
        exfalso
        refine hl2 ⟨?_, h1, h2⟩
        have h3 : ∀ z : ZMod 2, 1 + z = 0 → z = 1 := by decide
        exact h3 _ h0

/-- **The chain of an odd number of pairs keeps the run condition at every step**: every iterate
of the window with a pair at each of the cells `3 * y`, `y < m`, has every run of two or more set
cells starting at a multiple of `3`. The first two steps are the chain and the run of the first
`3 * m` cells; from the second step on the window is the pair with one set cell at the residue `3`
modulo `6`, whose run condition across the lone cell is decided at the windows of width eleven of
the pair's orbit ([RuleSpace] §5). -/
theorem rule106Stays_pairChain (m : ℕ) (hm : Odd m) : Rule106Stays (pairChain m) := by
  obtain ⟨t, rfl⟩ := hm
  have hm1 : 1 ≤ 2 * t + 1 := by omega
  have hc : 3 * (2 * t + 1) % 6 = 3 := by omega
  intro n
  rcases n with _ | _ | n
  · exact runs_pairChain_zero _
  · exact runs_pairChain_one _
  · rw [show n + 1 + 1 = n + 2 from rfl, Function.iterate_add_apply,
      window106_iterate_two_pairChain _ hm1]
    exact runs_spliced _ hc n

/-! ## The cell map carries a shadow -/

/-- Windows agreeing from a cell on have renormalizations agreeing from twice that cell on. -/
private theorem renorm_congr_ge {x y : ℕ → ZMod 2} {B : ℕ} (h : ∀ i, B ≤ i → x i = y i) :
    ∀ i, 2 * B ≤ i → renorm x i = renorm y i := by
  intro i hi
  simp only [renorm]
  split_ifs <;> first | rfl | exact h _ (by omega)

/-- **The cell map carries a shadow**: if a window that keeps the run condition agrees with the
orbit of the pair at every step from the cell `B` on, its renormalization agrees with it at every
step from the cell `2 * B + 6` on. A step count `4 * u + r`, `r < 4`, splits as `u` steps before the
renormalization, which commute with it on this window and on the pair, and `r` steps after, which
read `2 * r` cells to the left ([RuleSpace] §5). -/
theorem window106_iterate_renorm_eq_of_shadow (w : ℕ → ZMod 2) (hw : Rule106Stays w) (B : ℕ)
    (h : ∀ n j, B ≤ j → window106^[n] w j = window106^[n] (pairLattice {0}) j) :
    ∀ n j, 2 * B + 6 ≤ j →
      window106^[n] (renorm w) j = window106^[n] (pairLattice {0}) j := by
  intro n j hj
  obtain ⟨u, r, hr, rfl⟩ : ∃ u r, r < 4 ∧ n = r + 4 * u := ⟨n / 4, n % 4, by omega, by omega⟩
  have e1 : window106^[r + 4 * u] (renorm w) = window106^[r] (renorm (window106^[u] w)) := by
    have := (renorm_pow_window106_iterate hw 1 u).2
    simp only [pow_one, Function.iterate_one] at this
    rw [Function.iterate_add_apply, this]
  have e2 : window106^[r + 4 * u] (pairLattice {0}) =
      window106^[r] (renorm (window106^[u] (pairLattice {0}))) := by
    have := window106_iterate_four_pow_mul_pair 1 u
    simp only [pow_one, Function.iterate_one] at this
    rw [Function.iterate_add_apply, this]
  rw [e1, e2]
  apply window106_iterate_congr
  intro i h1 h2
  exact renorm_congr_ge (fun i hi => h u i hi) i (by omega)

/-! ## Lattices of pairs at a common spacing -/

/-- **The lattice of `m` pairs at the spacing `3 * 2 ^ k`**: the window with a pair `11` at each of
the cells `3 * 2 ^ k * y`, `y < m`. -/
def pairChainAt (k m : ℕ) : ℕ → ZMod 2 :=
  fun i => if i % (3 * 2 ^ k) ≤ 1 ∧ i / (3 * 2 ^ k) < m then 1 else 0

private theorem succ_mod_div_of_mod_zero (S a : ℕ) (h3 : 3 ≤ S) (h : a % S = 0) :
    (a + 1) % S = 1 ∧ (a + 1) / S = a / S := by
  obtain ⟨q, rfl⟩ : S ∣ a := Nat.dvd_of_mod_eq_zero h
  have h1 : (S * q + 1) % S = 1 := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : (S * q + 1) / S = q := by
    rw [Nat.mul_add_div (by omega : 0 < S) q 1, Nat.div_eq_of_lt (by omega : 1 < S), add_zero]
  rw [h1, h2, Nat.mul_div_cancel_left _ (by omega)]
  exact ⟨rfl, rfl⟩

private theorem mod_eq_zero_of_succ_mod_one (S a : ℕ) (h : (a + 1) % S = 1) :
    a % S = 0 := by
  have h1 := Nat.div_add_mod (a + 1) S
  rw [h] at h1
  have h2 : a = S * ((a + 1) / S) := by omega
  rw [h2]
  exact Nat.mul_mod_right _ _

private theorem two_mul_add_one_mod_two_mul (a S : ℕ) (hS : 0 < S) :
    (2 * a + 1) % (2 * S) = 2 * (a % S) + 1 := by
  have h := Nat.div_add_mod a S
  have e : 2 * a + 1 = (2 * (a % S) + 1) + (2 * S) * (a / S) := by
    have : 2 * S * (a / S) = 2 * (S * (a / S)) := by ring
    omega
  rw [e, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt a hS; omega)

private theorem two_mul_add_one_div_two_mul (a S : ℕ) (hS : 0 < S) :
    (2 * a + 1) / (2 * S) = a / S := by
  have h := Nat.div_add_mod a S
  have e : 2 * a + 1 = (2 * (a % S) + 1) + (2 * S) * (a / S) := by
    have : 2 * S * (a / S) = 2 * (S * (a / S)) := by ring
    omega
  rw [e, Nat.add_mul_div_left _ _ (by omega : 0 < 2 * S)]
  rw [Nat.div_eq_of_lt (by have := Nat.mod_lt a hS; omega), zero_add]

/-- The renormalization of a lattice of pairs at a spacing divisible by `3` is the lattice of the
same pairs at twice the spacing: the cell map sends a cell divisible by `3` to its double and the
next cell to the double plus one. -/
private theorem renorm_stretch (S m : ℕ) (h3 : 3 ≤ S) (hS : S % 3 = 0) :
    renorm (fun i => if i % S ≤ 1 ∧ i / S < m then (1 : ZMod 2) else 0) =
      fun i => if i % (2 * S) ≤ 1 ∧ i / (2 * S) < m then 1 else 0 := by
  funext i
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' i
  · have h0 : 2 * a % 2 = 0 := by omega
    have h1 : 2 * a / 2 = a := by omega
    have hD : a % S % 3 = a % 3 := Nat.mod_mod_of_dvd a (Nat.dvd_of_mod_eq_zero hS)
    simp only [renorm, h0, h1, ↓reduceIte, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _
      (by norm_num : 0 < 2)]
    split_ifs <;> first | rfl | omega
  · have h0 : ¬ (2 * a + 1) % 2 = 0 := by omega
    have h1 : (2 * a + 1 + 1) / 2 = a + 1 := by omega
    have hD : (a + 1) % S % 3 = (a + 1) % 3 :=
      Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hS)
    simp only [renorm, h0, h1, ↓reduceIte, two_mul_add_one_mod_two_mul a S (by omega),
      two_mul_add_one_div_two_mul a S (by omega)]
    by_cases ha : a % S = 0
    · obtain ⟨e1, e2⟩ := succ_mod_div_of_mod_zero S a h3 ha
      rw [e1, e2]
      split_ifs <;> first | rfl | omega
    · have hne : (a + 1) % S ≠ 1 := fun h => ha (mod_eq_zero_of_succ_mod_one S a h)
      split_ifs <;> first | rfl | omega

private theorem renorm_pairChainAt (k m : ℕ) :
    renorm (pairChainAt k m) = pairChainAt (k + 1) m := by
  have hT : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have e : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
  have := renorm_stretch (3 * 2 ^ k) m (by omega) (by omega)
  unfold pairChainAt
  rw [e]
  exact this

/-- **The `k`-fold renormalization of the chain of pairs** is the lattice of the same number of
pairs at the spacing `3 * 2 ^ k`. -/
theorem renorm_iterate_pairChain (k m : ℕ) : renorm^[k] (pairChain m) = pairChainAt k m := by
  induction k with
  | zero =>
    funext i
    simp [pairChainAt, pairChain]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, renorm_pairChainAt]

/-! ## The states of the lattices -/

/-- **The cells of a lattice of pairs**: the naturals below `3 * 2 ^ k * m` that are `0` or `1`
modulo `3 * 2 ^ k`, as integers. -/
def pairChainAtCells (k m : ℕ) : Finset ℤ :=
  ((Finset.range (3 * 2 ^ k * m)).filter fun i => i % (3 * 2 ^ k) ≤ 1).image fun i : ℕ => (i : ℤ)

private theorem mem_pairChainAtCells (k m j : ℕ) :
    (j : ℤ) ∈ pairChainAtCells k m ↔ j % (3 * 2 ^ k) ≤ 1 ∧ j / (3 * 2 ^ k) < m := by
  have hS : 0 < 3 * 2 ^ k := by positivity
  simp only [pairChainAtCells, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, hi⟩
    have : i = j := by omega
    subst this
    exact ⟨h2, (Nat.div_lt_iff_lt_mul hS).2 (by rw [Nat.mul_comm]; exact h1)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨j, ⟨by rw [Nat.mul_comm]; exact (Nat.div_lt_iff_lt_mul hS).1 h2, h1⟩, rfl⟩

private theorem nonneg_of_mem_pairChainAtCells (k m : ℕ) {z : ℤ} (hz : z ∈ pairChainAtCells k m) :
    0 ≤ z := by
  simp only [pairChainAtCells, Finset.mem_image] at hz
  obtain ⟨i, _, rfl⟩ := hz
  exact Int.natCast_nonneg i

private theorem zero_mem_pairChainAtCells (k m : ℕ) (hm : 1 ≤ m) :
    (0 : ℤ) ∈ pairChainAtCells k m := by
  have := (mem_pairChainAtCells k m 0).2 ⟨by simp, by simpa using (by omega : 0 < m)⟩
  simpa using this

private theorem fullWindow_pairChainAtCells (k m : ℕ) (hm : 1 ≤ m) :
    FiniteConfiguration.fullWindow
        (Finsupp.indicator (pairChainAtCells k m) fun _ _ => (1 : ZMod 2)) = pairChainAt k m := by
  funext j
  change (cfgOf (pairChainAtCells k m)).fullWindow j = _
  rw [fullWindow_indicator (zero_mem_pairChainAtCells k m hm)
    (fun x hx => nonneg_of_mem_pairChainAtCells k m hx) j]
  simp only [pairChainAt, mem_pairChainAtCells]

/-! ## The lattices are shadowed or on the orbit of the pair -/

/-- The chain of an odd number of pairs agrees with the orbit of the pair at every step from the
cell `3 * m + 1` on. -/
private theorem pairChain_agree_pair (m : ℕ) (hm : Odd m) (n j : ℕ) (hj : 3 * m + 1 ≤ j) :
    window106^[n] (pairChain m) j = window106^[n] (pairLattice {0}) j := by
  obtain ⟨t, rfl⟩ := hm
  have hm1 : 1 ≤ 2 * t + 1 := by omega
  have hc : 3 * (2 * t + 1) % 6 = 3 := by omega
  rcases n with _ | _ | n
  · simp only [Function.iterate_zero, id_eq]
    rw [pair_apply_ge j (by omega)]
    simp only [pairChain]
    exact ite_eq_right (fun h => by omega)
  · change window106 (pairChain (2 * t + 1)) j = window106 (pairLattice {0}) j
    rw [window106_pairChain, window106_apply_ge _ (by omega : 2 ≤ j), pair_apply_ge j (by omega),
      pair_apply_ge (j - 1) (by omega), zero_add, mul_zero]
    exact ite_eq_right (fun h => by omega)
  · rw [show n + 1 + 1 = n + 2 from rfl, Function.iterate_add_apply,
      window106_iterate_two_pairChain _ hm1]
    exact (window106_iterate_pair_add_single _ hc n j).2 (by omega)

/-- **The cell map carries a shadow, met with content**: the chain of three pairs keeps the run
condition and agrees with the pair's orbit from the cell `10` on at every step, so its
renormalization agrees with it from the cell `26` on; and the bound has content, the
renormalization being set at the cell `6` where the pair is clear. -/
theorem window106_iterate_renorm_eq_of_shadow_nonvacuous :
    Rule106Stays (pairChain 3) ∧
      (∀ n j, 10 ≤ j → window106^[n] (pairChain 3) j = window106^[n] (pairLattice {0}) j) ∧
      (∀ n j, 2 * 10 + 6 ≤ j →
        window106^[n] (renorm (pairChain 3)) j = window106^[n] (pairLattice {0}) j) ∧
      renorm (pairChain 3) 6 = 1 ∧ pairLattice {0} 6 = 0 := by
  have hs := rule106Stays_pairChain 3 ⟨1, rfl⟩
  have hagree : ∀ n j, 10 ≤ j →
      window106^[n] (pairChain 3) j = window106^[n] (pairLattice {0}) j :=
    fun n j hj => pairChain_agree_pair 3 ⟨1, rfl⟩ n j (by omega)
  refine ⟨hs, hagree, window106_iterate_renorm_eq_of_shadow _ hs 10 hagree, ?_, by decide⟩
  rw [renorm_pairChain]
  decide

/-- Every renormalization of the chain of an odd number of pairs agrees with the orbit of the pair
at every step from some cell on. -/
private theorem renorm_iterate_agree_pair (m : ℕ) (hm : Odd m) (i : ℕ) :
    ∃ B : ℕ, ∀ n j, B ≤ j →
      window106^[n] (renorm^[i] (pairChain m)) j = window106^[n] (pairLattice {0}) j := by
  induction i with
  | zero => exact ⟨3 * m + 1, fun n j hj => pairChain_agree_pair m hm n j hj⟩
  | succ i ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨2 * B + 6, ?_⟩
    rw [Function.iterate_succ_apply']
    exact window106_iterate_renorm_eq_of_shadow _
      (renorm_pow_window106_iterate (rule106Stays_pairChain m hm) i 0).1 B hB

/-- The state of a lattice of an odd number of pairs is shadowed by the pair. -/
private theorem pairShadowed_pairChainAt (k m : ℕ) (hm : Odd m) :
    FiniteConfiguration.PairShadowed
      (Finsupp.indicator (pairChainAtCells k m) fun _ _ => (1 : ZMod 2)) := by
  obtain ⟨t, rfl⟩ := hm
  obtain ⟨B, hB⟩ := renorm_iterate_agree_pair (2 * t + 1) ⟨t, rfl⟩ k
  refine ⟨0, B, fun n j hj => ?_⟩
  rw [fullWindow_pairChainAtCells k _ (by omega), ← renorm_iterate_pairChain]
  simp only [windowShift, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  exact hB n j hj

/-- The diameter of the state of a lattice of pairs: `2` for one pair, and at least `7` for
three or more. -/
private theorem diam_pairChainAtCells (k m : ℕ) (hm : 1 ≤ m) :
    (m = 1 → (cfgOf (pairChainAtCells k m)).diam = 2) ∧
      (3 ≤ m → 3 ≤ (cfgOf (pairChainAtCells k m)).diam) := by
  have hS : 0 < 3 * 2 ^ k := by positivity
  have hS3 : 3 ≤ 3 * 2 ^ k := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  constructor
  · rintro rfl
    have h1 : (1 : ℤ) ∈ pairChainAtCells k 1 := by
      have := (mem_pairChainAtCells k 1 1).2 ⟨by rw [Nat.mod_eq_of_lt (by omega)],
        by rw [Nat.div_eq_of_lt (by omega)]; exact Nat.one_pos⟩
      simpa using this
    have := diam_cfgOf (S := pairChainAtCells k 1) (a := 0) (b := 1)
      (zero_mem_pairChainAtCells k 1 le_rfl) h1 (fun x hx => by
        have hx0 := nonneg_of_mem_pairChainAtCells k 1 hx
        obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hx0
        obtain ⟨h2, h3⟩ := (mem_pairChainAtCells k 1 j).1 hx
        have h4 : j < 3 * 2 ^ k := by
          rcases Nat.div_eq_zero_iff.1 (Nat.lt_one_iff.mp h3) with h | h
          · omega
          · exact h
        rw [Nat.mod_eq_of_lt h4] at h2
        omega)
    simpa using this
  · intro h3
    have hb : ((3 * 2 ^ k * (m - 1) : ℕ) : ℤ) ∈ pairChainAtCells k m := by
      refine (mem_pairChainAtCells k m _).2 ⟨?_, ?_⟩
      · rw [Nat.mul_mod_right]
        omega
      · rw [Nat.mul_div_cancel_left _ hS]
        omega
    have := diam_ge_of_mem (S := pairChainAtCells k m) (zero_mem_pairChainAtCells k m hm) hb
    have h2 : 3 * 2 ^ k * 2 ≤ 3 * 2 ^ k * (m - 1) := Nat.mul_le_mul_left _ (by omega)
    simp only [sub_zero, Int.toNat_natCast] at this
    omega

/-- Reproduction of a state is invariant under translation, in both directions. -/
private theorem reproduces_translate_iff (hq : wolframRule 106 0 0 0 = 0) (c : ℤ)
    (p : FiniteConfiguration) :
    Reproduces (finRule (wolframRule 106) hq) (FiniteConfiguration.translate c p) ↔
      Reproduces (finRule (wolframRule 106) hq) p := by
  refine ⟨fun h => ?_, fun h => Reproduces.translate (wolframRule 106) hq h c⟩
  have := Reproduces.translate (wolframRule 106) hq h (-c)
  rwa [FiniteConfiguration.translate_translate', add_neg_cancel,
    FiniteConfiguration.translate_zero'] at this

/-- **A lattice of `2 ^ j * m` pairs is a number of steps from the lattice of `m` pairs at a wider
spacing**: the window of the lattice of `2 ^ j * m` pairs at the spacing `3 * 2 ^ k` is
`4 ^ k * (2 * (4 ^ j - 1))` steps from that of the lattice of `m` pairs at the spacing
`3 * 2 ^ (k + j)`, for an odd `m`. -/
private theorem pairChainAt_eq_iterate (k j m : ℕ) (hm : Odd m) :
    pairChainAt k (2 ^ j * m) =
      window106^[4 ^ k * (2 * (4 ^ j - 1))] (pairChainAt (k + j) m) := by
  have hs := rule106Stays_pairChain m hm
  have hV : Rule106Stays (renorm^[j] (pairChain m)) := (renorm_pow_window106_iterate hs j 0).1
  have h1 := (renorm_pow_window106_iterate hV k (2 * (4 ^ j - 1))).2
  rw [window106_iterate_renorm_pow_pairChain j m hs, ← Function.iterate_add_apply,
    renorm_iterate_pairChain] at h1
  rw [← renorm_iterate_pairChain, ← h1, add_comm k j, ← renorm_iterate_pairChain]

/-- **Reproduction is the same along a lattice and the lattice it comes from**: the state of the
lattice of `2 ^ j * m` pairs at the spacing `3 * 2 ^ k` is reproduced exactly when the state of the
lattice of `m` pairs at the spacing `3 * 2 ^ (k + j)` is, for an odd `m`. Their windows differ by
steps of the rule, so the states differ by iteration and translation, and rule `106` is
one-to-one. -/
private theorem reproduces_pairChainAt_pow_mul (hq : wolframRule 106 0 0 0 = 0) (k j m : ℕ)
    (hm : Odd m) :
    Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainAtCells k (2 ^ j * m)) fun _ _ => (1 : ZMod 2)) ↔
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainAtCells (k + j) m) fun _ _ => (1 : ZMod 2)) := by
  have hm1 : 1 ≤ m := hm.pos
  have hpow : 1 ≤ 2 ^ j * m := Nat.mul_pos (Nat.two_pow_pos j) hm1
  set u : FiniteConfiguration :=
    Finsupp.indicator (pairChainAtCells (k + j) m) fun _ _ => (1 : ZMod 2) with hu
  set s : FiniteConfiguration :=
    Finsupp.indicator (pairChainAtCells k (2 ^ j * m)) fun _ _ => (1 : ZMod 2) with hs
  have hu0 : u ≠ 0 := by
    intro h
    have h0 := support_indicator_one (pairChainAtCells (k + j) m)
    have hz := zero_mem_pairChainAtCells (k + j) m hm1
    change (cfgOf (pairChainAtCells (k + j) m)).support = _ at h0
    rw [← h0, show (cfgOf (pairChainAtCells (k + j) m)) = 0 from h] at hz
    simp at hz
  have hs0 : s ≠ 0 := by
    intro h
    have h0 := support_indicator_one (pairChainAtCells k (2 ^ j * m))
    have hz := zero_mem_pairChainAtCells k (2 ^ j * m) hpow
    change (cfgOf (pairChainAtCells k (2 ^ j * m))).support = _ at h0
    rw [← h0, show (cfgOf (pairChainAtCells k (2 ^ j * m))) = 0 from h] at hz
    simp at hz
  obtain ⟨hne, hfw⟩ := iterate_fullWindow hq hu0 (4 ^ k * (2 * (4 ^ j - 1)))
  have hwin : s.fullWindow =
      ((finRule (wolframRule 106) hq)^[4 ^ k * (2 * (4 ^ j - 1))] u).fullWindow := by
    rw [hfw, hs, hu, fullWindow_pairChainAtCells k _ hpow,
      fullWindow_pairChainAtCells (k + j) m hm1, pairChainAt_eq_iterate k j m hm]
  have htr := eq_translate_of_fullWindow_eq hs0 hne hwin
  rw [htr, reproduces_translate_iff hq,
    Reproduces.iterate_iff (wolframRule 106) hq (finRule_wolfram106_injective hq)]

/-- **The lattices of odd counts**: the state of the lattice of `m` pairs at the spacing
`3 * 2 ^ k`, for an odd `m`, is reproduced exactly when `m = 1`. -/
private theorem reproduces_pairChainAt_odd (hq : wolframRule 106 0 0 0 = 0) (k m : ℕ)
    (hm : Odd m) :
    Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainAtCells k m) fun _ _ => (1 : ZMod 2)) ↔ m = 1 := by
  have hm1 : 1 ≤ m := hm.pos
  rw [(pairShadowed_pairChainAt k m hm).reproduces_wolfram106_iff hq]
  change (cfgOf (pairChainAtCells k m)).diam = 2 ↔ m = 1
  obtain ⟨h1, h2⟩ := diam_pairChainAtCells k m hm1
  constructor
  · intro hd
    by_contra hne
    have h3 : 3 ≤ m := by
      obtain ⟨t, rfl⟩ := hm
      omega
    have := h2 h3
    omega
  · intro h
    exact h1 h

/-- **The lattices of pairs at a common spacing, classified**: rule `106` reproduces the state with
a pair at each of the cells `3 * 2 ^ k * y`, `y < m`, for a positive `m`, exactly when `m` is a
power of two. Write `m = 2 ^ j * m'` with `m'` odd: the lattice is a number of steps from the
lattice of `m'` pairs at the spacing `3 * 2 ^ (k + j)`; for `m' = 1` that is the pair, which rule
`106` reproduces, and for an odd `m' ≥ 3` it is a state shadowed by the pair and wider than it,
which rule `106` does not ([RuleSpace] §5). -/
theorem reproduces_wolfram106_pairChainAt_iff (hq : wolframRule 106 0 0 0 = 0) (k m : ℕ)
    (hm : 1 ≤ m) :
    Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainAtCells k m) fun _ _ => (1 : ZMod 2)) ↔
      ∃ j, m = 2 ^ j := by
  constructor
  · intro h
    obtain ⟨j, m', hm', rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : m ≠ 0)
    rw [reproduces_pairChainAt_pow_mul hq k j m' hm', reproduces_pairChainAt_odd hq _ m' hm'] at h
    exact ⟨j, by rw [h, mul_one]⟩
  · rintro ⟨j, rfl⟩
    have := reproduces_pairChainAt_pow_mul hq k j 1 odd_one
    rw [mul_one] at this
    rw [this, reproduces_pairChainAt_odd hq _ 1 odd_one]

private theorem not_two_pow_of_lt {m : ℕ} {a : ℕ} (hm : m < 2 ^ a) (hm' : 2 ^ (a - 1) < m) :
    ¬ ∃ j, m = 2 ^ j := by
  rintro ⟨j, rfl⟩
  have h1 : j < a := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hm
  have h2 : a - 1 < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hm'
  omega

/-- **Both sides are met**: the lattice of four pairs at the spacing `6`, with cells `0`, `1`,
`6`, `7`, `12`, `13`, `18` and `19`, is reproduced, and the lattices of three pairs at the spacing
`6` and of six pairs at the spacing `3` are not. -/
theorem reproduces_wolfram106_pairChainAt_iff_nonvacuous (hq : wolframRule 106 0 0 0 = 0) :
    (pairChainAtCells 1 4 = {0, 1, 6, 7, 12, 13, 18, 19} ∧
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainAtCells 1 4) fun _ _ => (1 : ZMod 2))) ∧
    (pairChainAtCells 1 3 = {0, 1, 6, 7, 12, 13} ∧
      ¬ Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainAtCells 1 3) fun _ _ => (1 : ZMod 2))) ∧
    (pairChainAtCells 0 6 = {0, 1, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16} ∧
      ¬ Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainAtCells 0 6) fun _ _ => (1 : ZMod 2))) := by
  refine ⟨⟨by decide, ?_⟩, ⟨by decide, fun h => ?_⟩, ⟨by decide, fun h => ?_⟩⟩
  · exact (reproduces_wolfram106_pairChainAt_iff hq 1 4 (by norm_num)).2 ⟨2, by norm_num⟩
  · exact not_two_pow_of_lt (a := 2) (by norm_num) (by norm_num)
      ((reproduces_wolfram106_pairChainAt_iff hq 1 3 (by norm_num)).1 h)
  · exact not_two_pow_of_lt (a := 3) (by norm_num) (by norm_num)
      ((reproduces_wolfram106_pairChainAt_iff hq 0 6 (by norm_num)).1 h)

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.rule106Stays_pairChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106Stays_pairChain

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_renorm_eq_of_shadow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_renorm_eq_of_shadow

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_renorm_eq_of_shadow_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_renorm_eq_of_shadow_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_pairChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_pairChain

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_six_pairLattice_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_six_pairLattice_range

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_renorm_pow_pairChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_renorm_pow_pairChain

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_iterate_pairChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_iterate_pairChain

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram106_pairChainAt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram106_pairChainAt_iff

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram106_pairChainAt_iff_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram106_pairChainAt_iff_nonvacuous
