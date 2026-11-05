module

public import ECA.Rule106Shadow
import all ECA.Rule106
import all ECA.Rule106Shadow

/-!
# Rule `106` at a pair with one more set cell: the splice
([RuleSpace] §5)

Rule `106` acts on the window of a state, read from its leftmost set cell, by `window106`: cell
`j` of the image is `w j + w (j - 2) * w (j - 1)`. Write `O n` for the window of the pair `11`
after `n` steps. Add to the pair one set cell `c` cells right of it, with `c` at the residue `3`
modulo `6`. At every step the cells below `c` are those of `O n`, cell `c` is the complement of
`O n`'s, and every cell past `c` is that of `O (n + 2)`: the lone cell moves the pair's orbit two
steps ahead past itself. Two steps from a chain of an odd number `m` of pairs three cells apart
make the pair with one set cell at the residue `3` modulo `6` (`c = 3 * m`), so the chain is
shadowed by the pair, and for `m ≥ 3` it is not reproduced.

The argument rests on two products of cells of `O n` and `O (n + 2)` beside `c`, which read only
the eleven cells of `O n` from `c - 5` on. The windows of width eleven of the orbit of the pair form
a finite language, listed by the class of the position modulo `6`: the orbit at step
`4 * u + r`, `r < 4`, is `r` steps of the renormalization of the orbit at step `u`, and the window
of width eleven of the first at a position is a function, through the position's residue modulo
`12` and `r` alone, of the window of width eleven of the second at the cell
`(p - 2 * r - 1) / 2 - 1`. The list is closed under these functions, which a finite computation
decides, and holds the windows of the pair; so every window of every step is listed, and the two
products hold at every listed window of the class of `c - 5`.

## Main results

* `pairWindow` / `pairWindowLanguage` / `pairWindow_mem_language` — the window of width `11` at a
  position, the finite language of the windows of the pair's orbit by the class of the position
  modulo `6`, and the statement that every window of every step lies in it.
* `renormBits` / `imageWindow` / `pairWindow_window106_iterate_renorm` /
  `imageWindow_mem_language` — the renormalized cells cut to a width, the function from a window
  to the window of the renormalization's steps, the statement that the window of `r < 4` steps of
  a renormalization is that function of the window before, and the closure of the language under
  it.
* `window106_iterate_pair_add_single` — **the splice**: the pair with one set cell `c` right of it,
  `c % 6 = 3`, has at every step the cells below `c` of the orbit of the pair and the cells past
  `c` of the orbit two steps ahead; `window106_iterate_pair_add_single_nonvacuous` has the
  advance of two steps with content, and `window106_iterate_pair_add_single_six` shows the
  residue cannot be weakened to `c % 3 = 0`.
* `pairChain` / `window106_iterate_two_pairChain` — the window with a pair at each cell `3 * y`,
  `y < m`, and its image after two steps: the pair and the set cell `3 * m`.
* `pairChainCells` / `pairShadowed_pairChain` / `not_reproduces_wolfram106_pairChain` — the state
  of the chain of pairs, shadowed by the pair for odd `m`, and not reproduced for odd `m ≥ 3`;
  `not_reproduces_wolfram106_pairChain_nonvacuous` meets both sides, the chain of three pairs
  and the pair itself.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## Windows of width eleven -/

/-- **The window of width `11`** of `w` at the position `p`: the number whose bit `k < 11` is set
when cell `p + k` of `w` is set, a cell at a negative position counting as clear. -/
def pairWindow (w : ℕ → ZMod 2) (p : ℤ) : ℕ :=
  ((List.range 11).map fun k : ℕ =>
    if 0 ≤ p + (k : ℤ) ∧ w (p + (k : ℤ)).toNat = 1 then 2 ^ k else 0).sum

/-- **The windows of width `11` of the pair's orbit**, listed by the class of the position modulo
`6`: the list of index `i` holds the windows of width `11` that the orbit of the pair `11` has at
the positions `p` with `p % 6 = i`, among its first `1024` steps, and the window `0`.
`pairWindow_mem_language` shows that no later step has another. -/
def pairWindowLanguage : List (List ℕ) := [
  [
    0, 1, 2, 3, 7, 11, 15, 19, 23, 27, 63, 64, 65, 66, 67, 71, 75, 79, 83, 87, 91, 127, 128, 129,
    130, 131, 135, 139, 143, 147, 151, 155, 191, 192, 193, 194, 195, 448, 449, 450, 455, 704,
    705, 706, 715, 960, 961, 962, 975, 1216, 1217, 1218, 1235, 1472, 1473, 1474, 1495, 1728,
    1729, 1730, 1755, 1984, 1985, 1986, 2047
  ],
  [
    0, 1, 3, 5, 7, 9, 11, 13, 31, 32, 33, 35, 37, 39, 41, 43, 45, 63, 64, 65, 67, 69, 71, 73, 75,
    77, 95, 96, 97, 224, 225, 227, 352, 353, 357, 480, 481, 487, 608, 609, 617, 736, 737, 747,
    864, 865, 877, 2016, 2017, 2047
  ],
  [
    0, 1, 2, 3, 4, 5, 6, 15, 16, 17, 18, 19, 20, 21, 22, 31, 32, 33, 34, 35, 36, 37, 38, 47, 48,
    112, 113, 176, 178, 240, 243, 304, 308, 368, 373, 432, 438, 1008, 1023, 1024, 1025, 1026,
    1027, 1028, 1029, 1030, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1055, 1056, 1057,
    1058, 1059, 1060, 1061, 1062, 1071, 1072, 1136, 1137, 1200, 1202, 1264, 1267, 1328, 1332,
    1392, 1397, 1456, 1462, 2032, 2047
  ],
  [
    0, 1, 2, 3, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 23, 24, 56, 88, 89, 120, 121, 152, 154, 184,
    186, 216, 219, 504, 511, 512, 513, 514, 515, 519, 520, 521, 522, 523, 527, 528, 529, 530,
    531, 535, 536, 568, 600, 601, 632, 633, 664, 666, 696, 698, 728, 731, 1016, 1023, 1024, 1025,
    1026, 1027, 1031, 1032, 1033, 1034, 1035, 1039, 1040, 1041, 1042, 1043, 1047, 1048, 1080,
    1112, 1113, 1144, 1145, 1176, 1178, 1208, 1210, 1240, 1243, 1528, 1535, 1536, 1537, 1538,
    1539, 1543, 1544, 1545, 1546, 1547, 1551, 1552, 1553, 1554, 1555, 1559, 1560, 1592, 1624,
    1625, 1656, 1657, 1688, 1690, 1720, 1722, 1752, 1755, 2040, 2047
  ],
  [
    0, 1, 3, 4, 5, 7, 8, 9, 11, 12, 28, 44, 60, 76, 77, 92, 93, 108, 109, 252, 255, 256, 257,
    259, 260, 261, 263, 264, 265, 267, 268, 284, 300, 316, 332, 333, 348, 349, 364, 365, 508,
    511, 512, 513, 515, 516, 517, 519, 520, 521, 523, 524, 540, 556, 572, 588, 589, 604, 605,
    620, 621, 764, 767, 768, 769, 772, 773, 776, 777, 780, 812, 844, 845, 876, 877, 1792, 1793,
    1795, 1796, 1797, 1799, 1800, 1801, 1803, 1820, 1852, 1884, 1885, 2044, 2047
  ],
  [
    0, 1, 2, 3, 4, 5, 6, 14, 22, 30, 38, 46, 54, 126, 127, 128, 129, 130, 131, 132, 133, 134,
    142, 150, 158, 166, 174, 182, 254, 255, 256, 257, 258, 259, 260, 261, 262, 270, 278, 286,
    294, 302, 310, 382, 383, 384, 386, 388, 390, 422, 896, 898, 900, 910, 942, 1408, 1410, 1412,
    1430, 1462, 1920, 1921, 1922, 1923, 1924, 1925, 1950, 2046, 2047
  ]
]

/-! ### The bits of a window -/

private theorem listSum_lt (N : ℕ) (b : ℕ → Prop) [DecidablePred b] :
    ((List.range N).map fun i => if b i then 2 ^ i else 0).sum < 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_succ]
    split_ifs <;> omega

private theorem testBit_listSum (N : ℕ) (b : ℕ → Prop) [DecidablePred b] (j : ℕ) :
    (((List.range N).map fun i => if b i then 2 ^ i else 0).sum).testBit j =
      decide (j < N ∧ b j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have hlt := listSum_lt N b
    by_cases hb : b N
    · rw [ite_eq_left hb, add_comm, ← mul_one (2 ^ N), Nat.testBit_two_pow_mul_add 1 hlt j, ih]
      by_cases hj : j < N
      · simp [hj, show j < N + 1 by omega]
      · by_cases hjN : j = N
        · subst hjN; simp [hb]
        · have h1 : (1 : ℕ).testBit (j - N) = false := by
            apply Nat.testBit_lt_two_pow
            have : 1 ≤ j - N := by omega
            calc 1 < 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (j - N) := Nat.pow_le_pow_right (by norm_num) this
          simp [hj, h1, show ¬ j < N + 1 by omega]
    · rw [ite_eq_right hb, add_zero, ih, decide_eq_decide]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_contra hj
        have : j = N := by omega
        subst this
        exact hb h2

private theorem testBit_pairWindow (w : ℕ → ZMod 2) (p : ℤ) (j : ℕ) :
    (pairWindow w p).testBit j = decide (j < 11 ∧ ex w (p + (j : ℤ)) = 1) := by
  unfold pairWindow
  rw [testBit_listSum 11 (fun k : ℕ => 0 ≤ p + (k : ℤ) ∧ w (p + (k : ℤ)).toNat = 1) j]
  have hex : ex w (p + (j : ℤ)) = if 0 ≤ p + (j : ℤ) then w (p + (j : ℤ)).toNat else 0 := rfl
  by_cases h : 0 ≤ p + (j : ℤ)
  · simp [hex, h]
  · simp [hex, h]

/-- A bit read as a cell. -/
private def bz (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem ex_pairWindow (w : ℕ → ZMod 2) (p : ℤ) (k : ℕ) (hk : k < 11) :
    ex w (p + (k : ℤ)) = bz ((pairWindow w p).testBit k) := by
  rw [testBit_pairWindow]
  simp only [hk, true_and]
  generalize ex w (p + (k : ℤ)) = x
  revert x
  decide

private theorem stepZ_iterate_bits (h : ℤ → ZMod 2) (Y : ℕ) (lo : ℤ) (N : ℕ)
    (hh : ∀ i : ℕ, i < N → h (lo + (i : ℤ)) = bz (Y.testBit i)) (t : ℕ) :
    ∀ i : ℕ, 2 * t ≤ i → i < N → stepZ^[t] h (lo + (i : ℤ)) = bz ((stepNat^[t] Y).testBit i) := by
  induction t with
  | zero => intro i _ hi; simpa using hh i hi
  | succ t ih =>
    intro i hi hiN
    have e0 := ih i (by omega) hiN
    have e2 := ih (i - 2) (by omega) (by omega)
    have e1 := ih (i - 1) (by omega) (by omega)
    have h2 : lo + (i : ℤ) - 2 = lo + ((i - 2 : ℕ) : ℤ) := by omega
    have h1 : lo + (i : ℤ) - 1 = lo + ((i - 1 : ℕ) : ℤ) := by omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change stepZ^[t] h (lo + (i : ℤ)) + stepZ^[t] h (lo + (i : ℤ) - 2) *
      stepZ^[t] h (lo + (i : ℤ) - 1) = bz ((stepNat (stepNat^[t] Y)).testBit i)
    rw [h2, h1, e0, e1, e2, testBit_stepNat]
    simp only [show 2 ≤ i by omega, show 1 ≤ i by omega, decide_true, Bool.true_and]
    cases (stepNat^[t] Y).testBit i <;> cases (stepNat^[t] Y).testBit (i - 2) <;>
      cases (stepNat^[t] Y).testBit (i - 1) <;> decide

/-! ## The window after the renormalization is local -/

/-- **The renormalized window, cut to a width**: for a position `p` at the residue `p0` modulo
`12`, the number whose bit `i < 11 + 2 * r` is the cell `p - 2 * r + i` of the renormalization of
a window `v`, read off the window `w` of width `11` of `v` that starts at the cell
`(p - 2 * r - 1) / 2 - 1`. Only the residue `p0` enters: moving `p` by a multiple of `12` moves
that cell and the cells read from it alike. -/
def renormBits (w p0 r : ℕ) : ℕ :=
  ((List.range (11 + 2 * r)).map fun i : ℕ =>
    let z := p0 + 12 - 2 * r + i
    let q := (p0 + 11 - 2 * r) / 2 - 1
    if (if z % 2 = 0 then z / 2 % 3 ≠ 1 ∧ w.testBit (z / 2 - q)
        else (z + 1) / 2 % 3 = 1 ∧ w.testBit ((z + 1) / 2 - q))
    then 2 ^ i else 0).sum

/-- **The image function**: for a position `p` at the residue `p0` modulo `12` and `r` steps, from
the window `w` of width `11` of a window `v` at the cell `(p - 2 * r - 1) / 2 - 1`, the window of
width `11` at `p` of `r` steps of rule `106`'s window map on the renormalization of `v`. The
renormalized cells `renormBits w p0 r` are stepped `r` times as the bits of a number, and the
window of width `11` is read off at the offset `2 * r`. -/
def imageWindow (w p0 r : ℕ) : ℕ :=
  ((fun n : ℕ => n ^^^ ((n <<< 2) &&& (n <<< 1)))^[r] (renormBits w p0 r) >>> (2 * r)) % 2 ^ 11

private theorem bz_decide (x : ZMod 2) : bz (decide (x = 1)) = x := by
  revert x
  decide

private theorem renormZ_cell (v : ℕ → ZMod 2) (p : ℤ) (r i : ℕ) (hr : r < 4)
    (hi : i < 11 + 2 * r) :
    renormZ (ex v) (p - 2 * (r : ℤ) + (i : ℤ)) =
      bz ((renormBits (pairWindow v ((p - 2 * (r : ℤ) - 1) / 2 - 1)) (p % 12).toNat r).testBit
        i) := by
  have hlt : (p % 12).toNat < 12 := by omega
  have hp12 : p = 12 * (p / 12) + ((p % 12).toNat : ℤ) := by omega
  generalize (p % 12).toNat = p0 at hlt hp12 ⊢
  generalize p / 12 = a at hp12
  subst hp12
  unfold renormBits
  rw [testBit_listSum]
  simp only [testBit_pairWindow, hi, true_and]
  unfold renormZ
  by_cases h2 : (12 * a + (p0 : ℤ) - 2 * r + i) % 2 = 0
  · have h2' : (p0 + 12 - 2 * r + i) % 2 = 0 := by omega
    have hcov : (p0 + 12 - 2 * r + i) / 2 - ((p0 + 11 - 2 * r) / 2 - 1) < 11 := by omega
    have hidx : (12 * a + (p0 : ℤ) - 2 * r - 1) / 2 - 1 +
        (((p0 + 12 - 2 * r + i) / 2 - ((p0 + 11 - 2 * r) / 2 - 1) : ℕ) : ℤ) =
        (12 * a + p0 - 2 * r + i) / 2 := by omega
    simp only [h2, h2', ↓reduceIte, hidx, hcov, true_and]
    by_cases h3 : (12 * a + (p0 : ℤ) - 2 * r + i) / 2 % 3 = 1
    · have h3' : (p0 + 12 - 2 * r + i) / 2 % 3 = 1 := by omega
      simp [h3, h3', bz]
    · have h3' : ¬ ((p0 + 12 - 2 * r + i) / 2 % 3 = 1) := by omega
      simp only [h3, h3', ↓reduceIte, ne_eq, not_false_eq_true, true_and]
      exact (bz_decide _).symm
  · have h2' : ¬ ((p0 + 12 - 2 * r + i) % 2 = 0) := by omega
    have hcov : (p0 + 12 - 2 * r + i + 1) / 2 - ((p0 + 11 - 2 * r) / 2 - 1) < 11 := by omega
    have hidx : (12 * a + (p0 : ℤ) - 2 * r - 1) / 2 - 1 +
        (((p0 + 12 - 2 * r + i + 1) / 2 - ((p0 + 11 - 2 * r) / 2 - 1) : ℕ) : ℤ) =
        (12 * a + p0 - 2 * r + i + 1) / 2 := by omega
    simp only [h2, h2', ↓reduceIte, hidx, hcov, true_and]
    by_cases h3 : (12 * a + (p0 : ℤ) - 2 * r + i + 1) / 2 % 3 = 1
    · have h3' : (p0 + 12 - 2 * r + i + 1) / 2 % 3 = 1 := by omega
      simp only [h3, h3', ↓reduceIte, true_and]
      exact (bz_decide _).symm
    · have h3' : ¬ ((p0 + 12 - 2 * r + i + 1) / 2 % 3 = 1) := by omega
      simp [h3, h3', bz]

private theorem bz_eq_one (b : Bool) : bz b = 1 ↔ b = true := by
  cases b <;> decide

/-- **The window after the renormalization is local**: the window of width `11` at `p` of `r < 4`
steps of rule `106`'s window map on the renormalization of `v` is the image function of the
window of width `11` of `v` at the cell `(p - 2 * r - 1) / 2 - 1`, with `p` entering through its
residue modulo `12` and `r` alone. -/
theorem pairWindow_window106_iterate_renorm (v : ℕ → ZMod 2) {r : ℕ} (hr : r < 4) (p : ℤ) :
    pairWindow (window106^[r] (renorm v)) p =
      imageWindow (pairWindow v ((p - 2 * (r : ℤ) - 1) / 2 - 1)) (p % 12).toNat r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_pairWindow]
  unfold imageWindow
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hj : j < 11
  · have hcell : ex (window106^[r] (renorm v)) (p + (j : ℤ)) =
        bz (((fun n : ℕ => n ^^^ ((n <<< 2) &&& (n <<< 1)))^[r]
          (renormBits (pairWindow v ((p - 2 * (r : ℤ) - 1) / 2 - 1)) (p % 12).toNat r)).testBit
          (2 * r + j)) := by
      rw [ex_iterate, ex_renorm]
      have := stepZ_iterate_bits (renormZ (ex v))
        (renormBits (pairWindow v ((p - 2 * (r : ℤ) - 1) / 2 - 1)) (p % 12).toNat r)
        (p - 2 * (r : ℤ)) (11 + 2 * r) (fun i hi => renormZ_cell v p r i hr hi) r (2 * r + j)
        (by omega) (by omega)
      rw [show p + (j : ℤ) = p - 2 * (r : ℤ) + ((2 * r + j : ℕ) : ℤ) by push_cast; ring]
      exact this
    rw [hcell]
    simp [hj, bz_eq_one]
  · simp [hj]

/-! ## The window language -/

/-- **The windows of the pair's orbit are closed under the renormalization**: for every residue
`p0` modulo `12` and every `r < 4`, the image function sends each listed window of the source
class to a listed window of the class of `p0` modulo `6`. -/
theorem imageWindow_mem_language :
    ∀ p0 < 12, ∀ r < 4, ∀ w ∈ pairWindowLanguage.getD (((p0 + 11 - 2 * r) / 2 + 5) % 6) [],
      imageWindow w p0 r ∈ pairWindowLanguage.getD (p0 % 6) [] := by
  decide +kernel

private theorem pairWindow_pair_mem (p : ℤ) :
    pairWindow (pairLattice {0}) p ∈ pairWindowLanguage.getD (p % 6).toNat [] := by
  by_cases hp : -11 < p ∧ p < 2
  · obtain ⟨h1, h2⟩ := hp
    interval_cases p <;> decide +kernel
  · have h0 : pairWindow (pairLattice {0}) p = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [testBit_pairWindow]
      have : ¬ (j < 11 ∧ ex (pairLattice {0}) (p + (j : ℤ)) = 1) := by
        rintro ⟨hj, hex⟩
        have hexd : ex (pairLattice {0}) (p + (j : ℤ)) =
            if 0 ≤ p + (j : ℤ) then pairLattice {0} (p + (j : ℤ)).toNat else 0 := rfl
        by_cases hz : 0 ≤ p + (j : ℤ)
        · rw [hexd, ite_eq_left hz] at hex
          simp only [pairLattice, Finset.mem_singleton] at hex
          split_ifs at hex with hc
          · omega
          · exact absurd hex (by decide)
        · rw [hexd, ite_eq_right hz] at hex
          exact absurd hex (by decide)
      simp [this]
    rw [h0]
    have hall : ∀ i < 6, 0 ∈ pairWindowLanguage.getD i [] := by decide
    exact hall _ (by omega)

/-- **The window language**: every window of width `11` of the orbit of the pair `11`, at every
position, is listed for the class of the position modulo `6` ([RuleSpace] §5). -/
theorem pairWindow_mem_language (n : ℕ) (p : ℤ) :
    pairWindow (window106^[n] (pairLattice {0})) p ∈ pairWindowLanguage.getD (p % 6).toNat [] := by
  induction n using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn
      exact pairWindow_pair_mem p
    · obtain ⟨u, r, hr, rfl⟩ : ∃ u r, r < 4 ∧ n = r + 4 * u := ⟨n / 4, n % 4, by omega, by omega⟩
      have hu : u < r + 4 * u := by omega
      rw [Function.iterate_add_apply, rule106Renorm u,
        pairWindow_window106_iterate_renorm _ hr]
      have h1 := ih u hu ((p - 2 * (r : ℤ) - 1) / 2 - 1)
      have e : (((p - 2 * (r : ℤ) - 1) / 2 - 1) % 6).toNat =
          (((p % 12).toNat + 11 - 2 * r) / 2 + 5) % 6 := by omega
      rw [e] at h1
      have h2 := imageWindow_mem_language (p % 12).toNat (by omega) r hr _ h1
      have e2 : (p % 6).toNat = (p % 12).toNat % 6 := by omega
      rw [e2]
      exact h2

/-! ## The splice at a lone cell -/

private theorem window106_apply_ge (w : ℕ → ZMod 2) {j : ℕ} (hj : 2 ≤ j) :
    window106 w j = w j + w (j - 2) * w (j - 1) := by
  simp [window106, hj, show 1 ≤ j by omega]

/-- The two products the splice rests on, read from the windows of the pair's orbit at a position
of class `4` modulo `6`: the check that decides them at every listed window. -/
private def spliceOK (w : ℕ) : Bool :=
  let w2 := stepNat (stepNat w)
  ((w.testBit 4 && !w.testBit 5) == (w2.testBit 4 && w2.testBit 5)) &&
    (!w2.testBit 6 || (w.testBit 5 != w2.testBit 5))

private theorem spliceOK_language : (pairWindowLanguage.getD 4 []).all spliceOK = true := by
  decide +kernel

private theorem splice_bool (a b c d e : Bool)
    (h : (((a && !b) == (c && d)) && (!e || (b != d))) = true) :
    bz a * (1 + bz b) = bz c * bz d ∧ bz e * (1 + bz b + bz d) = 0 := by
  revert a b c d e
  decide

private theorem ex_cell (X : ℕ → ZMod 2) (c k : ℕ) (hck : 5 ≤ c + k) :
    ex X ((c : ℤ) - 5 + (k : ℤ)) = X (c + k - 5) := by
  rw [show (c : ℤ) - 5 + (k : ℤ) = ((c + k - 5 : ℕ) : ℤ) by omega, ex_natCast]

private theorem splice_identities (c : ℕ) (hc : c % 6 = 3) (n : ℕ) :
    window106^[n] (pairLattice {0}) (c - 1) * (1 + window106^[n] (pairLattice {0}) c) =
        window106^[n + 2] (pairLattice {0}) (c - 1) * window106^[n + 2] (pairLattice {0}) c ∧
      window106^[n + 2] (pairLattice {0}) (c + 1) *
        (1 + window106^[n] (pairLattice {0}) c + window106^[n + 2] (pairLattice {0}) c) = 0 := by
  have hA2 : window106^[n + 2] (pairLattice {0}) =
      window106^[2] (window106^[n] (pairLattice {0})) := by
    rw [← Function.iterate_add_apply, add_comm]
  have hmem := pairWindow_mem_language n ((c : ℤ) - 5)
  have e4 : (((c : ℤ) - 5) % 6).toNat = 4 := by omega
  rw [e4] at hmem
  have hok : spliceOK (pairWindow (window106^[n] (pairLattice {0})) ((c : ℤ) - 5)) = true :=
    List.all_eq_true.mp spliceOK_language _ hmem
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
  have x0 : A (c - 1) = bz (w.testBit 4) := by
    have := hc0 4 (by omega)
    rwa [ex_cell A c 4 (by omega), show c + 4 - 5 = c - 1 by omega] at this
  have x1 : A c = bz (w.testBit 5) := by
    have := hc0 5 (by omega)
    rwa [ex_cell A c 5 (by omega), show c + 5 - 5 = c by omega] at this
  have y0 : window106^[2] A (c - 1) = bz ((stepNat^[2] w).testBit 4) := by
    have := hc2 4 (by omega) (by omega)
    rwa [ex_cell _ c 4 (by omega), show c + 4 - 5 = c - 1 by omega] at this
  have y1 : window106^[2] A c = bz ((stepNat^[2] w).testBit 5) := by
    have := hc2 5 (by omega) (by omega)
    rwa [ex_cell _ c 5 (by omega), show c + 5 - 5 = c by omega] at this
  have y2 : window106^[2] A (c + 1) = bz ((stepNat^[2] w).testBit 6) := by
    have := hc2 6 (by omega) (by omega)
    rwa [ex_cell _ c 6 (by omega), show c + 6 - 5 = c + 1 by omega] at this
  rw [x0, x1, y0, y1, y2]
  exact splice_bool _ _ _ _ _ hok

private theorem zmod_aux (a c y s : ZMod 2) (h : y * (1 + a + c) = 0) :
    s + (1 + a) * y = s + c * y := by
  revert a c y s
  decide

private theorem pair_apply_ge (j : ℕ) (hj : 2 ≤ j) : pairLattice {0} j = 0 := by
  simp only [pairLattice, Finset.mem_singleton]
  exact ite_eq_right (fun h => by omega)

private theorem pair_two_apply (j : ℕ) (hj : 4 ≤ j) : window106^[2] (pairLattice {0}) j = 0 := by
  rw [pairLattice_zero_eq_winOfNat, iterate_winOfNat]
  have : stepNat^[2] 3 = 11 := by decide +kernel
  rw [this]
  exact winOfNat_apply_of_lt (L := 4) (by norm_num) hj

/-- **The splice at a lone cell**: the pair with one more set cell `c` cells right of it, `c`
at the residue `3` modulo `6`, agrees at every step with the orbit of the pair below `c`, and
from the cell past `c` on with the orbit of the pair two steps ahead ([RuleSpace] §5). -/
theorem window106_iterate_pair_add_single (c : ℕ) (hc : c % 6 = 3) (n j : ℕ) :
    (j < c → window106^[n] (pairLattice {0} + Pi.single c 1) j =
      window106^[n] (pairLattice {0}) j) ∧
    (c < j → window106^[n] (pairLattice {0} + Pi.single c 1) j =
      window106^[n + 2] (pairLattice {0}) j) := by
  have hc3 : 3 ≤ c := by omega
  set X : ℕ → ZMod 2 := pairLattice {0} + Pi.single c 1 with hX
  have ha : ∀ n, ∀ j < c, window106^[n] X j = window106^[n] (pairLattice {0}) j := by
    intro n
    refine window106_iterate_congr_lt (fun j hj => ?_) n
    simp [hX, show j ≠ c by omega]
  have hb : ∀ n, window106^[n] X c = 1 + window106^[n] (pairLattice {0}) c := by
    intro n
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
  have hcc : ∀ n, ∀ j, c < j → window106^[n] X j = window106^[n + 2] (pairLattice {0}) j := by
    intro n
    induction n with
    | zero =>
      intro j hj
      rw [Function.iterate_zero, id_eq, show 0 + 2 = 2 from rfl, pair_two_apply j (by omega)]
      simp [hX, pair_apply_ge j (by omega), show j ≠ c by omega]
    | succ n ih =>
      intro j hj
      have e3 : n + 1 + 2 = (n + 2) + 1 := rfl
      rw [Function.iterate_succ_apply', e3, Function.iterate_succ_apply',
        window106_apply_ge _ (by omega : 2 ≤ j), window106_apply_ge _ (by omega : 2 ≤ j)]
      obtain ⟨i1, i2⟩ := splice_identities c hc n
      rw [ih j hj]
      rcases Nat.lt_or_ge j (c + 3) with h3 | h3
      · rcases (by omega : j = c + 1 ∨ j = c + 2) with rfl | rfl
        · rw [show c + 1 - 2 = c - 1 by omega, show c + 1 - 1 = c by omega, ha n (c - 1) (by omega),
            hb n, i1]
        · rw [show c + 2 - 2 = c by omega, show c + 2 - 1 = c + 1 by omega, hb n,
            ih (c + 1) (by omega)]
          exact zmod_aux _ _ _ _ i2
      · rw [ih (j - 2) (by omega), ih (j - 1) (by omega)]
  exact ⟨fun hj => ha n j hj, fun hj => hcc n j hj⟩

private theorem pairLattice_add_single_nine :
    pairLattice {0} + Pi.single 9 1 = winOfNat 515 := by
  funext j
  by_cases hj : j < 10
  · interval_cases j <;> decide
  · rw [winOfNat_apply_of_lt (L := 10) (by norm_num) (by omega)]
    simp [pair_apply_ge j (by omega), show j ≠ 9 by omega]

private theorem pairLattice_add_single_six :
    pairLattice {0} + Pi.single 6 1 = winOfNat 67 := by
  funext j
  by_cases hj : j < 7
  · interval_cases j <;> decide
  · rw [winOfNat_apply_of_lt (L := 7) (by norm_num) (by omega)]
    simp [pair_apply_ge j (by omega), show j ≠ 6 by omega]

/-- **The splice has content**: with the lone cell at `c = 9`, the iterate at step `26` is set
at cell `10`, as the orbit of the pair is at step `28`, while the orbit of the pair at step `26` is
clear there. -/
theorem window106_iterate_pair_add_single_nonvacuous :
    9 % 6 = 3 ∧ 9 < 10 ∧ window106^[26] (pairLattice {0} + Pi.single 9 1) 10 = 1 ∧
      window106^[26 + 2] (pairLattice {0}) 10 = 1 ∧ window106^[26] (pairLattice {0}) 10 = 0 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rw [pairLattice_add_single_nine, iterate_winOfNat]
    have h : (stepNat^[26] 515).testBit 10 = true := by decide +kernel
    change (if (stepNat^[26] 515).testBit 10 = true then (1 : ZMod 2) else 0) = 1
    rw [h]
    rfl
  · rw [pairLattice_zero_eq_winOfNat, iterate_winOfNat]
    have h : (stepNat^[26 + 2] 3).testBit 10 = true := by decide +kernel
    change (if (stepNat^[26 + 2] 3).testBit 10 = true then (1 : ZMod 2) else 0) = 1
    rw [h]
    rfl
  · rw [pairLattice_zero_eq_winOfNat, iterate_winOfNat]
    have h : (stepNat^[26] 3).testBit 10 = false := by decide +kernel
    change (if (stepNat^[26] 3).testBit 10 = true then (1 : ZMod 2) else 0) = 0
    rw [h]
    rfl

/-- **The residue `3` modulo `6` cannot be weakened to `3` dividing `c`**: with the lone cell at
`c = 6`, the iterate at step `8` is set at cell `7`, while the orbit of the pair two steps ahead is
clear there. -/
theorem window106_iterate_pair_add_single_six :
    6 % 3 = 0 ∧ 6 < 7 ∧ window106^[8] (pairLattice {0} + Pi.single 6 1) 7 = 1 ∧
      window106^[8 + 2] (pairLattice {0}) 7 = 0 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [pairLattice_add_single_six, iterate_winOfNat]
    have h : (stepNat^[8] 67).testBit 7 = true := by decide +kernel
    change (if (stepNat^[8] 67).testBit 7 = true then (1 : ZMod 2) else 0) = 1
    rw [h]
    rfl
  · rw [pairLattice_zero_eq_winOfNat, iterate_winOfNat]
    have h : (stepNat^[8 + 2] 3).testBit 7 = false := by decide +kernel
    change (if (stepNat^[8 + 2] 3).testBit 7 = true then (1 : ZMod 2) else 0) = 0
    rw [h]
    rfl

/-! ## A chain of pairs -/

/-- **A chain of pairs**: the window with a pair `11` at the cell `3 * y` for every `y < m`. -/
def pairChain (m : ℕ) : ℕ → ZMod 2 :=
  fun i => if i % 3 ≤ 1 ∧ i / 3 < m then 1 else 0

private theorem window106_pairChain (m : ℕ) :
    window106 (pairChain m) = fun j => if j < 3 * m then (1 : ZMod 2) else 0 := by
  funext j
  simp only [window106, pairChain]
  split_ifs <;> first | omega | rfl

private theorem window106_run (m : ℕ) (hm : 1 ≤ m) :
    window106 (fun j => if j < 3 * m then (1 : ZMod 2) else 0) =
      pairLattice {0} + Pi.single (3 * m) 1 := by
  funext j
  simp only [window106, pairLattice, Pi.add_apply, Pi.single_apply, Finset.mem_singleton]
  split_ifs <;> first | omega | rfl

/-- **Two steps from a chain of pairs**: two steps of rule `106`'s window map take the window
with a pair at each of the cells `3 * y`, `y < m`, to the pair `11` together with one set cell at
`3 * m` ([RuleSpace] §5). The first step makes the run of the first `3 * m` cells, the second
leaves the pair, clear cells, and the cell `3 * m`. -/
theorem window106_iterate_two_pairChain (m : ℕ) (hm : 1 ≤ m) :
    window106^[2] (pairChain m) = pairLattice {0} + Pi.single (3 * m) 1 := by
  change window106 (window106 (pairChain m)) = _
  rw [window106_pairChain, window106_run m hm]

/-! ## The states a chain of pairs gives -/

/-- **The cells of a chain of pairs**: the naturals below `3 * m` that are not `2` modulo `3`,
as integers. -/
def pairChainCells (m : ℕ) : Finset ℤ :=
  ((Finset.range (3 * m)).filter fun i => i % 3 ≠ 2).image fun i : ℕ => (i : ℤ)

private theorem mem_pairChainCells (m : ℕ) (j : ℕ) :
    (j : ℤ) ∈ pairChainCells m ↔ j % 3 ≤ 1 ∧ j / 3 < m := by
  simp only [pairChainCells, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, hi⟩
    have : i = j := by omega
    subst this
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨j, ⟨by omega, by omega⟩, rfl⟩

private theorem nonneg_of_mem_pairChainCells (m : ℕ) {z : ℤ} (hz : z ∈ pairChainCells m) :
    0 ≤ z := by
  simp only [pairChainCells, Finset.mem_image] at hz
  obtain ⟨i, _, rfl⟩ := hz
  exact Int.natCast_nonneg i

private theorem fullWindow_pairChainCells (m : ℕ) (hm : 1 ≤ m) :
    FiniteConfiguration.fullWindow
        (Finsupp.indicator (pairChainCells m) fun _ _ => (1 : ZMod 2)) = pairChain m := by
  have h0 : (0 : ℤ) ∈ pairChainCells m := by
    have := (mem_pairChainCells m 0).2 ⟨by omega, by omega⟩
    simpa using this
  funext j
  change (cfgOf (pairChainCells m)).fullWindow j = _
  rw [fullWindow_indicator h0 (fun x hx => nonneg_of_mem_pairChainCells m hx) j]
  simp only [pairChain, mem_pairChainCells]

/-- **The odd chains of pairs are shadowed by the pair**: the state with a pair at each of the
cells `3 * y`, `y < m`, for an odd `m`, agrees at every step and at every cell from `3 * m + 1` on
with the orbit of the pair ([RuleSpace] §5). -/
theorem pairShadowed_pairChain (m : ℕ) (hm : Odd m) :
    FiniteConfiguration.PairShadowed
      (Finsupp.indicator (pairChainCells m) fun _ _ => (1 : ZMod 2)) := by
  obtain ⟨t, rfl⟩ := hm
  have hm1 : 1 ≤ 2 * t + 1 := by omega
  have hc : 3 * (2 * t + 1) % 6 = 3 := by omega
  refine ⟨0, 3 * (2 * t + 1) + 1, fun n j hj => ?_⟩
  rw [fullWindow_pairChainCells _ hm1]
  simp only [windowShift, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
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

/-- **The odd chains of at least three pairs are not reproduced**: rule `106` does not reproduce
the state with a pair at each of the cells `3 * y`, `y < m`, for an odd `m` of at least `3`
([RuleSpace] §5). The state is shadowed by the pair, and its diameter is `3 * m - 1`. -/
theorem not_reproduces_wolfram106_pairChain (hq : wolframRule 106 0 0 0 = 0) (m : ℕ)
    (hm : Odd m) (h3 : 3 ≤ m) :
    ¬ Reproduces (finRule (wolframRule 106) hq)
      (Finsupp.indicator (pairChainCells m) fun _ _ => (1 : ZMod 2)) := by
  intro hrep
  have hd := ((pairShadowed_pairChain m hm).reproduces_wolfram106_iff hq).mp hrep
  have h0 : (0 : ℤ) ∈ pairChainCells m := by
    have := (mem_pairChainCells m 0).2 ⟨by omega, by omega⟩
    simpa using this
  have hb : ((3 * m - 2 : ℕ) : ℤ) ∈ pairChainCells m :=
    (mem_pairChainCells m (3 * m - 2)).2 ⟨by omega, by omega⟩
  have := diam_ge_of_mem (S := pairChainCells m) h0 hb
  change (cfgOf _).diam = 2 at hd
  omega

/-- **Both sides are met**: the chain of three pairs is shadowed by the pair and not reproduced,
and the chain of one pair, the pair itself, is shadowed and reproduced. -/
theorem not_reproduces_wolfram106_pairChain_nonvacuous (hq : wolframRule 106 0 0 0 = 0) :
    (FiniteConfiguration.PairShadowed
        (Finsupp.indicator (pairChainCells 3) fun _ _ => (1 : ZMod 2)) ∧
      ¬ Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainCells 3) fun _ _ => (1 : ZMod 2))) ∧
    (FiniteConfiguration.PairShadowed
        (Finsupp.indicator (pairChainCells 1) fun _ _ => (1 : ZMod 2)) ∧
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.indicator (pairChainCells 1) fun _ _ => (1 : ZMod 2))) := by
  refine ⟨⟨pairShadowed_pairChain 3 ⟨1, rfl⟩,
    not_reproduces_wolfram106_pairChain hq 3 ⟨1, rfl⟩ le_rfl⟩,
    pairShadowed_pairChain 1 ⟨0, rfl⟩, ?_⟩
  have h1 : pairChainCells 1 = {0, 1} := by decide
  rw [h1]
  have hrep : Reproduces (finRule (wolframRule 106) hq)
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single 1 1) := by
    simpa using reproduces_wolfram106_orbit hq 0
  rw [pair_eq_cfgOf] at hrep
  exact hrep

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.pairWindow_window106_iterate_renorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.pairWindow_window106_iterate_renorm

set_option linter.style.longLine false in
/-- info: 'ECA.imageWindow_mem_language' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.imageWindow_mem_language

set_option linter.style.longLine false in
/-- info: 'ECA.pairWindow_mem_language' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.pairWindow_mem_language

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_pair_add_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_pair_add_single

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_pair_add_single_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_pair_add_single_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_pair_add_single_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_pair_add_single_six

set_option linter.style.longLine false in
/-- info: 'ECA.window106_iterate_two_pairChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.window106_iterate_two_pairChain

set_option linter.style.longLine false in
/-- info: 'ECA.pairShadowed_pairChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.pairShadowed_pairChain

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram106_pairChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram106_pairChain

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram106_pairChain_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram106_pairChain_nonvacuous
