module

public import ECA.EdgeColumns
import all ECA.EdgeWindow
import all ECA.EdgeColumns

/-!
# Rules `106` and `120` reproduce a pattern
([RuleSpace] §5)

Rule `106` sends `a b c` to `c + a * b`, so on the window read from the leftmost set cell it acts by
`window106`: cell `j` of the image is `w j + w (j - 2) * w (j - 1)`. Write `P(X)` for the pair
lattice, a pair `11` at each cell `6 * x` with `x ∈ X`, and `C(X)` for the copy lattice, a copy of
the pattern `1101` at each such cell. Three statements about the window map give reproduction, and
all three are proved, so rules `106` and `120` reproduce a pattern unconditionally. Four steps from
the pair `11` equal one step renormalized under the cell map `j ↦ 2 * j - [j % 3 = 1]`
(`Rule106Renorm`); twenty-four steps take `P(2 * Y)` to
`P(2 * Y ∪ (2 * Y + 1))` (`Rule106Step24`); two steps take `P(X)` to `C(X)` (`Rule106TwoSteps`).
Writing `g s` for the number whose base-four digits are the binary digits of `s`, induction over
the bits of `s` gives `P(sub s)` after `24 * g s` steps from `P({0})`, with `sub s` the submasks of
`s`, and `C(sub s)` two steps later. For `s = (2 ^ b - 1) * 2 ^ a` the lattice `C(sub s)` is `2 ^ b`
copies of the pattern at gap `6 * 2 ^ a - 4`, and the full window of a state, read from its leftmost
set cell, determines the state up to translation. Rule `120` is the mirror of rule `106`, and
reflection carries reproduction to the mirror rule.

## Main results

* `window106` / `renormCell` / `renorm` / `pairLattice` / `copiesLattice` — the window map, the
  cell map of the renormalization, the renormalized window and the two lattices.
* `Rule106Renorm` / `Rule106Step24` / `Rule106TwoSteps` — the three statements the results
  consume, as propositions.
* `Rule106Class` / `renorm_window106_four` / `rule106Class_renorm_iterate` / `rule106Renorm` —
  the class of windows starting with the pair whose runs of two or more set cells start at
  multiples of `3`, four steps commuting with the renormalization on the class, the class kept
  by the first four iterates of a renormalization, and the first statement proved by strong
  induction on the orbit of the pair; `not_renorm_window106_four_of_offphase` — the class
  condition is needed, and `renorm_window106_four_nonvacuous` — the commutation at the sixth
  window of the orbit.
* `blockLattice` / `blockStep` / `window106_blockLattice` / `window106_iterate_blockLattice` — a
  lattice of disjoint pieces in blocks of width `L`, one step of a piece, and the statement that
  the window map acts on each block alone while the pieces' last two cells stay clear.
* `rule106TwoSteps` / `rule106Step24` — two of the three statements, proved from the block
  statement by finite computation on one piece; `rule106Step24_nonvacuous` — the second at
  `Y = {0, 1}`, pairs at cells `0` and `12` becoming pairs at cells `0`, `6`, `12` and `18`.
* `renorm_renormCell` / `renorm_pairLattice` — the renormalization puts `w j` at `renormCell j`,
  and sends a pair lattice to the pair lattice of the doubles.
* `FiniteConfiguration.fullWindow` — the window of a state read from its leftmost set cell with no
  cut in the width.
* `reproduces_wolfram106_of_window` — rule `106` reproduces the pattern of cells `0`, `1` and `3`,
  from the three statements as hypotheses; `reproduces_wolfram120_of_window` — rule `120`
  reproduces its reflection, from the same three.
* `reproduces_wolfram106` / `reproduces_wolfram120` — the two forms with the three statements
  proved, no hypothesis left.
* `copies_window106_nonvacuous` — the chain at the first doubling: the full window of the
  twenty-fourth iterate of rule `106` from the pattern is `C({0, 1})`, cells `0`, `1`, `3`, `6`,
  `7` and `9` set and all others clear.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## Windows, the cell map and the lattices -/

/-- **Rule `106`'s window map**: cell `j` of the image is `w j + w (j - 2) * w (j - 1)`, a cell
below `0` being clear. -/
def window106 (w : ℕ → ZMod 2) : ℕ → ZMod 2 := fun j =>
  w j + (if 2 ≤ j then w (j - 2) else 0) * (if 1 ≤ j then w (j - 1) else 0)

/-- **The cell map of the renormalization**: cell `j` goes to cell `2 * j`, except that a cell
`j` with `j % 3 = 1` goes to `2 * j - 1`. -/
def renormCell (j : ℕ) : ℕ := if j % 3 = 1 then 2 * j - 1 else 2 * j

/-- **The renormalized window**: `w j` stands at cell `renormCell j` and every other cell is
clear; at an even cell `i` the value is `w (i / 2)` when `(i / 2) % 3 ≠ 1`, at an odd cell `i` it
is `w ((i + 1) / 2)` when `((i + 1) / 2) % 3 = 1`, and `0` otherwise. -/
def renorm (w : ℕ → ZMod 2) : ℕ → ZMod 2 := fun i =>
  if i % 2 = 0 then (if (i / 2) % 3 ≠ 1 then w (i / 2) else 0)
  else (if ((i + 1) / 2) % 3 = 1 then w ((i + 1) / 2) else 0)

/-- **The pair lattice** of a finite set `X`: a pair `11` at each cell `6 * x`, `x ∈ X`. -/
def pairLattice (X : Finset ℕ) : ℕ → ZMod 2 :=
  fun i => if i % 6 ≤ 1 ∧ i / 6 ∈ X then 1 else 0

/-- **The copy lattice** of a finite set `X`: a copy of the pattern `1101` at each cell `6 * x`,
`x ∈ X`. -/
def copiesLattice (X : Finset ℕ) : ℕ → ZMod 2 :=
  fun i => if (i % 6 = 0 ∨ i % 6 = 1 ∨ i % 6 = 3) ∧ i / 6 ∈ X then 1 else 0

/-- **The renormalization statement**: from the pair `11`, `4 * u` steps of rule `106`'s window map
give the renormalization of the window after `u` steps. -/
def Rule106Renorm : Prop :=
  ∀ u : ℕ, window106^[4 * u] (pairLattice {0}) = renorm (window106^[u] (pairLattice {0}))

/-- **The twenty-four-step statement**: twenty-four steps of rule `106`'s window map take the pair
lattice of the doubles of `Y` to the pair lattice of the doubles of `Y` and their successors. -/
def Rule106Step24 : Prop :=
  ∀ Y : Finset ℕ, window106^[24] (pairLattice (Y.image (2 * ·))) =
    pairLattice (Y.image (2 * ·) ∪ Y.image (2 * · + 1))

/-- **The two-step statement**: two steps of rule `106`'s window map take the pair lattice of `X`
to the copy lattice of `X`. -/
def Rule106TwoSteps : Prop :=
  ∀ X : Finset ℕ, window106^[2] (pairLattice X) = copiesLattice X

/-! ## The renormalization of a pair lattice -/

theorem renorm_renormCell (w : ℕ → ZMod 2) (j : ℕ) : renorm w (renormCell j) = w j := by
  unfold renorm renormCell
  split_ifs <;> first | omega | (congr 1; omega)

private theorem mem_image_two {X : Finset ℕ} {n : ℕ} :
    n ∈ X.image (2 * ·) ↔ n % 2 = 0 ∧ n / 2 ∈ X := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by omega, ?_⟩
    rw [show 2 * x / 2 = x by omega]
    exact hx
  · rintro ⟨h1, h2⟩
    exact ⟨n / 2, h2, by omega⟩

/-- **The renormalization of a pair lattice** is the pair lattice of the doubles. -/
theorem renorm_pairLattice (X : Finset ℕ) :
    renorm (pairLattice X) = pairLattice (X.image (2 * ·)) := by
  funext i
  simp only [renorm, pairLattice, mem_image_two]
  have e1 : i / 2 / 6 = i / 12 := by omega
  have e3 : i / 6 / 2 = i / 12 := by omega
  by_cases h : i % 2 = 0
  · simp only [h, ↓reduceIte, e1, e3]
    by_cases hM : i / 12 ∈ X <;> simp only [hM, and_true, and_false, ite_false] <;>
      split_ifs <;> first | omega | rfl
  · simp only [h, ↓reduceIte, e3]
    have e2 : (i + 1) / 2 / 6 = (i + 1) / 12 := by omega
    simp only [e2]
    by_cases hc : (i + 1) / 2 % 6 ≤ 1 ∧ (i + 1) / 2 % 3 = 1
    · have e4 : (i + 1) / 12 = i / 12 := by omega
      simp only [e4]
      by_cases hM : i / 12 ∈ X <;> simp only [hM, and_true, and_false, ite_false] <;>
        split_ifs <;> first | omega | rfl
    · split_ifs <;> first | omega | rfl

/-! ## Blocks of disjoint pieces -/

/-- **A block lattice**: cell `i` is set when its residue `i % L` lies in `S` and its block
`i / L` lies in `X`, so a copy of the piece `S` stands in each block of width `L` indexed by `X`. -/
def blockLattice (L : ℕ) (S X : Finset ℕ) : ℕ → ZMod 2 :=
  fun i => if i % L ∈ S ∧ i / L ∈ X then 1 else 0

/-- **One step on a piece**: the residues below `L` that are set after one step of `window106`
from the window that is `1` exactly on `S`. -/
def blockStep (L : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun r => window106 (fun j => if j ∈ S then 1 else 0) r = 1)

private theorem blockLattice_apply {L : ℕ} (hL : 0 < L) {q r : ℕ} (hr : r < L) (S X : Finset ℕ) :
    blockLattice L S X (L * q + r) = if r ∈ S ∧ q ∈ X then 1 else 0 := by
  unfold blockLattice
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div hL, Nat.div_eq_of_lt hr, Nat.add_zero]

/-- **One step of `window106` acts on each block alone**: when the pieces' last two cells are
clear, the image of a block lattice is the block lattice of the image of the piece. -/
theorem window106_blockLattice {L : ℕ} (hL : 2 ≤ L) {S : Finset ℕ} (hS : ∀ r ∈ S, r + 2 < L)
    (X : Finset ℕ) :
    window106 (blockLattice L S X) = blockLattice L (blockStep L S) X := by
  have hL0 : 0 < L := by omega
  have key : ∀ r, r < L → window106 (fun j => if j ∈ S then (1 : ZMod 2) else 0) r =
      if r ∈ blockStep L S then 1 else 0 := by
    intro r hr
    have hz : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
    by_cases h : window106 (fun j => if j ∈ S then (1 : ZMod 2) else 0) r = 1
    · have hm : r ∈ blockStep L S := Finset.mem_filter.2 ⟨Finset.mem_range.2 hr, h⟩
      rw [ite_eq_left hm]
      exact h
    · have hm : r ∉ blockStep L S := fun hh => h (Finset.mem_filter.1 hh).2
      rw [ite_eq_right hm]
      exact hz _ h
  funext i
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < L ∧ i = L * q + r :=
    ⟨i / L, i % L, Nat.mod_lt _ hL0, (Nat.div_add_mod i L).symm⟩
  have hk := key r hr
  simp only [window106] at hk ⊢
  rw [blockLattice_apply hL0 hr (blockStep L S) X, blockLattice_apply hL0 hr S X]
  by_cases hr2 : 2 ≤ r
  · have e2 : L * q + r - 2 = L * q + (r - 2) := by omega
    have e1 : L * q + r - 1 = L * q + (r - 1) := by omega
    rw [e2, e1, blockLattice_apply hL0 (by omega : r - 2 < L) S X,
      blockLattice_apply hL0 (by omega : r - 1 < L) S X,
      ite_eq_left (by omega : 2 ≤ L * q + r), ite_eq_left (by omega : 1 ≤ L * q + r)]
    rw [ite_eq_left hr2, ite_eq_left (by omega : 1 ≤ r)] at hk
    by_cases hq : q ∈ X
    · simp only [hq, and_true]
      exact hk
    · simp [hq]
  · rw [ite_eq_right hr2, zero_mul, add_zero] at hk
    have hfirst : (if 2 ≤ L * q + r then blockLattice L S X (L * q + r - 2) else 0) = 0 := by
      rcases q with _ | q
      · rw [ite_eq_right (by simp; omega)]
      · have e : L * (q + 1) + r - 2 = L * q + (L + r - 2) := by rw [Nat.mul_succ]; omega
        rw [e, blockLattice_apply hL0 (by omega : L + r - 2 < L) S X]
        split_ifs with h h'
        · exact absurd (hS _ h'.1) (by omega)
        · rfl
        · rfl
    rw [hfirst, zero_mul, add_zero]
    by_cases hq : q ∈ X
    · simp only [hq, and_true]
      exact hk
    · simp [hq]

/-- **Iterating the block statement**: as long as each stage of the piece keeps its last two cells
clear, `n` steps of `window106` on a block lattice give the block lattice of the `n`-th iterate of
the piece's step. -/
theorem window106_iterate_blockLattice {L : ℕ} (hL : 2 ≤ L) (S X : Finset ℕ) (n : ℕ)
    (hS : ∀ k < n, ∀ r ∈ (blockStep L)^[k] S, r + 2 < L) :
    window106^[n] (blockLattice L S X) = blockLattice L ((blockStep L)^[n] S) X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun k hk => hS k (by omega)), window106_blockLattice hL (hS n (by omega))]

private theorem pairLattice_eq_blockLattice (X : Finset ℕ) :
    pairLattice X = blockLattice 6 {0, 1} X := by
  funext i
  unfold pairLattice blockLattice
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply if_congr _ rfl rfl
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

private theorem copiesLattice_eq_blockLattice (X : Finset ℕ) :
    copiesLattice X = blockLattice 6 {0, 1, 3} X := by
  funext i
  unfold copiesLattice blockLattice
  simp only [Finset.mem_insert, Finset.mem_singleton]

private theorem mem_image_two_succ {X : Finset ℕ} {n : ℕ} :
    n ∈ X.image (2 * · + 1) ↔ n % 2 = 1 ∧ n / 2 ∈ X := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by omega, ?_⟩
    rw [show (2 * x + 1) / 2 = x by omega]
    exact hx
  · rintro ⟨h1, h2⟩
    exact ⟨n / 2, h2, by omega⟩

private theorem pairLattice_double_eq (Y : Finset ℕ) :
    pairLattice (Y.image (2 * ·)) = blockLattice 12 {0, 1} Y := by
  funext i
  unfold pairLattice blockLattice
  simp only [Finset.mem_insert, Finset.mem_singleton, mem_image_two]
  apply if_congr _ rfl rfl
  have e : i / 6 / 2 = i / 12 := by omega
  rw [e]
  by_cases hy : i / 12 ∈ Y
  · simp only [hy, and_true]
    omega
  · simp only [hy, and_false]

private theorem pairLattice_double_union_eq (Y : Finset ℕ) :
    pairLattice (Y.image (2 * ·) ∪ Y.image (2 * · + 1)) = blockLattice 12 {0, 1, 6, 7} Y := by
  funext i
  unfold pairLattice blockLattice
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, mem_image_two,
    mem_image_two_succ]
  apply if_congr _ rfl rfl
  have e : i / 6 / 2 = i / 12 := by omega
  rw [e]
  by_cases hy : i / 12 ∈ Y
  · simp only [hy, and_true]
    omega
  · simp only [hy, and_false, or_self]

/-- **The two-step statement holds**: two steps of rule `106`'s window map take the pair lattice of
`X` to the copy lattice of `X`, the pieces sitting in blocks of width `6`. -/
theorem rule106TwoSteps : Rule106TwoSteps := by
  intro X
  rw [pairLattice_eq_blockLattice, copiesLattice_eq_blockLattice,
    window106_iterate_blockLattice (L := 6) (by norm_num) {0, 1} X 2 (by decide)]
  rw [show (blockStep 6)^[2] ({0, 1} : Finset ℕ) = {0, 1, 3} from by decide]

/-- **The twenty-four-step statement holds**: twenty-four steps of rule `106`'s window map take the
pair lattice of the doubles of `Y` to the pair lattice of the doubles and their successors, the
pieces sitting in blocks of width `12`. -/
theorem rule106Step24 : Rule106Step24 := by
  intro Y
  rw [pairLattice_double_eq, pairLattice_double_union_eq,
    window106_iterate_blockLattice (L := 12) (by norm_num) {0, 1} Y 24 (by decide)]
  rw [show (blockStep 12)^[24] ({0, 1} : Finset ℕ) = {0, 1, 6, 7} from by decide]

/-- **The twenty-four-step statement at `Y = {0, 1}`**: pairs at cells `0` and `12` become pairs
at cells `0`, `6`, `12` and `18`. -/
theorem rule106Step24_nonvacuous :
    window106^[24] (pairLattice {0, 2}) = pairLattice {0, 1, 2, 3} := by
  have h := rule106Step24 {0, 1}
  rwa [show ({0, 1} : Finset ℕ).image (2 * ·) = {0, 2} from by decide,
    show ({0, 1} : Finset ℕ).image (2 * · + 1) = {1, 3} from by decide,
    show ({0, 2} : Finset ℕ) ∪ {1, 3} = {0, 1, 2, 3} from by decide] at h

/-! ## The submasks and the digit map -/

/-- The number whose base-four digits are the binary digits of `s`. -/
private def quadDigits (s : ℕ) : ℕ :=
  if s = 0 then 0 else 4 * quadDigits (s / 2) + s % 2
termination_by s
decreasing_by omega

private theorem quadDigits_zero : quadDigits 0 = 0 := by
  rw [quadDigits]
  simp

private theorem quadDigits_double (s : ℕ) : quadDigits (2 * s) = 4 * quadDigits s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [quadDigits_zero]
  · have h0 : 2 * s ≠ 0 := by omega
    rw [quadDigits]
    simp [h0, show 2 * s / 2 = s by omega]

private theorem quadDigits_double_succ (s : ℕ) :
    quadDigits (2 * s + 1) = 4 * quadDigits s + 1 := by
  rw [quadDigits]
  simp [show (2 * s + 1) / 2 = s by omega]

/-- The submasks of `s`, as a finite set. -/
private def submasks (s : ℕ) : Finset ℕ :=
  if s = 0 then {0}
  else if s % 2 = 0 then (submasks (s / 2)).image (2 * ·)
  else (submasks (s / 2)).image (2 * ·) ∪ (submasks (s / 2)).image (2 * · + 1)
termination_by s
decreasing_by all_goals omega

private theorem submasks_zero : submasks 0 = {0} := by
  rw [submasks]
  simp

private theorem submasks_double (s : ℕ) : submasks (2 * s) = (submasks s).image (2 * ·) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [submasks_zero]
  · have h0 : 2 * s ≠ 0 := by omega
    rw [submasks]
    simp [h0, show 2 * s / 2 = s by omega]

private theorem submasks_double_succ (s : ℕ) :
    submasks (2 * s + 1) = (submasks s).image (2 * ·) ∪ (submasks s).image (2 * · + 1) := by
  rw [submasks]
  simp [show (2 * s + 1) / 2 = s by omega]

/-! ## The pair lattice after `24 * g s` steps -/

private theorem iterate_pairLattice (h1 : Rule106Renorm) (h2 : Rule106Step24) :
    ∀ s : ℕ, window106^[24 * quadDigits s] (pairLattice {0}) = pairLattice (submasks s) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [quadDigits_zero, submasks_zero]
    · obtain ⟨s', rfl | rfl⟩ := Nat.even_or_odd' s
      · have hlt : s' < 2 * s' := by omega
        have e : 24 * quadDigits (2 * s') = 4 * (24 * quadDigits s') := by
          rw [quadDigits_double]; ring
        rw [e, h1, ih s' hlt, renorm_pairLattice, submasks_double]
      · have hlt : s' < 2 * s' + 1 := by omega
        have e : 24 * quadDigits (2 * s' + 1) = 24 + 4 * (24 * quadDigits s') := by
          rw [quadDigits_double_succ]; ring
        rw [e, Function.iterate_add_apply, h1, ih s' hlt, renorm_pairLattice, h2,
          submasks_double_succ]

/-! ## From a state to its full window -/

/-- **The full window** of a finite state: cell `j` is the state's value `j` cells right of its
leftmost set cell, with no cut in the width. -/
noncomputable def FiniteConfiguration.fullWindow (s : FiniteConfiguration) : ℕ → ZMod 2 :=
  fun j => s (s.leftEnd + j)

private theorem wolframRule106_apply (a b c : ZMod 2) : wolframRule 106 a b c = c + a * b := by
  revert a b c
  decide

private theorem fullWindow_finRule (hq : wolframRule 106 0 0 0 = 0) {s : FiniteConfiguration}
    (hs : s ≠ 0) : (finRule (wolframRule 106) hq s).fullWindow = window106 s.fullWindow := by
  funext j
  have hq1 : wolframRule 106 0 0 1 = 1 := by decide
  have h := leftWindow_finRule (f := wolframRule 106) (hq := hq) hq1 hs (W := j + 1) (j := j)
    (by omega)
  simp only [leftWindow, show j < j + 1 from by omega, ite_true, wolframRule106_apply] at h
  have e1 : (if 2 ≤ j then (if j - 2 < j + 1 then s (s.leftEnd + ((j - 2 : ℕ) : ℤ)) else 0)
      else 0) = if 2 ≤ j then s.fullWindow (j - 2) else 0 := by
    split_ifs <;> first | rfl | omega
  have e2 : (if 1 ≤ j then (if j - 1 < j + 1 then s (s.leftEnd + ((j - 1 : ℕ) : ℤ)) else 0)
      else 0) = if 1 ≤ j then s.fullWindow (j - 1) else 0 := by
    split_ifs <;> first | rfl | omega
  rw [e1, e2] at h
  exact h

private theorem iterate_fullWindow (hq : wolframRule 106 0 0 0 = 0) {s : FiniteConfiguration}
    (hs : s ≠ 0) :
    ∀ n : ℕ, (finRule (wolframRule 106) hq)^[n] s ≠ 0 ∧
      ((finRule (wolframRule 106) hq)^[n] s).fullWindow = window106^[n] s.fullWindow := by
  have hq1 : wolframRule 106 0 0 1 = 1 := by decide
  intro n
  induction n with
  | zero => exact ⟨hs, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨LocalRule.finRule_ne_zero_of_leftTap hq1 ih.1, by
      rw [fullWindow_finRule hq ih.1, ih.2]⟩

/-! ## The pattern and its copies -/

/-- The pattern of cells `0`, `1` and `3`. -/
private noncomputable abbrev pattern106 : FiniteConfiguration :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1

private theorem pattern_apply (x : ℤ) :
    pattern106 x =
      if x = 0 ∨ x = 1 ∨ x = 3 then 1 else 0 := by
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> first | omega | decide

private theorem pattern_ne_zero :
    pattern106 ≠ 0 := by
  intro h
  have := pattern_apply 0
  rw [h] at this
  simp at this

private theorem pattern_support :
    pattern106.support =
      {0, 1, 3} := by
  ext x
  rw [Finsupp.mem_support_iff, pattern_apply]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  split_ifs with h <;> simp [h]

private theorem pattern_leftEnd :
    pattern106.leftEnd = 0 := by
  have hne : pattern106.support.Nonempty := by
    rw [pattern_support]; exact ⟨0, by simp⟩
  rw [leftEnd_eq hne]
  apply le_antisymm
  · exact Finset.min'_le _ _ (by rw [pattern_support]; simp)
  · exact Finset.le_min' _ _ _ (fun y hy => by
      rw [pattern_support] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      omega)

private theorem pattern_diam :
    pattern106.diam = 4 := by
  have hne : pattern106.support.Nonempty := by
    rw [pattern_support]; exact ⟨0, by simp⟩
  rw [diam_eq' hne]
  have h1 : pattern106.support.min' hne = 0 := by
    rw [← leftEnd_eq hne]; exact pattern_leftEnd
  have h2 : pattern106.support.max' hne = 3 := by
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (fun y hy => by
        rw [pattern_support] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        omega)
    · exact Finset.le_max' _ _ (by rw [pattern_support]; simp)
  rw [h1, h2]
  rfl

private theorem pattern_fullWindow :
    pattern106.fullWindow =
      copiesLattice {0} := by
  funext j
  simp only [fullWindow, pattern_leftEnd, zero_add, pattern_apply, copiesLattice,
    Finset.mem_singleton]
  split_ifs <;> first | rfl | omega

private theorem div_mod_of_eq {m j k n : ℕ} (hk : k < m) (h : n = m * j + k) :
    n / m = j ∧ n % m = k := by
  subst h
  have hm : 0 < m := by omega
  exact ⟨by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hk, Nat.add_zero],
    by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]⟩

private theorem sum_indicator (m B : ℕ) (hm : 4 ≤ m) (i : ℤ) :
    (∑ j ∈ Finset.range B,
      if i - (m : ℤ) * j = 0 ∨ i - (m : ℤ) * j = 1 ∨ i - (m : ℤ) * j = 3 then (1 : ZMod 2)
      else 0) =
    if 0 ≤ i ∧ (i.toNat % m = 0 ∨ i.toNat % m = 1 ∨ i.toNat % m = 3) ∧ i.toNat / m < B then 1
    else 0 := by
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    simp only [Int.toNat_natCast, hi, true_and]
    have key : ∀ j : ℕ, ((n : ℤ) - (m : ℤ) * j = 0 ∨ (n : ℤ) - (m : ℤ) * j = 1 ∨
        (n : ℤ) - (m : ℤ) * j = 3) → n / m = j ∧ (n % m = 0 ∨ n % m = 1 ∨ n % m = 3) := by
      intro j hj
      have hmj : ((m * j : ℕ) : ℤ) = (m : ℤ) * j := by push_cast; rfl
      rcases hj with hj | hj | hj
      · have := div_mod_of_eq (m := m) (j := j) (k := 0) (n := n) (by omega) (by omega)
        exact ⟨this.1, Or.inl this.2⟩
      · have := div_mod_of_eq (m := m) (j := j) (k := 1) (n := n) (by omega) (by omega)
        exact ⟨this.1, Or.inr (Or.inl this.2)⟩
      · have := div_mod_of_eq (m := m) (j := j) (k := 3) (n := n) (by omega) (by omega)
        exact ⟨this.1, Or.inr (Or.inr this.2)⟩
    by_cases hc : (n % m = 0 ∨ n % m = 1 ∨ n % m = 3) ∧ n / m < B
    · rw [ite_eq_left hc, Finset.sum_eq_single_of_mem (n / m) (Finset.mem_range.2 hc.2)]
      · rw [ite_eq_left]
        have hd := Nat.div_add_mod n m
        have hmj : ((m * (n / m) : ℕ) : ℤ) = (m : ℤ) * ((n / m : ℕ) : ℤ) := by push_cast; rfl
        rcases hc.1 with h | h | h
        · left; omega
        · right; left; omega
        · right; right; omega
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

private theorem translate_apply' (c x : ℤ) (s : FiniteConfiguration) :
    FiniteConfiguration.translate c s x = s (x - c) := by
  have := Finsupp.mapDomain_apply_of_injective (add_left_injective c) s (x - c)
  simpa [FiniteConfiguration.translate] using this

private theorem copiesLattice_image (A B n : ℕ) (hA : 0 < A) :
    copiesLattice ((Finset.range B).image (A * ·)) n =
      if (n % (6 * A) = 0 ∨ n % (6 * A) = 1 ∨ n % (6 * A) = 3) ∧ n / (6 * A) < B then 1
      else 0 := by
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
  unfold copiesLattice
  rw [hmod, hdiv]
  apply if_congr _ rfl rfl
  rw [hmem]
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

private theorem copies_of_window {u : FiniteConfiguration} (hu : u ≠ 0) {A B G : ℕ}
    (hA : 0 < A) (hG : G + 4 ≤ 6 * A)
    (hw : u.fullWindow = copiesLattice ((Finset.range B).image (A * ·))) :
    Copies pattern106 u B G := by
  refine ⟨fun j => u.leftEnd + ((6 * A * j : ℕ) : ℤ), ?_, ?_⟩
  · intro j _
    rw [pattern_diam]
    have : 6 * A * (j + 1) = 6 * A * j + 6 * A := by ring
    push_cast [this]
    omega
  · ext x
    rw [Finsupp.finsetSum_apply]
    simp only [translate_apply', pattern_apply]
    have e : ∀ j : ℕ, x - (u.leftEnd + ((6 * A * j : ℕ) : ℤ)) =
        (x - u.leftEnd) - ((6 * A : ℕ) : ℤ) * j := by
      intro j
      push_cast
      ring
    simp only [e]
    rw [sum_indicator (6 * A) B (by omega) (x - u.leftEnd)]
    by_cases hx : x < u.leftEnd
    · rw [eq_zero_of_lt_leftEnd hu hx, ite_eq_right]
      omega
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x - u.leftEnd by omega)
      have hxn : x = u.leftEnd + n := by omega
      have h1 : u x = u.fullWindow n := by rw [hxn]; rfl
      rw [h1, hw, copiesLattice_image A B n hA, hn]
      simp only [Int.toNat_natCast, Int.natCast_nonneg, true_and]

/-- **The class of windows**: the windows starting with the pair `11` in which every run of two or
more set cells starts at a multiple of `3`. -/
def Rule106Class (w : ℕ → ZMod 2) : Prop :=
  w 0 = 1 ∧ w 1 = 1 ∧ ∀ j, w j = 0 → w (j + 1) = 1 → w (j + 2) = 1 → (j + 1) % 3 = 0

/-! ## The renormalization of the orbit of the pair -/

/-- The window map on cells indexed by all integers. -/
private def stepZ (x : ℤ → ZMod 2) : ℤ → ZMod 2 := fun z => x z + x (z - 2) * x (z - 1)

/-- The renormalization on cells indexed by all integers. -/
private def renormZ (f : ℤ → ZMod 2) : ℤ → ZMod 2 := fun z =>
  if z % 2 = 0 then (if (z / 2) % 3 = 1 then 0 else f (z / 2))
  else (if ((z + 1) / 2) % 3 = 1 then f ((z + 1) / 2) else 0)

/-- The translate of a window by `c` cells. -/
private def shiftZ (c : ℤ) (f : ℤ → ZMod 2) : ℤ → ZMod 2 := fun k => f (c + k)

/-- The class condition on cells indexed by all integers. -/
private def ClassZ (f : ℤ → ZMod 2) : Prop :=
  ∀ k, f k = 0 → f (k + 1) = 1 → f (k + 2) = 1 → (k + 1) % 3 = 0

private theorem stepZ_shift (c : ℤ) (f : ℤ → ZMod 2) :
    stepZ (shiftZ c f) = shiftZ c (stepZ f) := by
  funext k
  simp only [stepZ, shiftZ]
  rw [show c + k - 2 = c + (k - 2) by ring, show c + k - 1 = c + (k - 1) by ring]

private theorem stepZ_iterate_shift (n : ℕ) (c : ℤ) (f : ℤ → ZMod 2) :
    stepZ^[n] (shiftZ c f) = shiftZ c (stepZ^[n] f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, stepZ_shift]

private theorem renormZ_shift (a : ℤ) (f : ℤ → ZMod 2) :
    renormZ (shiftZ (3 * a) f) = shiftZ (6 * a) (renormZ f) := by
  funext z
  simp only [renormZ, shiftZ]
  have h1 : (6 * a + z) % 2 = z % 2 := by omega
  have h2 : (6 * a + z) / 2 = 3 * a + z / 2 := by omega
  have h3 : (6 * a + z + 1) / 2 = 3 * a + (z + 1) / 2 := by omega
  have h4 : (3 * a + z / 2) % 3 = (z / 2) % 3 := by omega
  have h5 : (3 * a + (z + 1) / 2) % 3 = ((z + 1) / 2) % 3 := by omega
  rw [h1, h2, h4, h3, h5]

private theorem classZ_shift (a : ℤ) {f : ℤ → ZMod 2} (hf : ClassZ f) :
    ClassZ (shiftZ (3 * a) f) := by
  intro k h0 h1 h2
  have := hf (3 * a + k) h0 (by simpa [shiftZ, add_assoc] using h1)
    (by simpa [shiftZ, add_assoc] using h2)
  omega

set_option synthInstance.maxSize 1000 in
private theorem local_four (G : ℤ → ZMod 2) (hG : ClassZ G) (r : ℤ) (hr0 : 0 ≤ r) (hr : r < 6) :
    stepZ^[4] (renormZ G) r = renormZ (stepZ G) r := by
  have c : ∀ k : ℤ, G k = 0 → G (k + 1) = 1 → G (k + 2) = 1 → (k + 1) % 3 = 0 := hG
  have c3 := c (-5)
  have c4 := c (-4)
  have c5 := c (-3)
  have c6 := c (-2)
  have c7 := c (-1)
  have c8 := c 0
  have c9 := c 1
  interval_cases r <;>
  simp only [stepZ, renormZ, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    Int.reduceAdd, Int.reduceSub, Int.reduceMod, Int.reduceDiv, Int.reduceNeg, ↓reduceIte]
    at c3 c4 c5 c6 c7 c8 c9 ⊢
  all_goals generalize G (-5) = x0 at *
  all_goals generalize G (-4) = x1 at *
  all_goals generalize G (-3) = x2 at *
  all_goals generalize G (-2) = x3 at *
  all_goals generalize G (-1) = x4 at *
  all_goals generalize G 0 = x5 at *
  all_goals generalize G 1 = x6 at *
  all_goals generalize G 2 = x7 at *
  all_goals generalize G 3 = x8 at *
  all_goals clear hG c
  all_goals revert c3 c4 c5 c6 c7 c8 c9
  all_goals revert x0 x1 x2 x3 x4 x5 x6 x7 x8
  all_goals decide +kernel


set_option maxHeartbeats 1000000 in
-- Twenty-four cases, each a `decide` over ten cells, together exceed the default budget.
set_option synthInstance.maxSize 1000 in
private theorem local_class (G : ℤ → ZMod 2) (hG : ClassZ G) (n : ℕ) (hn : n < 4) (r : ℤ)
    (hr0 : 0 ≤ r) (hr : r < 6) :
    stepZ^[n] (renormZ G) r = 0 → stepZ^[n] (renormZ G) (r + 1) = 1 →
      stepZ^[n] (renormZ G) (r + 2) = 1 → (r + 1) % 3 = 0 := by
  have c : ∀ k : ℤ, G k = 0 → G (k + 1) = 1 → G (k + 2) = 1 → (k + 1) % 3 = 0 := hG
  have c3 := c (-5)
  have c4 := c (-4)
  have c5 := c (-3)
  have c6 := c (-2)
  have c7 := c (-1)
  have c8 := c 0
  have c9 := c 1
  have c10 := c 2
  have c11 := c 3
  interval_cases n <;> interval_cases r <;>
  simp only [stepZ, renormZ, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    Int.reduceAdd, Int.reduceSub, Int.reduceMod, Int.reduceDiv, Int.reduceNeg, ↓reduceIte]
    at c3 c4 c5 c6 c7 c8 c9 c10 c11 ⊢
  all_goals generalize G (-5) = x0 at *
  all_goals generalize G (-4) = x1 at *
  all_goals generalize G (-3) = x2 at *
  all_goals generalize G (-2) = x3 at *
  all_goals generalize G (-1) = x4 at *
  all_goals generalize G 0 = x5 at *
  all_goals generalize G 1 = x6 at *
  all_goals generalize G 2 = x7 at *
  all_goals generalize G 3 = x8 at *
  all_goals generalize G 4 = x9 at *
  all_goals generalize G 5 = x10 at *
  all_goals clear hG c
  all_goals revert c3 c4 c5 c6 c7 c8 c9 c10 c11
  all_goals revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  all_goals decide +kernel

private theorem stepZ_renormZ_shift (n : ℕ) (a : ℤ) (f : ℤ → ZMod 2) :
    stepZ^[n] (renormZ (shiftZ (3 * a) f)) = shiftZ (6 * a) (stepZ^[n] (renormZ f)) := by
  rw [renormZ_shift, stepZ_iterate_shift]

private theorem classZ_iterate {f : ℤ → ZMod 2} (hf : ClassZ f) {n : ℕ} (hn : n < 4) :
    ClassZ (stepZ^[n] (renormZ f)) := by
  intro k h0 h1 h2
  have hG := classZ_shift (k / 6) hf
  have e := stepZ_renormZ_shift n (k / 6) f
  have key := local_class _ hG n hn (k % 6) (by omega) (by omega)
  have q0 := congrFun e (k % 6)
  have q1 := congrFun e (k % 6 + 1)
  have q2 := congrFun e (k % 6 + 2)
  simp only [shiftZ] at q0 q1 q2
  rw [q0] at key
  rw [q1] at key
  rw [q2] at key
  rw [show 6 * (k / 6) + k % 6 = k by omega] at key
  rw [show 6 * (k / 6) + (k % 6 + 1) = k + 1 by omega] at key
  rw [show 6 * (k / 6) + (k % 6 + 2) = k + 2 by omega] at key
  have := key h0 h1 h2
  omega

private theorem local_four_all {f : ℤ → ZMod 2} (hf : ClassZ f) (z : ℤ) :
    stepZ^[4] (renormZ f) z = renormZ (stepZ f) z := by
  have hG := classZ_shift (z / 6) hf
  have e := stepZ_renormZ_shift 4 (z / 6) f
  have key := local_four _ hG (z % 6) (by omega) (by omega)
  have q0 := congrFun e (z % 6)
  simp only [shiftZ] at q0
  rw [q0] at key
  rw [show 6 * (z / 6) + z % 6 = z by omega] at key
  rw [key]
  have e2 : renormZ (stepZ (shiftZ (3 * (z / 6)) f)) =
      shiftZ (6 * (z / 6)) (renormZ (stepZ f)) := by
    rw [stepZ_shift, renormZ_shift]
  have q1 := congrFun e2 (z % 6)
  simp only [shiftZ] at q1
  rw [q1, show 6 * (z / 6) + z % 6 = z by omega]

/-- A window extended by clear cells below `0`, indexed by all integers. -/
private def ex (v : ℕ → ZMod 2) (z : ℤ) : ZMod 2 := if 0 ≤ z then v z.toNat else 0

private theorem ex_natCast (v : ℕ → ZMod 2) (n : ℕ) : ex v n = v n := by simp [ex]

private theorem ex_neg (v : ℕ → ZMod 2) {z : ℤ} (h : z < 0) : ex v z = 0 := by
  simp [ex]
  omega

private theorem ex_window106 (v : ℕ → ZMod 2) : ex (window106 v) = stepZ (ex v) := by
  funext z
  by_cases hz : 0 ≤ z
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    have e2 : ex v ((n : ℤ) - 2) = if 2 ≤ n then v (n - 2) else 0 := by
      by_cases h : 2 ≤ n
      · rw [show ((n : ℤ) - 2) = ((n - 2 : ℕ) : ℤ) by omega, ex_natCast]
        simp [h]
      · rw [ex_neg _ (by omega)]
        simp [h]
    have e1 : ex v ((n : ℤ) - 1) = if 1 ≤ n then v (n - 1) else 0 := by
      by_cases h : 1 ≤ n
      · rw [show ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) by omega, ex_natCast]
        simp [h]
      · rw [ex_neg _ (by omega)]
        simp [h]
    simp only [stepZ, ex_natCast, e1, e2, window106]
  · have h1 : ex (window106 v) z = 0 := ex_neg _ (by omega)
    have h2 : ex v z = 0 := ex_neg _ (by omega)
    have h3 : ex v (z - 2) = 0 := ex_neg _ (by omega)
    simp only [stepZ, h1, h2, h3, zero_mul, add_zero]

private theorem ex_renorm (w : ℕ → ZMod 2) : ex (renorm w) = renormZ (ex w) := by
  funext z
  by_cases hz : 0 ≤ z
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    have a1 : ex w ((n : ℤ) / 2) = w (n / 2) := by
      rw [show ((n : ℤ) / 2) = ((n / 2 : ℕ) : ℤ) by omega, ex_natCast]
    have a2 : ex w (((n : ℤ) + 1) / 2) = w ((n + 1) / 2) := by
      rw [show (((n : ℤ) + 1) / 2) = (((n + 1) / 2 : ℕ) : ℤ) by omega, ex_natCast]
    simp only [ex_natCast, renorm, renormZ, a1, a2]
    by_cases hp : n % 2 = 0
    · have : (n : ℤ) % 2 = 0 := by omega
      simp only [hp, this, ite_true]
      by_cases hq : (n / 2) % 3 = 1
      · have : ((n : ℤ) / 2) % 3 = 1 := by omega
        simp [hq, this]
      · have : ¬ (((n : ℤ) / 2) % 3 = 1) := by omega
        simp [hq, this]
    · have : ¬ ((n : ℤ) % 2 = 0) := by omega
      simp only [hp, this, ite_false]
      by_cases hq : ((n + 1) / 2) % 3 = 1
      · have : (((n : ℤ) + 1) / 2) % 3 = 1 := by omega
        simp [hq, this]
      · have : ¬ ((((n : ℤ) + 1) / 2) % 3 = 1) := by omega
        simp [hq, this]
  · have h1 : ex (renorm w) z = 0 := ex_neg _ (by omega)
    rw [h1]
    unfold renormZ
    split_ifs with h2 h3 h4
    · rfl
    · rw [ex_neg _ (by omega)]
    · rw [ex_neg _ (by omega)]
    · rfl

private theorem ex_iterate (n : ℕ) (v : ℕ → ZMod 2) : ex (window106^[n] v) = stepZ^[n] (ex v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ex_window106, ih]

private theorem classZ_ex {w : ℕ → ZMod 2} (hw : Rule106Class w) : ClassZ (ex w) := by
  intro k h0 h1 h2
  by_cases hk : k < -1
  · rw [ex_neg _ (by omega)] at h1
    exact absurd h1 (by decide)
  · by_cases hk' : k = -1
    · omega
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
      rw [ex_natCast] at h0
      rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, ex_natCast] at h1
      rw [show ((j : ℤ) + 2) = ((j + 2 : ℕ) : ℤ) by push_cast; ring, ex_natCast] at h2
      have := hw.2.2 j h0 h1 h2
      omega

/-- **Four steps commute with the renormalization on the class**: for a window in `Rule106Class`,
four steps of `window106` on the renormalized window are the renormalization of one step. -/
theorem renorm_window106_four {w : ℕ → ZMod 2} (hw : Rule106Class w) :
    window106^[4] (renorm w) = renorm (window106 w) := by
  funext q
  have h := local_four_all (classZ_ex hw) q
  rw [← ex_natCast (window106^[4] (renorm w)) q, ← ex_natCast (renorm (window106 w)) q,
    ex_iterate, ex_renorm, ex_renorm, ex_window106]
  exact h

private theorem window106_iterate_zero (n : ℕ) (u : ℕ → ZMod 2) : window106^[n] u 0 = u 0 := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih]; simp [window106]

private theorem window106_iterate_one (n : ℕ) (u : ℕ → ZMod 2) : window106^[n] u 1 = u 1 := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih]; simp [window106]

/-- **The class is kept**: for a window in `Rule106Class`, each of the first four iterates of its
renormalization is in `Rule106Class`. -/
theorem rule106Class_renorm_iterate {w : ℕ → ZMod 2} (hw : Rule106Class w) {r : ℕ} (hr : r < 4) :
    Rule106Class (window106^[r] (renorm w)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [window106_iterate_zero]
    simp [renorm, hw.1]
  · rw [window106_iterate_one]
    have : renorm w 1 = w 1 := by simp [renorm]
    rw [this, hw.2.1]
  · intro j h0 h1 h2
    have hc := classZ_iterate (classZ_ex hw) hr
    rw [← ex_renorm, ← ex_iterate] at hc
    have := hc j (by rw [ex_natCast]; exact h0)
      (by rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, ex_natCast]; exact h1)
      (by rw [show ((j : ℤ) + 2) = ((j + 2 : ℕ) : ℤ) by push_cast; ring, ex_natCast]; exact h2)
    omega

/-- The pair `11` is in the class. -/
private theorem rule106Class_pair : Rule106Class (pairLattice {0}) := by
  refine ⟨by simp [pairLattice], by simp [pairLattice], ?_⟩
  intro j h0 h1 h2
  unfold pairLattice at h0 h1 h2
  split_ifs at h0 h1 h2
  all_goals simp_all
  all_goals omega

private theorem renorm_pair : renorm (pairLattice {0}) = pairLattice {0} := by
  rw [renorm_pairLattice]
  simp

private theorem orbit_joint (m : ℕ) :
    Rule106Class (window106^[m] (pairLattice {0})) ∧
      window106^[4 * m] (pairLattice {0}) = renorm (window106^[m] (pairLattice {0})) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hR : window106^[4 * m] (pairLattice {0}) = renorm (window106^[m] (pairLattice {0})) := by
      rcases m with _ | u
      · exact renorm_pair.symm
      · obtain ⟨hc, hr⟩ := ih u (by omega)
        rw [show 4 * (u + 1) = 4 + 4 * u by ring, Function.iterate_add_apply, hr,
          renorm_window106_four hc, Function.iterate_succ_apply']
    refine ⟨?_, hR⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact rule106Class_pair
    · obtain ⟨hc, hr⟩ := ih (m / 4) (by omega)
      have e : window106^[m] (pairLattice {0}) =
          window106^[m % 4] (window106^[4 * (m / 4)] (pairLattice {0})) := by
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      rw [e, hr]
      exact rule106Class_renorm_iterate hc (Nat.mod_lt _ (by norm_num))

/-- **The renormalization statement holds**: from the pair `11`, `4 * u` steps of rule `106`'s
window map give the renormalization of the window after `u` steps. -/
theorem rule106Renorm : Rule106Renorm := fun u => (orbit_joint u).2

/-- **The class condition is needed in the commutation of four steps**: at the window whose set
cells are `0`, `1`, `4` and `5`, a run of two starting at cell `4`, outside `Rule106Class`, the
two sides of the commutation differ at cell `12`, clear on the left and set on the right. -/
theorem not_renorm_window106_four_of_offphase (w : ℕ → ZMod 2)
    (hw : ∀ j, w j = if j ∈ ({0, 1, 4, 5} : Finset ℕ) then 1 else 0) :
    ¬ Rule106Class w ∧ window106^[4] (renorm w) 12 = 0 ∧ renorm (window106 w) 12 = 1 := by
  obtain rfl : w = fun j => if j ∈ ({0, 1, 4, 5} : Finset ℕ) then 1 else 0 := funext hw
  refine ⟨fun h => ?_, by decide +kernel, by decide +kernel⟩
  have := h.2.2 3 (by decide) (by decide) (by decide)
  exact absurd this (by decide)

private theorem pair0_eq_block : pairLattice {0} = blockLattice 12 {0, 1} {0} := by
  funext i
  unfold pairLattice blockLattice
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply if_congr _ rfl rfl
  omega

private theorem blockLattice_big {S : Finset ℕ} {i : ℕ} (h : 12 ≤ i) :
    blockLattice 12 S {0} i = 0 := by
  unfold blockLattice
  rw [ite_eq_right]
  simp only [Finset.mem_singleton, not_and]
  intro _
  omega

private theorem orbit_block (n : ℕ) (hS : ∀ k < n, ∀ r ∈ (blockStep 12)^[k] ({0, 1} : Finset ℕ),
    r + 2 < 12) :
    window106^[n] (pairLattice {0}) = blockLattice 12 ((blockStep 12)^[n] {0, 1}) {0} := by
  rw [pair0_eq_block]
  exact window106_iterate_blockLattice (by norm_num) _ _ n hS

/-- **The commutation of four steps is met with content**: the sixth window of the orbit of the
pair, `window106^[5] (pairLattice {0})`, with cells `0`, `1`, `2` and `4` set, is in
`Rule106Class`, and both sides of the commutation have cells `0`, `1`, `6` and `7` set and all
others clear. -/
theorem renorm_window106_four_nonvacuous :
    Rule106Class (window106^[5] (pairLattice {0})) ∧
      (∀ j, window106^[5] (pairLattice {0}) j = if j ∈ ({0, 1, 2, 4} : Finset ℕ) then 1 else 0) ∧
      (∀ j, window106^[4] (renorm (window106^[5] (pairLattice {0}))) j =
        if j ∈ ({0, 1, 6, 7} : Finset ℕ) then 1 else 0) ∧
      (∀ j, renorm (window106 (window106^[5] (pairLattice {0}))) j =
        if j ∈ ({0, 1, 6, 7} : Finset ℕ) then 1 else 0) := by
  have o5 : window106^[5] (pairLattice {0}) = blockLattice 12 {0, 1, 2, 4} {0} := by
    rw [orbit_block 5 (by decide)]
    rw [show (blockStep 12)^[5] ({0, 1} : Finset ℕ) = {0, 1, 2, 4} from by decide]
  have o6 : window106 (window106^[5] (pairLattice {0})) = blockLattice 12 {0, 1, 3, 4} {0} := by
    rw [← Function.iterate_succ_apply' window106, orbit_block 6 (by decide)]
    rw [show (blockStep 12)^[6] ({0, 1} : Finset ℕ) = {0, 1, 3, 4} from by decide]
  have hr : ∀ j, renorm (window106 (window106^[5] (pairLattice {0}))) j =
      if j ∈ ({0, 1, 6, 7} : Finset ℕ) then 1 else 0 := by
    intro j
    rw [o6]
    by_cases hj : j < 30
    · interval_cases j <;> decide +kernel
    · have hn : j ∉ ({0, 1, 6, 7} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [ite_eq_right hn]
      unfold renorm
      split_ifs <;> first | rfl | exact blockLattice_big (by omega)
  have hc := (orbit_joint 5).1
  refine ⟨hc, fun j => ?_, fun j => ?_, hr⟩
  · rw [o5]
    by_cases hj : j < 12
    · interval_cases j <;> decide +kernel
    · rw [blockLattice_big (by omega), ite_eq_right]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  · rw [renorm_window106_four hc]
    exact hr j


/-! ## The sink -/

private theorem submasks_pow (a m : ℕ) :
    submasks (2 ^ a * m) = (submasks m).image (2 ^ a * ·) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by ring
    rw [e, submasks_double, ih, Finset.image_image]
    congr 1
    funext x
    simp only [Function.comp]
    ring

private theorem submasks_mersenne (b : ℕ) : submasks (2 ^ b - 1) = Finset.range (2 ^ b) := by
  induction b with
  | zero => simp [submasks_zero]
  | succ b ih =>
    have hp : 0 < 2 ^ b := Nat.two_pow_pos b
    have e : 2 ^ (b + 1) - 1 = 2 * (2 ^ b - 1) + 1 := by
      rw [pow_succ]
      omega
    rw [e, submasks_double_succ, ih]
    ext n
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, pow_succ]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> omega
    · intro hn
      by_cases hpar : n % 2 = 0
      · exact Or.inl ⟨n / 2, by omega, by omega⟩
      · exact Or.inr ⟨n / 2, by omega, by omega⟩

private theorem fullWindow_iterate_pattern (h1 : Rule106Renorm) (h2 : Rule106Step24)
    (h3 : Rule106TwoSteps) (s : ℕ) :
    window106^[24 * quadDigits s] (copiesLattice {0}) = copiesLattice (submasks s) := by
  rw [← h3 {0}, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply,
    iterate_pairLattice h1 h2 s, h3]

/-- **Rule `106` reproduces a pattern**, from three statements about rule `106`'s window as
hypotheses: the pair `11` renormalizes four steps to one, twenty-four steps double a pair lattice
into its successors, and two steps turn pairs into copies of the pattern of cells `0`, `1` and
`3`. -/
theorem reproduces_wolfram106_of_window (h1 : Rule106Renorm) (h2 : Rule106Step24)
    (h3 : Rule106TwoSteps) :
    ∀ (hq : wolframRule 106 0 0 0 = 0),
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1) := by
  intro hq
  refine ⟨pattern_ne_zero, fun N G => ?_⟩
  have hB : N ≤ 2 ^ N := (Nat.lt_two_pow_self).le
  have hA : G + 4 ≤ 6 * 2 ^ (G + 4) := by
    have := Nat.lt_two_pow_self (n := G + 4)
    omega
  have hApos : 0 < 2 ^ (G + 4) := Nat.two_pow_pos _
  refine ⟨24 * quadDigits ((2 ^ N - 1) * 2 ^ (G + 4)), 2 ^ N, hB, ?_⟩
  obtain ⟨hne, hfw⟩ := iterate_fullWindow hq pattern_ne_zero
    (24 * quadDigits ((2 ^ N - 1) * 2 ^ (G + 4)))
  refine copies_of_window hne hApos hA ?_
  rw [hfw, pattern_fullWindow, fullWindow_iterate_pattern h1 h2 h3, mul_comm, submasks_pow,
    submasks_mersenne]

/-- **Rule `120` reproduces a pattern**, from the same three statements: rule `120` is the mirror
of rule `106`, so it reproduces the reflection of the pattern rule `106` reproduces. -/
theorem reproduces_wolfram120_of_window (h1 : Rule106Renorm) (h2 : Rule106Step24)
    (h3 : Rule106TwoSteps) :
    ∀ (hq : wolframRule 120 0 0 0 = 0),
      Reproduces (finRule (wolframRule 120) hq)
        (FiniteConfiguration.reflect
          (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1)) := by
  intro hq
  have hq106 : wolframRule 106 0 0 0 = 0 := by decide
  have hm : mirrorRule (wolframRule 106) = wolframRule 120 := by
    funext a b c
    revert a b c
    decide
  exact reproduces_congr hm (by decide) hq
    (reproducesReflect _ hq106 _ (reproduces_wolfram106_of_window h1 h2 h3 hq106))

/-- **Rule `106` reproduces a pattern**: the pattern of cells `0`, `1` and `3`. -/
theorem reproduces_wolfram106 :
    ∀ (hq : wolframRule 106 0 0 0 = 0),
      Reproduces (finRule (wolframRule 106) hq)
        (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1) :=
  reproduces_wolfram106_of_window rule106Renorm rule106Step24 rule106TwoSteps

/-- **Rule `120` reproduces a pattern**: the reflection of the pattern of cells `0`, `1` and `3`,
the mirror image of the pattern rule `106` reproduces. -/
theorem reproduces_wolfram120 :
    ∀ (hq : wolframRule 120 0 0 0 = 0),
      Reproduces (finRule (wolframRule 120) hq)
        (FiniteConfiguration.reflect
          (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1)) :=
  reproduces_wolfram120_of_window rule106Renorm rule106Step24 rule106TwoSteps

/-! ## The chain at the first doubling -/

/-- The window whose cell `j` is bit `j` of `n`. -/
private def winOfNat (n : ℕ) : ℕ → ZMod 2 := fun j => if n.testBit j then 1 else 0

/-- One step of rule `106`'s window map on the bits of a number. -/
private def stepNat (n : ℕ) : ℕ := n ^^^ ((n <<< 2) &&& (n <<< 1))

private theorem window106_winOfNat (n : ℕ) : window106 (winOfNat n) = winOfNat (stepNat n) := by
  funext j
  unfold window106 winOfNat stepNat
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
  by_cases c2 : 2 ≤ j
  · have c1 : 1 ≤ j := by omega
    simp only [c1, c2, decide_true, Bool.true_and, ite_true]
    cases n.testBit j <;> cases n.testBit (j - 1) <;> cases n.testBit (j - 2) <;> decide
  · by_cases c1 : 1 ≤ j
    · simp only [c1, c2, decide_true, decide_false, Bool.true_and, Bool.false_and,
        ite_true, ite_false]
      cases n.testBit j <;> cases n.testBit (j - 1) <;> decide
    · simp only [c1, c2, decide_false, Bool.false_and, ite_false]
      cases n.testBit j <;> decide

private theorem iterate_winOfNat (n m : ℕ) :
    window106^[n] (winOfNat m) = winOfNat (stepNat^[n] m) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, window106_winOfNat, ih]

private theorem winOfNat_apply_of_lt {n L j : ℕ} (h : n < 2 ^ L) (hj : L ≤ j) :
    winOfNat n j = 0 := by
  have : n < 2 ^ j := lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hj)
  simp [winOfNat, Nat.testBit_eq_false_of_lt this]

private theorem stepNat_iterate_24 : stepNat^[24] 11 = 715 := by
  decide +kernel

private theorem copiesLattice_zero_eq : copiesLattice {0} = winOfNat 11 := by
  funext j
  by_cases hj : j < 12
  · interval_cases j <;> decide
  · rw [winOfNat_apply_of_lt (L := 4) (by norm_num) (by omega)]
    simp only [copiesLattice, Finset.mem_singleton]
    exact ite_eq_right (fun h => by omega)

private theorem copiesLattice_pair_eq : copiesLattice {0, 1} = winOfNat 715 := by
  funext j
  by_cases hj : j < 12
  · interval_cases j <;> decide
  · rw [winOfNat_apply_of_lt (L := 10) (by norm_num) (by omega)]
    simp only [copiesLattice, Finset.mem_insert, Finset.mem_singleton]
    exact ite_eq_right (fun h => by omega)

/-- **The chain at the first doubling**: the full window of the twenty-fourth iterate of rule `106`
from the pattern of cells `0`, `1` and `3` is the copy lattice of `{0, 1}`, two copies of the
pattern with their cells `0`, `1`, `3`, `6`, `7` and `9` set and every other cell clear. -/
theorem copies_window106_nonvacuous (hq : wolframRule 106 0 0 0 = 0) :
    (finRule (wolframRule 106) hq)^[24]
        (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1) ≠ 0 ∧
      ((finRule (wolframRule 106) hq)^[24]
        (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1)).fullWindow =
        copiesLattice {0, 1} ∧
      ∀ j : ℕ, ((finRule (wolframRule 106) hq)^[24]
        (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1)).fullWindow j =
        if j ∈ ({0, 1, 3, 6, 7, 9} : Finset ℕ) then 1 else 0 := by
  obtain ⟨hne, hfw⟩ := iterate_fullWindow hq pattern_ne_zero 24
  have key : ((finRule (wolframRule 106) hq)^[24] pattern106).fullWindow = winOfNat 715 := by
    rw [hfw, pattern_fullWindow, copiesLattice_zero_eq, iterate_winOfNat, stepNat_iterate_24]
  refine ⟨hne, by rw [key, copiesLattice_pair_eq], fun j => ?_⟩
  rw [key]
  by_cases hj : j < 10
  · interval_cases j <;> decide
  · rw [winOfNat_apply_of_lt (L := 10) (by norm_num) (by omega)]
    have hn : j ∉ ({0, 1, 3, 6, 7, 9} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (ite_eq_right hn).symm

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram106_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram106_of_window

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram120_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram120_of_window

set_option linter.style.longLine false in
/-- info: 'ECA.copies_window106_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.copies_window106_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.rule106TwoSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106TwoSteps

set_option linter.style.longLine false in
/-- info: 'ECA.rule106Step24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106Step24

set_option linter.style.longLine false in
/-- info: 'ECA.rule106Step24_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106Step24_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_window106_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_window106_four

set_option linter.style.longLine false in
/-- info: 'ECA.rule106Class_renorm_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106Class_renorm_iterate

set_option linter.style.longLine false in
/-- info: 'ECA.rule106Renorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.rule106Renorm

set_option linter.style.longLine false in
/-- info: 'ECA.not_renorm_window106_four_of_offphase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_renorm_window106_four_of_offphase

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram106' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram106

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_wolfram120' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_wolfram120

set_option linter.style.longLine false in
/-- info: 'ECA.renorm_window106_four_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.renorm_window106_four_nonvacuous
