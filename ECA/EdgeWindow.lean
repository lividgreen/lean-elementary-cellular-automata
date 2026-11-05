module

public import ECA.ReproductionBracket
public import ECA.EndpointClasses

/-!
# Rule `54` reproduces no pattern
([RuleSpace] §5)

At a quiescent rule with `f 0 0 1 = 1` the leftmost set cell of a nonzero finite state moves left
exactly one cell a step, so the window of width `W` read from the image's leftmost set cell is a
function of the state's window alone. At rule `54` every such window is, from `5 * ⌈W / 4⌉` steps
on, a string of blocks of four cells `1000` and `1110`. A pattern reproduced by rule `54` would have
an iterate that is two or more copies at gap `4`, whose window of width `diam p + 4` is the
pattern's own window followed by four clear cells; closure of windows makes that window recur at
every multiple of the iterate, and the block form forbids four clear cells in a row at a block
boundary, so rule `54` reproduces no pattern, with no hypothesis left.

## Main results

* `FiniteConfiguration.leftEnd` / `FiniteConfiguration.leftWindow` — the leftmost set cell and the
  window of a given width read from it.
* `FiniteConfiguration.leftEnd_finRule` — the leftmost set cell of the image moves left one cell.
* `FiniteConfiguration.leftWindow_finRule` — the window recurrence: cell `j` of the image's window
  is the rule applied to cells `j - 2`, `j - 1` and `j` of the state's window.
* `leftWindowClosed` — closure of windows, from the recurrence;
  `leftWindow_finRule_nonvacuous` — the recurrence's hypotheses meet at rule `54`;
  `not_leftWindowClosed_wolfram4` — the hypothesis `f 0 0 1 = 1` is load-bearing.
* `EtherBlocks` — the block form of the window.
* `etherBlocksLate54` — the windows of rule `54` are blocks from `5 * ((W + 3) / 4)` steps on, by
  induction over blocks of four cells; `not_etherBlocks_early_wolfram54` — the threshold is not
  vacuous: the window of width `8` of the seventh iterate from a three-cell state is not blocks.
* `LeftWindowClosed` / `EtherBlocksLate54` / `LeftWindowCopies` — the three statements the sink
  consumes, as propositions.
* `leftWindowCopies` — copies read the pattern's window, the third of those statements;
  `leftWindowCopies_nonvacuous` — its hypotheses meet at the pattern of cells `0` and `2`.
* `not_reproduces_wolfram54` — rule `54` reproduces no pattern, unconditionally;
  `not_reproduces_wolfram54_of_window` — the same from the three statements as hypotheses.
* `etherBlocks_single_wolfram54` — the window of width `8` of the tenth iterate of rule `54` from
  the single cell satisfies the block form; `not_etherBlocks_single_wolfram30` — rule `30` does not.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-! ## The window read from the leftmost set cell -/

/-- **The leftmost set cell** of a finite state: the least element of its support, and `0` at the
zero state. -/
noncomputable def FiniteConfiguration.leftEnd (s : FiniteConfiguration) : ℤ :=
  if h : s.support.Nonempty then s.support.min' h else 0

/-- **The window of width `W`** read rightwards from the leftmost set cell: cell `j` is the
state's value at `leftEnd + j` for `j < W`, and clear beyond the width. -/
noncomputable def FiniteConfiguration.leftWindow (s : FiniteConfiguration) (W : ℕ) :
    ℕ → ZMod 2 :=
  fun j => if j < W then s (s.leftEnd + j) else 0

/-- **The block form of a window of width `W`**: every block of four cells from cell `0` is `1000`
or `1110`, the two rows of the ether of rule `54`, each block at its own phase; a top block cut
short is a prefix of one. -/
def EtherBlocks (W : ℕ) (w : ℕ → ZMod 2) : Prop :=
  ∀ j < W, (j % 4 = 0 → w j = 1) ∧ (j % 4 = 3 → w j = 0) ∧ (j % 4 = 1 → j + 1 < W → w j = w (j + 1))

/-! ## The three statements the sink consumes -/

/-- **Closure of windows**: at a quiescent rule with `f 0 0 1 = 1`, two nonzero states with equal
windows of width `W` have nonzero images with equal windows of width `W`. -/
def LeftWindowClosed : Prop :=
  ∀ (f : LocalRule) (hq : f 0 0 0 = 0), f 0 0 1 = 1 → ∀ (W : ℕ) (s s' : FiniteConfiguration),
    s ≠ 0 → s' ≠ 0 → s.leftWindow W = s'.leftWindow W →
      finRule f hq s ≠ 0 ∧ (finRule f hq s).leftWindow W = (finRule f hq s').leftWindow W

/-- **The windows of rule `54` are blocks late**: from `5 * ((W + 3) / 4)` steps on, the window of
width `W` of every iterate of a nonzero state under rule `54` has the block form. -/
def EtherBlocksLate54 : Prop :=
  ∀ (hq : wolframRule 54 0 0 0 = 0) (s : FiniteConfiguration), s ≠ 0 → ∀ W n : ℕ,
    5 * ((W + 3) / 4) ≤ n → EtherBlocks W (((finRule (wolframRule 54) hq)^[n] s).leftWindow W)

/-- **Copies read the pattern's window**: a state that is `k ≥ 1` copies of a nonzero pattern `p` at
gap `G` has the window of width `diam p + G` of `p`. -/
def LeftWindowCopies : Prop :=
  ∀ (p s : FiniteConfiguration) (k G : ℕ), p ≠ 0 → 1 ≤ k → Copies p s k G →
    s.leftWindow (p.diam + G) = p.leftWindow (p.diam + G)

/-! ## The sink -/

private theorem FiniteConfiguration.leftEnd_eq {s : FiniteConfiguration}
    (hne : s.support.Nonempty) : s.leftEnd = s.support.min' hne := by
  simp [leftEnd, hne]

private theorem FiniteConfiguration.diam_eq' {s : FiniteConfiguration}
    (hne : s.support.Nonempty) :
    s.diam = (s.support.max' hne - s.support.min' hne).toNat + 1 := by
  simp [diam, hne]

private theorem FiniteConfiguration.one_le_diam {p : FiniteConfiguration} (hp : p ≠ 0) :
    1 ≤ p.diam := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  rw [diam_eq' hne]
  omega

private theorem FiniteConfiguration.leftWindow_eq_zero_of_diam_le {p : FiniteConfiguration}
    (hp : p ≠ 0) {W j : ℕ} (h1 : p.diam ≤ j) (h2 : j < W) : p.leftWindow W j = 0 := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmm := Finset.min'_le_max' p.support hne
  simp only [leftWindow, h2, ite_true]
  by_contra hc
  have hmem : p.leftEnd + (j : ℤ) ∈ p.support := Finsupp.mem_support_iff.mpr hc
  have hle : p.leftEnd + (j : ℤ) ≤ p.support.max' hne := Finset.le_max' p.support _ hmem
  rw [diam_eq' hne] at h1
  rw [leftEnd_eq hne] at hle
  omega

private theorem iterate_closed (h1 : LeftWindowClosed) (hq : wolframRule 54 0 0 0 = 0)
    (hq1 : wolframRule 54 0 0 1 = 1) (W : ℕ) :
    ∀ (j : ℕ) (a b : FiniteConfiguration), a ≠ 0 → b ≠ 0 → a.leftWindow W = b.leftWindow W →
      (finRule (wolframRule 54) hq)^[j] a ≠ 0 ∧
        ((finRule (wolframRule 54) hq)^[j] a).leftWindow W =
          ((finRule (wolframRule 54) hq)^[j] b).leftWindow W := by
  intro j
  induction j with
  | zero => intro a b ha _ h; exact ⟨ha, h⟩
  | succ j ih =>
    intro a b ha hb h
    obtain ⟨ha', h'⟩ := h1 (wolframRule 54) hq hq1 W a b ha hb h
    have hb' := (h1 (wolframRule 54) hq hq1 W b b hb hb rfl).1
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih _ _ ha' hb' h'

private theorem FiniteConfiguration.eq_zero_of_lt_leftEnd {s : FiniteConfiguration} (hs : s ≠ 0)
    {x : ℤ} (hx : x < s.leftEnd) : s x = 0 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  rw [leftEnd_eq hne] at hx
  by_contra hc
  have hmem : x ∈ s.support := Finsupp.mem_support_iff.mpr hc
  have := Finset.min'_le s.support x hmem
  omega

/-- **The leftmost set cell moves left one cell a step**: at a quiescent rule with `f 0 0 1 = 1`
the leftmost set cell of the image of a nonzero state is one cell left of the state's. -/
theorem FiniteConfiguration.leftEnd_finRule {f : LocalRule} {hq : f 0 0 0 = 0} (h : f 0 0 1 = 1)
    {s : FiniteConfiguration} (hs : s ≠ 0) : (finRule f hq s).leftEnd = s.leftEnd - 1 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hne' : (finRule f hq s).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (LocalRule.finRule_ne_zero_of_leftTap h hs)
  rw [leftEnd_eq hne', leftEnd_eq hne]
  exact LocalRule.finRule_min'_of_leftTap h hne hne'

/-- **The window recurrence**: at a quiescent rule with `f 0 0 1 = 1`, cell `j` of the window of
width `W` of the image of a nonzero state is `f` of cells `j - 2`, `j - 1` and `j` of the state's
window of width `W`, a cell below `0` being clear because it lies left of the leftmost set cell. -/
theorem FiniteConfiguration.leftWindow_finRule {f : LocalRule} {hq : f 0 0 0 = 0}
    (h : f 0 0 1 = 1) {s : FiniteConfiguration} (hs : s ≠ 0) {W j : ℕ} (hj : j < W) :
    (finRule f hq s).leftWindow W j =
      f (if 2 ≤ j then s.leftWindow W (j - 2) else 0) (if 1 ≤ j then s.leftWindow W (j - 1) else 0)
        (s.leftWindow W j) := by
  simp only [leftWindow, hj, ite_true, leftEnd_finRule h hs, finRule_apply]
  have e1 : s (s.leftEnd - 1 + j - 1) =
      if 2 ≤ j then (if j - 2 < W then s (s.leftEnd + ((j - 2 : ℕ) : ℤ)) else 0) else 0 := by
    split_ifs with h2 h3
    · congr 1; omega
    · omega
    · exact eq_zero_of_lt_leftEnd hs (by omega)
  have e2 : s (s.leftEnd - 1 + j) =
      if 1 ≤ j then (if j - 1 < W then s (s.leftEnd + ((j - 1 : ℕ) : ℤ)) else 0) else 0 := by
    split_ifs with h2 h3
    · congr 1; omega
    · omega
    · exact eq_zero_of_lt_leftEnd hs (by omega)
  have e3 : s (s.leftEnd - 1 + j + 1) = s (s.leftEnd + j) := by congr 1; omega
  rw [e1, e2, e3]

/-- **Closure of windows holds**: at a quiescent rule with `f 0 0 1 = 1`, two nonzero states with
equal windows have nonzero images with equal windows. -/
theorem leftWindowClosed : LeftWindowClosed := by
  intro f hq h W s s' hs hs' hw
  refine ⟨LocalRule.finRule_ne_zero_of_leftTap h hs, ?_⟩
  funext j
  by_cases hj : j < W
  · rw [leftWindow_finRule h hs hj, leftWindow_finRule h hs' hj, hw]
  · simp [leftWindow, hj]

/-! ## Rule `54` settles into blocks -/

/-- The window recurrence at rule `54`, as a property of a family `e n j` of window cells (time `n`,
cell `j`) below a width. -/
private def WinRec (e : ℕ → ℕ → ZMod 2) (W : ℕ) : Prop :=
  ∀ n j, j < W → e (n + 1) j = wolframRule 54 (if 2 ≤ j then e n (j - 2) else 0)
    (if 1 ≤ j then e n (j - 1) else 0) (e n j)

/-- Block `b` (cells `4b` to `4b + 3`) is settled from time `T`: its first cell is set, its last
clear, its middle cells equal, and the first of them toggles. -/
private def Settled (e : ℕ → ℕ → ZMod 2) (b T : ℕ) : Prop :=
  ∀ t, T ≤ t → e t (4 * b) = 1 ∧ e t (4 * b + 3) = 0 ∧ e t (4 * b + 1) = e t (4 * b + 2) ∧
    e (t + 1) (4 * b + 1) = 1 + e t (4 * b + 1)

private theorem WinRec.cell0 {e : ℕ → ℕ → ZMod 2} {W : ℕ} (hr : WinRec e W) (hW : 0 < W) (t : ℕ) :
    e (t + 1) 0 = wolframRule 54 0 0 (e t 0) := by
  have := hr t 0 hW
  simpa using this

private theorem WinRec.cell1 {e : ℕ → ℕ → ZMod 2} {W : ℕ} (hr : WinRec e W) (hW : 1 < W) (t : ℕ) :
    e (t + 1) 1 = wolframRule 54 0 (e t 0) (e t 1) := by
  have := hr t 1 hW
  simpa using this

private theorem WinRec.cell {e : ℕ → ℕ → ZMod 2} {W : ℕ} (hr : WinRec e W) (t j : ℕ)
    (hj : j + 2 < W) :
    e (t + 1) (j + 2) = wolframRule 54 (e t j) (e t (j + 1)) (e t (j + 2)) := by
  have := hr t (j + 2) hj
  simp only [show 2 ≤ j + 2 from by omega, show 1 ≤ j + 2 from by omega, ite_true] at this
  simpa using this

/-- The four cells of the block above, with the alternating cell below them, one step of the
recurrence when the cell between is clear. -/
private def tr5 (s : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 :=
  (1 + s.1, wolframRule 54 s.1 0 s.2.1, wolframRule 54 0 s.2.1 s.2.2.1,
    wolframRule 54 s.2.1 s.2.2.1 s.2.2.2.1, wolframRule 54 s.2.2.1 s.2.2.2.1 s.2.2.2.2)

private theorem tr5_five (s : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    (tr5^[5] s).2.1 = 1 ∧ (tr5^[5] s).2.2.2.2 = 0 ∧ (tr5^[5] s).2.2.1 = (tr5^[5] s).2.2.2.1 := by
  revert s
  decide

private theorem tr5_step (s : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)
    (h : s.2.1 = 1 ∧ s.2.2.2.2 = 0 ∧ s.2.2.1 = s.2.2.2.1) :
    ((tr5 s).2.1 = 1 ∧ (tr5 s).2.2.2.2 = 0 ∧ (tr5 s).2.2.1 = (tr5 s).2.2.2.1) ∧
      (tr5 s).2.2.1 = 1 + s.2.2.1 := by
  revert s
  decide

/-- One step of the recurrence on cells `1`, `2` and `3`, cell `0` being set. -/
private def tr3 (s : ZMod 2 × ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (wolframRule 54 0 1 s.1, wolframRule 54 1 s.1 s.2.1, wolframRule 54 s.1 s.2.1 s.2.2)

private theorem tr3_three (s : ZMod 2 × ZMod 2 × ZMod 2) :
    (tr3^[3] s).1 = (tr3^[3] s).2.1 ∧ (tr3^[3] s).2.2 = 0 := by
  revert s
  decide

private theorem tr3_step (s : ZMod 2 × ZMod 2 × ZMod 2) (h : s.1 = s.2.1 ∧ s.2.2 = 0) :
    ((tr3 s).1 = (tr3 s).2.1 ∧ (tr3 s).2.2 = 0) ∧ (tr3 s).1 = 1 + s.1 := by
  revert s
  decide

/-- Block `0` is settled from time `3`, cell `0` being set at every time. -/
private theorem settled_zero {e : ℕ → ℕ → ZMod 2} {W : ℕ} (hr : WinRec e W) (hW : 3 < W)
    (h0 : ∀ n, e n 0 = 1) : Settled e 0 3 := by
  let St : ℕ → ZMod 2 × ZMod 2 × ZMod 2 := fun t => (e t 1, e t 2, e t 3)
  have hSt : ∀ t, St (t + 1) = tr3 (St t) := by
    intro t
    have r1 := hr.cell1 (by omega) t
    have r2 := hr.cell t 0 (by omega)
    have r3 := hr.cell t 1 (by omega)
    rw [h0 t] at r1 r2
    simp only [St, tr3, Prod.mk.injEq]
    exact ⟨r1, r2, r3⟩
  have hit : ∀ k, St k = tr3^[k] (St 0) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ← ih, hSt]
  have hinv : ∀ t, 3 ≤ t → (St t).1 = (St t).2.1 ∧ (St t).2.2 = 0 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rw [hit 3]; exact tr3_three _
    | succ t _ ih => rw [hSt]; exact (tr3_step _ ih).1
  intro t ht
  have hi := hinv t ht
  have hs := tr3_step _ hi
  rw [← hSt] at hs
  exact ⟨h0 t, hi.2, hi.1, hs.2⟩

/-- A settled block settles the block above it five steps later. -/
private theorem settled_succ {e : ℕ → ℕ → ZMod 2} {W : ℕ} (hr : WinRec e W) {b T : ℕ}
    (hb : 4 * b + 7 < W) (h : Settled e b T) : Settled e (b + 1) (T + 5) := by
  have hx : ∀ t, T ≤ t → e (t + 1) (4 * b + 2) = 1 + e t (4 * b + 2) := by
    intro t ht
    obtain ⟨_, _, h13, h14⟩ := h t ht
    obtain ⟨_, _, h23, _⟩ := h (t + 1) (by omega)
    rw [← h23, h14, h13]
  let St : ℕ → ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 := fun t =>
    (e t (4 * b + 2), e t (4 * b + 4), e t (4 * b + 5), e t (4 * b + 6), e t (4 * b + 7))
  have hSt : ∀ t, T ≤ t → St (t + 1) = tr5 (St t) := by
    intro t ht
    have h3 := (h t ht).2.1
    have r4 := hr.cell t (4 * b + 2) (by omega)
    have r5 := hr.cell t (4 * b + 3) (by omega)
    have r6 := hr.cell t (4 * b + 4) (by omega)
    have r7 := hr.cell t (4 * b + 5) (by omega)
    rw [h3] at r4 r5
    simp only [St, tr5, Prod.mk.injEq]
    exact ⟨hx t ht, r4, r5, r6, r7⟩
  have hit : ∀ k, St (T + k) = tr5^[k] (St T) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, hSt _ (by omega), Function.iterate_succ_apply', ← ih]
  have hinv : ∀ t, T + 5 ≤ t →
      (St t).2.1 = 1 ∧ (St t).2.2.2.2 = 0 ∧ (St t).2.2.1 = (St t).2.2.2.1 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rw [hit 5]; exact tr5_five _
    | succ t ht ih => rw [hSt _ (by omega)]; exact (tr5_step _ ih).1
  intro t ht
  have hi := hinv t ht
  have hs := tr5_step _ hi
  rw [← hSt _ (by omega)] at hs
  have e1 : 4 * (b + 1) = 4 * b + 4 := by ring
  rw [e1]
  exact ⟨hi.1, hi.2.1, hi.2.2, hs.2⟩

/-- **The windows of rule `54` are blocks late**: from `5 * ((W + 3) / 4)` steps on, the window of
width `W` of every iterate of a nonzero state under rule `54` has the block form. -/
theorem etherBlocksLate54 : EtherBlocksLate54 := by
  intro hq s hs W n hn
  set it := finRule (wolframRule 54) hq with hit
  have hq1 : wolframRule 54 0 0 1 = 1 := by decide
  have hne : ∀ k, it^[k] s ≠ 0 := by
    intro k
    induction k with
    | zero => exact hs
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact LocalRule.finRule_ne_zero_of_leftTap hq1 ih
  set W' := 4 * ((W + 3) / 4) with hW'
  let e : ℕ → ℕ → ZMod 2 := fun k j => (it^[k] s).leftWindow W' j
  have hr : WinRec e W' := by
    intro k j hj
    simp only [e]
    rw [Function.iterate_succ_apply']
    exact leftWindow_finRule hq1 (hne k) hj
  intro j hj
  have hjW' : j < W' := by omega
  have h0 : ∀ k, e k 0 = 1 := by
    intro k
    induction k with
    | zero =>
      have hsne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
      have hmem : s.leftEnd ∈ s.support := by
        rw [leftEnd_eq hsne]
        exact Finset.min'_mem _ _
      have hv : s s.leftEnd ≠ 0 := Finsupp.mem_support_iff.mp hmem
      have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      simp only [e, leftWindow, Function.iterate_zero, id_eq, show 0 < W' by omega, ite_true]
      simpa using this _ hv
    | succ k ih =>
      have := hr.cell0 (by omega) k
      rw [this, ih]
      decide
  have hall : ∀ b, 4 * b + 3 < W' → Settled e b (5 * b + 3) := by
    intro b
    induction b with
    | zero => intro hb; exact settled_zero hr (by omega) h0
    | succ b ih =>
      intro hb
      have := settled_succ hr (b := b) (by omega) (ih (by omega))
      have e1 : 5 * (b + 1) + 3 = 5 * b + 3 + 5 := by ring
      rw [e1]
      exact this
  have hwin : ∀ i, i < W → (it^[n] s).leftWindow W i = e n i := by
    intro i hi
    simp only [e, leftWindow, hi, ite_true, show i < W' by omega]
  have hbl := hall (j / 4) (by omega) n (by omega)
  refine ⟨fun h4 => ?_, fun h3 => ?_, fun h1 hj1 => ?_⟩
  · rw [hwin j hj]
    have : j = 4 * (j / 4) := by omega
    rw [this]
    exact hbl.1
  · rw [hwin j hj]
    have : j = 4 * (j / 4) + 3 := by omega
    rw [this]
    exact hbl.2.1
  · rw [hwin j hj, hwin (j + 1) hj1]
    have : j = 4 * (j / 4) + 1 := by omega
    have h2 : j + 1 = 4 * (j / 4) + 2 := by omega
    rw [h2]
    conv_lhs => rw [this]
    exact hbl.2.2.1

/-- **Rule `54` reproduces no pattern**, from closure of windows, the block form late and the
window of copies as hypotheses: an iterate that is two copies at gap `4` has the pattern's window of
width `diam p + 4`, closure makes that window recur at every multiple of the iterate's index, and
the block form puts a set cell where the pattern's window has four clear ones. -/
theorem not_reproduces_wolfram54_of_window (h1 : LeftWindowClosed) (h2 : EtherBlocksLate54)
    (h3 : LeftWindowCopies) :
    ∀ (hq : wolframRule 54 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 54) hq) p := by
  intro hq p ⟨hp, hrep⟩
  obtain ⟨t, k, hk, hcop⟩ := hrep 2 4
  have hq1 : wolframRule 54 0 0 1 = 1 := by decide
  have ht : t ≠ 0 := by
    rintro rfl
    have := copies_diam_le hp hcop (by omega)
    have h1d := FiniteConfiguration.one_le_diam hp
    simp only [Function.iterate_zero, id_eq] at this
    nlinarith
  have hs := h3 p _ k 4 hp (by omega) hcop
  have hs0 := (iterate_closed h1 hq hq1 (p.diam + 4) t p p hp hp rfl).1
  have hper : ∀ j, ((finRule (wolframRule 54) hq)^[j + t] p).leftWindow (p.diam + 4) =
      ((finRule (wolframRule 54) hq)^[j] p).leftWindow (p.diam + 4) := by
    intro j
    rw [Function.iterate_add_apply]
    exact (iterate_closed h1 hq hq1 (p.diam + 4) j _ p hs0 hp hs).2
  have hmul : ∀ m : ℕ, ((finRule (wolframRule 54) hq)^[m * t] p).leftWindow (p.diam + 4) =
      p.leftWindow (p.diam + 4) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.succ_mul, hper, ih]
  set W := p.diam + 4 with hW
  have hn : 5 * ((W + 3) / 4) ≤ (5 * ((W + 3) / 4)) * t := Nat.le_mul_of_pos_right _ (by omega)
  have hE := h2 hq p hp W _ hn
  rw [hmul] at hE
  have hd := FiniteConfiguration.one_le_diam hp
  have hj := hE (4 * ((p.diam + 3) / 4)) (by omega)
  have h0 := FiniteConfiguration.leftWindow_eq_zero_of_diam_le hp
    (W := W) (j := 4 * ((p.diam + 3) / 4)) (by omega) (by omega)
  rw [hj.1 (by omega)] at h0
  exact one_ne_zero h0

/-! ## Copies read the pattern's window -/

private theorem FiniteConfiguration.translate_eq_sub (i : ℤ) (p : FiniteConfiguration) (x : ℤ) :
    translate i p x = p (x - i) := by
  have h := Finsupp.mapDomain_apply_of_injective (add_left_injective i) p (x - i)
  rw [sub_add_cancel] at h
  exact h

/-- Left of the second copy's start, a sum of copies agrees with its first copy. -/
private theorem copies_apply_left {p s : FiniteConfiguration} {k G : ℕ} (hp : p ≠ 0) (hk : 1 ≤ k)
    (h : Copies p s k G) :
    ∃ c0 : ℤ, ∀ x, x < c0 + p.leftEnd + ((p.diam + G : ℕ) : ℤ) → s x = p (x - c0) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c 0, fun x hx => ?_⟩
  have hmono : ∀ j, 1 ≤ j → j < k → c 0 + ((p.diam + G : ℕ) : ℤ) ≤ c j := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hj
      have h1 := hc j (by omega)
      by_cases h0 : j = 0
      · subst h0
        push_cast at h1 ⊢
        omega
      · have h2 := ih (by omega) (by omega)
        push_cast at h1 h2 ⊢
        omega
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single 0]
  · rw [translate_eq_sub]
  · intro j hj hj0
    rw [translate_eq_sub]
    have hjk : j < k := Finset.mem_range.mp hj
    have := hmono j (by omega) hjk
    exact eq_zero_of_lt_leftEnd hp (by omega)
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

/-- **Copies read the pattern's window**: a state that is `k ≥ 1` copies of a nonzero pattern `p` at
gap `G` has the window of width `diam p + G` of `p`, since the first copy's leftmost set cell is
the state's and the later copies start at least `diam p + G` cells to its right. -/
theorem leftWindowCopies : LeftWindowCopies := by
  intro p s k G hp hk hcop
  obtain ⟨c0, hc0⟩ := copies_apply_left hp hk hcop
  have hpne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hd := FiniteConfiguration.one_le_diam hp
  have hmem : p p.leftEnd ≠ 0 := by
    rw [leftEnd_eq hpne]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
  have hsm : s (c0 + p.leftEnd) ≠ 0 := by
    rw [hc0 _ (by push_cast; omega)]
    simpa using hmem
  have hs : s ≠ 0 := fun h => hsm (by simp [h])
  have hend : s.leftEnd = c0 + p.leftEnd := by
    have hsne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    rw [leftEnd_eq hsne]
    apply le_antisymm (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hsm))
    by_contra hlt
    push Not at hlt
    have hm := Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hsne)
    rw [hc0 _ (by push_cast; omega)] at hm
    exact hm (eq_zero_of_lt_leftEnd hp (by omega))
  funext j
  simp only [leftWindow]
  by_cases hj : j < p.diam + G
  · simp only [hj, ite_true]
    rw [hend, hc0 _ (by push_cast; omega)]
    congr 1
    ring
  · simp [hj]

/-- **Rule `54` reproduces no pattern**: whatever the nonzero or zero state `p`, the iterates of
rule `54` from `p` are never, for every bound and gap, at least that many copies of `p` at that gap
([RuleSpace] §5). -/
theorem not_reproduces_wolfram54 :
    ∀ (hq : wolframRule 54 0 0 0 = 0) (p : FiniteConfiguration),
      ¬ Reproduces (finRule (wolframRule 54) hq) p :=
  not_reproduces_wolfram54_of_window leftWindowClosed etherBlocksLate54 leftWindowCopies

/-- **Joint satisfiability of copies reading the pattern's window**: the pattern `p` of cells `0`
and `2`, the state `s` of cells `5`, `7`, `9` and `11`, `k = 2` and `G = 1` meet the three
hypotheses at once, with offsets `5` and `9`; `diam p + G = 4`, and both windows of width `4` read
`1010`. -/
theorem leftWindowCopies_nonvacuous {p s : FiniteConfiguration}
    (hp : p = Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (2 : ℤ) (1 : ZMod 2))
    (hs : s = Finsupp.single (5 : ℤ) (1 : ZMod 2) + Finsupp.single (7 : ℤ) (1 : ZMod 2) +
      Finsupp.single (9 : ℤ) (1 : ZMod 2) + Finsupp.single (11 : ℤ) (1 : ZMod 2)) :
    p ≠ 0 ∧ 1 ≤ 2 ∧ Copies p s 2 1 ∧ p.diam + 1 = 4 ∧
      (∀ j : ℕ, s.leftWindow 4 j = if j = 0 ∨ j = 2 then 1 else 0) ∧
      (∀ j : ℕ, p.leftWindow 4 j = if j = 0 ∨ j = 2 then 1 else 0) := by
  have hpv : ∀ x : ℤ, p x = (if x = 0 then 1 else 0) + (if x = 2 then 1 else 0) := by
    intro x
    subst hp
    simp [Finsupp.single_apply, eq_comm]
  have hsv : ∀ x : ℤ, s x = (if x = 5 then 1 else 0) + (if x = 7 then 1 else 0) +
      (if x = 9 then 1 else 0) + (if x = 11 then 1 else 0) := by
    intro x
    subst hs
    simp [Finsupp.single_apply, eq_comm]
  have hp0 : p ≠ 0 := by
    intro hc
    have := congrArg (fun g : FiniteConfiguration => g 0) hc
    rw [hpv] at this
    simp at this
  have hs0 : s ≠ 0 := by
    intro hc
    have := congrArg (fun g : FiniteConfiguration => g 5) hc
    rw [hsv] at this
    simp at this
  have hpne := Finsupp.support_nonempty_iff.mpr hp0
  have hsne := Finsupp.support_nonempty_iff.mpr hs0
  have hpend : p.leftEnd = 0 := by
    rw [leftEnd_eq hpne]
    apply le_antisymm
    · apply Finset.min'_le
      rw [Finsupp.mem_support_iff, hpv]
      simp
    · have hm := Finset.min'_mem _ hpne
      rw [Finsupp.mem_support_iff, hpv] at hm
      by_contra hlt
      push Not at hlt
      have e1 : (Finset.min' _ hpne : ℤ) ≠ 0 := by omega
      have e2 : (Finset.min' _ hpne : ℤ) ≠ 2 := by omega
      simp [e1, e2] at hm
  have hsend : s.leftEnd = 5 := by
    rw [leftEnd_eq hsne]
    apply le_antisymm
    · apply Finset.min'_le
      rw [Finsupp.mem_support_iff, hsv]
      simp
    · have hm := Finset.min'_mem _ hsne
      rw [Finsupp.mem_support_iff, hsv] at hm
      by_contra hlt
      push Not at hlt
      have e1 : (Finset.min' _ hsne : ℤ) ≠ 5 := by omega
      have e2 : (Finset.min' _ hsne : ℤ) ≠ 7 := by omega
      have e3 : (Finset.min' _ hsne : ℤ) ≠ 9 := by omega
      have e4 : (Finset.min' _ hsne : ℤ) ≠ 11 := by omega
      simp [e1, e2, e3, e4] at hm
  have hdiam : p.diam = 3 := by
    rw [diam_eq' hpne]
    have : p.support.max' hpne = 2 := by
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        rw [Finsupp.mem_support_iff, hpv] at hy
        by_contra hlt
        push Not at hlt
        have e1 : y ≠ 0 := by omega
        have e2 : y ≠ 2 := by omega
        simp [e1, e2] at hy
      · apply Finset.le_max'
        rw [Finsupp.mem_support_iff, hpv]
        simp
    have hmin : p.support.min' hpne = 0 := by rw [← leftEnd_eq hpne]; exact hpend
    rw [this, hmin]
    rfl
  have hcop : Copies p s 2 1 := by
    refine ⟨fun j => if j = 0 then 5 else 9, ?_, ?_⟩
    · intro j hj
      have : j = 0 := by omega
      subst this
      simp [hdiam]
    · ext x
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finsupp.add_apply,
        translate_eq_sub, hpv, hsv, ite_true, show (1 : ℕ) ≠ 0 from by omega, ite_false]
      have b1 : (x - 5 = 2) ↔ x = 7 := by omega
      have b2 : (x - 9 = 2) ↔ x = 11 := by omega
      have b3 : (x - 5 = 0) ↔ x = 5 := by omega
      have b4 : (x - 9 = 0) ↔ x = 9 := by omega
      by_cases a1 : x = 5 <;> by_cases a2 : x = 7 <;> by_cases a3 : x = 9 <;>
        by_cases a4 : x = 11 <;> simp [a1, a2, a3, a4, b1, b2, b3, b4]
  refine ⟨hp0, by omega, hcop, by omega, ?_, ?_⟩
  · intro j
    simp only [leftWindow, hsend, hsv]
    by_cases hj : j < 4
    · simp only [hj, ite_true]
      interval_cases j <;> simp
    · have h0 : j ≠ 0 := by omega
      have h2 : j ≠ 2 := by omega
      simp [hj, h0, h2]
  · intro j
    simp only [leftWindow, hpend, hpv]
    by_cases hj : j < 4
    · simp only [hj, ite_true]
      interval_cases j <;> simp
    · have h0 : j ≠ 0 := by omega
      have h2 : j ≠ 2 := by omega
      simp [hj, h0, h2]

/-! ## A computed instance and its guard -/

/-- The cell `i` after `n` steps of the rule `f` from the single cell at `0`, by the rule's own
recursion. -/
private def cellAt (f : LocalRule) : ℕ → ℤ → ZMod 2
  | 0, i => if i = 0 then 1 else 0
  | n + 1, i => f (cellAt f n (i - 1)) (cellAt f n i) (cellAt f n (i + 1))

private theorem iterate_single_apply (f : LocalRule) (hq : f 0 0 0 = 0) (n : ℕ) (i : ℤ) :
    ((finRule f hq)^[n] (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration)) i =
      cellAt f n i := by
  induction n generalizing i with
  | zero => simp [cellAt, Finsupp.single_apply, eq_comm]
  | succ n ih =>
    rw [Function.iterate_succ_apply', finRule_apply, ih, ih, ih]
    rfl

private theorem cellAt_bound (f : LocalRule) (hq : f 0 0 0 = 0) (n : ℕ) :
    ∀ i, cellAt f n i ≠ 0 → -(n : ℤ) ≤ i ∧ i ≤ n := by
  induction n with
  | zero =>
    intro i hi
    simp only [cellAt] at hi
    split_ifs at hi with h
    · simp [h]
    · exact absurd rfl hi
  | succ n ih =>
    intro i hi
    simp only [cellAt] at hi
    by_cases h : cellAt f n (i - 1) = 0 ∧ cellAt f n i = 0 ∧ cellAt f n (i + 1) = 0
    · rw [h.1, h.2.1, h.2.2, hq] at hi
      exact absurd rfl hi
    · push_cast
      by_cases ha : cellAt f n (i - 1) = 0
      · by_cases hb : cellAt f n i = 0
        · have hc : cellAt f n (i + 1) ≠ 0 := fun hc => h ⟨ha, hb, hc⟩
          have := ih _ hc
          omega
        · have := ih _ hb
          omega
      · have := ih _ ha
        omega

private theorem leftWindow_iterate_single (f : LocalRule) (hq : f 0 0 0 = 0) (n : ℕ)
    (h : cellAt f n (-(n : ℤ)) ≠ 0) (j : ℕ) :
    ((finRule f hq)^[n] (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration)).leftWindow
        8 j = if j < 8 then cellAt f n (-(n : ℤ) + j) else 0 := by
  set s : FiniteConfiguration := (finRule f hq)^[n] (Finsupp.single (0 : ℤ) (1 : ZMod 2)) with hs
  have hval : ∀ i, s i = cellAt f n i := iterate_single_apply f hq n
  have hmem : -(n : ℤ) ∈ s.support := Finsupp.mem_support_iff.mpr (by rw [hval]; exact h)
  have hne : s.support.Nonempty := ⟨_, hmem⟩
  have hend : s.leftEnd = -(n : ℤ) := by
    rw [leftEnd_eq hne]
    apply le_antisymm (Finset.min'_le _ _ hmem)
    have hm := Finset.min'_mem s.support hne
    have := cellAt_bound f hq n _ (by rw [← hval]; exact Finsupp.mem_support_iff.mp hm)
    exact this.1
  simp only [leftWindow, hend, hval]

/-- **The tenth iterate of rule `54` from the single cell reads blocks**: its window of width `8`
reads `10001000`, and satisfies the block form at the bound of `EtherBlocksLate54`. -/
theorem etherBlocks_single_wolfram54 (hq : wolframRule 54 0 0 0 = 0) :
    EtherBlocks 8
      (((finRule (wolframRule 54) hq)^[10]
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration)).leftWindow 8) := by
  have hc : cellAt (wolframRule 54) 10 (-((10 : ℕ) : ℤ)) ≠ 0 := by decide +kernel
  intro j hj
  simp only [leftWindow_iterate_single (wolframRule 54) hq 10 hc, hj, ite_true]
  interval_cases j <;> decide +kernel

/-- **Guard**: the tenth iterate of rule `30` from the single cell reads `11001000`, so cells `1`
and `2` of its window of width `8` differ and the block form fails: the block form is the ether of
rule `54`, not a property of every rule that moves its left end out a cell a step. -/
theorem not_etherBlocks_single_wolfram30 (hq : wolframRule 30 0 0 0 = 0) :
    ¬ EtherBlocks 8
      (((finRule (wolframRule 30) hq)^[10]
        (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration)).leftWindow 8) := by
  have hc : cellAt (wolframRule 30) 10 (-((10 : ℕ) : ℤ)) ≠ 0 := by decide +kernel
  intro h
  have := (h 1 (by omega)).2.2 (by omega) (by omega)
  simp only [leftWindow_iterate_single (wolframRule 30) hq 10 hc] at this
  revert this
  decide +kernel

private theorem leftEnd_single :
    FiniteConfiguration.leftEnd
      (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration) = 0 := by
  have hne : (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration).support.Nonempty :=
    ⟨0, by simp⟩
  rw [leftEnd_eq hne]
  simp

/-- **Joint satisfiability of the window recurrence**: rule `54`, the single cell `s` at `0`, width
`4` and `j = 1` meet the three hypotheses at once; the image's window reads `1110`, and its cell `1`
is `f 0 1 0 = 1` of cells `0`, `0` and `1` of the state's window. -/
theorem leftWindow_finRule_nonvacuous (hq : wolframRule 54 0 0 0 = 0) {s : FiniteConfiguration}
    (hs0 : s = Finsupp.single (0 : ℤ) (1 : ZMod 2)) :
    wolframRule 54 0 0 1 = 1 ∧ s ≠ 0 ∧ 1 < 4 ∧
      (∀ j : ℕ, (finRule (wolframRule 54) hq s).leftWindow 4 j = if j < 3 then 1 else 0) ∧
      (finRule (wolframRule 54) hq s).leftWindow 4 1 =
        wolframRule 54 (if 2 ≤ 1 then s.leftWindow 4 (1 - 2) else 0)
          (if 1 ≤ 1 then s.leftWindow 4 (1 - 1) else 0) (s.leftWindow 4 1) ∧
      wolframRule 54 0 1 0 = 1 := by
  subst hs0
  have h1 : wolframRule 54 0 0 1 = 1 := by decide
  have hs : (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration) ≠ 0 := by
    intro hc
    have := congrArg (fun g : FiniteConfiguration => g 0) hc
    simp at this
  refine ⟨h1, hs, by omega, ?_, leftWindow_finRule h1 hs (by omega), by decide⟩
  intro j
  have hend := leftEnd_finRule (hq := hq) h1 hs
  rw [leftEnd_single] at hend
  simp only [leftWindow, hend, finRule_apply]
  by_cases hj : j < 4
  · simp only [hj, ite_true]
    have r1 : wolframRule 54 0 0 1 = 1 := by decide
    have r2 : wolframRule 54 0 1 0 = 1 := by decide
    have r3 : wolframRule 54 1 0 0 = 1 := by decide
    have r4 : wolframRule 54 0 0 0 = 0 := hq
    interval_cases j <;> simp [r1, r2, r3, r4]
  · have : ¬ j < 3 := by omega
    simp [hj, this]

/-- **Guard**: the hypothesis `f 0 0 1 = 1` of closure of windows is load-bearing. At rule `4`,
which is quiescent and has `f 0 0 1 = 0`, the single cell `a` at `0` and the state `b` with cells
`0` and `1` set both read `1` in a window of width `1`; the image of `a` is nonzero with window
`1`, and the image of `b` is the zero state, with window `0`. -/
theorem not_leftWindowClosed_wolfram4 (hq : wolframRule 4 0 0 0 = 0) {a b : FiniteConfiguration}
    (ha : a = Finsupp.single (0 : ℤ) (1 : ZMod 2))
    (hb : b = Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (1 : ℤ) (1 : ZMod 2)) :
    wolframRule 4 0 0 1 = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a.leftWindow 1 = b.leftWindow 1 ∧
      finRule (wolframRule 4) hq a ≠ 0 ∧ finRule (wolframRule 4) hq b = 0 ∧
      (finRule (wolframRule 4) hq a).leftWindow 1 0 = 1 ∧
      (finRule (wolframRule 4) hq b).leftWindow 1 0 = 0 := by
  subst ha hb
  have hbv : ∀ x : ℤ, (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (1 : ℤ) (1 : ZMod 2)
      : FiniteConfiguration) x = (if x = 0 then 1 else 0) + (if x = 1 then 1 else 0) := by
    intro x
    simp [Finsupp.single_apply, eq_comm]
  have hav : ∀ x : ℤ, (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration) x =
      if x = 0 then 1 else 0 := by
    intro x
    simp [Finsupp.single_apply, eq_comm]
  have r1 : wolframRule 4 0 0 1 = 0 := by decide
  have r2 : wolframRule 4 0 1 0 = 1 := by decide
  have r3 : wolframRule 4 1 0 0 = 0 := by decide
  have r4 : wolframRule 4 0 1 1 = 0 := by decide
  have r5 : wolframRule 4 1 1 0 = 0 := by decide
  have hA : finRule (wolframRule 4) hq (Finsupp.single (0 : ℤ) (1 : ZMod 2)) =
      Finsupp.single (0 : ℤ) (1 : ZMod 2) := by
    ext i
    rw [finRule_apply, hav, hav, hav]
    by_cases h0 : i = 0
    · subst h0; decide
    · by_cases h1 : i - 1 = 0
      · have : i + 1 ≠ 0 := by omega
        have h2 : i ≠ 0 := h0
        simp [h1, this, h2, r3]
      · by_cases h2 : i + 1 = 0
        · have : i ≠ 0 := h0
          simp [h1, h2, this, r1]
        · simp [h0, h1, h2, hq]
  have hB : finRule (wolframRule 4) hq (Finsupp.single (0 : ℤ) (1 : ZMod 2) +
      Finsupp.single (1 : ℤ) (1 : ZMod 2) : FiniteConfiguration) = 0 := by
    ext i
    rw [finRule_apply, hbv, hbv, hbv]
    by_cases h0 : i = 0
    · subst h0; decide
    · by_cases h1 : i = 1
      · subst h1; decide
      · by_cases h2 : i = -1
        · subst h2; decide
        · by_cases h3 : i = 2
          · subst h3; decide
          · have e1 : i - 1 ≠ 0 := by omega
            have e2 : i - 1 ≠ 1 := by omega
            have e3 : i + 1 ≠ 0 := by omega
            have e4 : i + 1 ≠ 1 := by omega
            simp [h0, h1, e1, e2, e3, e4, hq]
  have hs1 : (Finsupp.single (0 : ℤ) (1 : ZMod 2) : FiniteConfiguration) ≠ 0 := by
    intro hc
    have := congrArg (fun g : FiniteConfiguration => g 0) hc
    simp at this
  have hs2 : (Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (1 : ℤ) (1 : ZMod 2) :
      FiniteConfiguration) ≠ 0 := by
    intro hc
    have := congrArg (fun g : FiniteConfiguration => g 0) hc
    rw [hbv] at this
    simp at this
  have hendB : FiniteConfiguration.leftEnd (Finsupp.single (0 : ℤ) (1 : ZMod 2) +
      Finsupp.single (1 : ℤ) (1 : ZMod 2) : FiniteConfiguration) = 0 := by
    have hne := Finsupp.support_nonempty_iff.mpr hs2
    rw [leftEnd_eq hne]
    apply le_antisymm
    · apply Finset.min'_le
      rw [Finsupp.mem_support_iff, hbv]
      simp
    · have hm := Finset.min'_mem _ hne
      rw [Finsupp.mem_support_iff, hbv] at hm
      by_contra hlt
      push Not at hlt
      have e1 : (Finset.min' _ hne : ℤ) ≠ 0 := by omega
      have e2 : (Finset.min' _ hne : ℤ) ≠ 1 := by omega
      simp [e1, e2] at hm
  refine ⟨by decide, hs1, hs2, ?_, ?_, hB, ?_, ?_⟩
  · funext j
    simp only [leftWindow, hendB, leftEnd_single, hav, hbv]
    by_cases hj : j < 1
    · have : j = 0 := by omega
      subst this; simp
    · simp [hj]
  · rw [hA]; exact hs1
  · rw [hA]; simp [leftWindow, leftEnd_single]
  · rw [hB]; simp [leftWindow, leftEnd]

/-- One step of the window recurrence of rule `54` on the cells below width `8`. -/
private def winStep8 (w : ℕ → ZMod 2) : ℕ → ZMod 2 := fun j =>
  if j < 8 then wolframRule 54 (if 2 ≤ j then w (j - 2) else 0) (if 1 ≤ j then w (j - 1) else 0)
    (w j) else 0

/-- The window of width `8` of the state with cells `0`, `1` and `3` set. -/
private def winInit8 : ℕ → ZMod 2 := fun j => if j = 0 ∨ j = 1 ∨ j = 3 then 1 else 0

/-- **Guard**: the threshold of `EtherBlocksLate54` is not vacuous. From the state with cells `0`,
`1` and `3` set, the window of width `8` of the seventh iterate of rule `54` reads `10001111`, and
fails the block form at cell `7`; seven steps is below `5 * ((8 + 3) / 4) = 10`. -/
theorem not_etherBlocks_early_wolfram54 (hq : wolframRule 54 0 0 0 = 0) {s : FiniteConfiguration}
    (hs : s = Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (1 : ℤ) (1 : ZMod 2) +
      Finsupp.single (3 : ℤ) (1 : ZMod 2)) :
    7 < 5 * ((8 + 3) / 4) ∧
      (∀ j : ℕ, ((finRule (wolframRule 54) hq)^[7] s).leftWindow 8 j =
        if j = 0 ∨ (4 ≤ j ∧ j < 8) then 1 else 0) ∧
      ¬ EtherBlocks 8 (((finRule (wolframRule 54) hq)^[7] s).leftWindow 8) := by
  have hsv : ∀ x : ℤ, s x =
      (if x = 0 then 1 else 0) + (if x = 1 then 1 else 0) + (if x = 3 then 1 else 0) := by
    intro x
    subst hs
    simp [Finsupp.single_apply, eq_comm]
  have hq1 : wolframRule 54 0 0 1 = 1 := by decide
  have hs0 : s ≠ 0 := by
    intro hc
    have := congrArg (fun g : FiniteConfiguration => g 0) hc
    rw [hsv] at this
    simp at this
  have hend : s.leftEnd = 0 := by
    have hne := Finsupp.support_nonempty_iff.mpr hs0
    rw [leftEnd_eq hne]
    apply le_antisymm
    · apply Finset.min'_le
      rw [Finsupp.mem_support_iff, hsv]
      simp
    · have hm := Finset.min'_mem _ hne
      rw [Finsupp.mem_support_iff, hsv] at hm
      by_contra hlt
      push Not at hlt
      have e1 : (Finset.min' _ hne : ℤ) ≠ 0 := by omega
      have e2 : (Finset.min' _ hne : ℤ) ≠ 1 := by omega
      have e3 : (Finset.min' _ hne : ℤ) ≠ 3 := by omega
      simp [e1, e2, e3] at hm
  have hw0 : s.leftWindow 8 = winInit8 := by
    funext j
    simp only [leftWindow, hend, hsv, winInit8]
    by_cases hj : j < 8
    · simp only [hj, ite_true]
      interval_cases j <;> simp
    · have h0 : j ≠ 0 := by omega
      have h1 : j ≠ 1 := by omega
      have h3 : j ≠ 3 := by omega
      simp [hj, h0, h1, h3]
  have hiter : ∀ n, (finRule (wolframRule 54) hq)^[n] s ≠ 0 ∧
      ((finRule (wolframRule 54) hq)^[n] s).leftWindow 8 = winStep8^[n] winInit8 := by
    intro n
    induction n with
    | zero => exact ⟨hs0, hw0⟩
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        exact LocalRule.finRule_ne_zero_of_leftTap hq1 ih.1
      · funext j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        by_cases hj : j < 8
        · rw [leftWindow_finRule hq1 ih.1 hj, ih.2]
          simp only [winStep8, hj, ite_true]
        · simp [leftWindow, winStep8, hj]
  have h7 : ∀ j < 8, (winStep8^[7] winInit8) j = if j = 0 ∨ (4 ≤ j ∧ j < 8) then 1 else 0 := by
    decide +kernel
  have hwin : ∀ j : ℕ, ((finRule (wolframRule 54) hq)^[7] s).leftWindow 8 j =
      if j = 0 ∨ (4 ≤ j ∧ j < 8) then 1 else 0 := by
    intro j
    rw [(hiter 7).2]
    by_cases hj : j < 8
    · exact h7 j hj
    · have : ¬ (j = 0 ∨ (4 ≤ j ∧ j < 8)) := by omega
      rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply']
      simp only [this, ite_false]
      simp [winStep8, hj]
  refine ⟨by decide, hwin, fun h => ?_⟩
  have := (h 7 (by omega)).2.1 (by omega)
  rw [hwin 7] at this
  revert this
  decide

/-! ## Axiom guards -/

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.leftEnd_finRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.leftEnd_finRule

set_option linter.style.longLine false in
/-- info: 'ECA.FiniteConfiguration.leftWindow_finRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.FiniteConfiguration.leftWindow_finRule

set_option linter.style.longLine false in
/-- info: 'ECA.leftWindowClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.leftWindowClosed

set_option linter.style.longLine false in
/-- info: 'ECA.leftWindow_finRule_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.leftWindow_finRule_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_leftWindowClosed_wolfram4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_leftWindowClosed_wolfram4

set_option linter.style.longLine false in
/-- info: 'ECA.leftWindowCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.leftWindowCopies

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram54_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram54_of_window

set_option linter.style.longLine false in
/-- info: 'ECA.not_reproduces_wolfram54' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_reproduces_wolfram54

set_option linter.style.longLine false in
/-- info: 'ECA.leftWindowCopies_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.leftWindowCopies_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.etherBlocks_single_wolfram54' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.etherBlocks_single_wolfram54

set_option linter.style.longLine false in
/-- info: 'ECA.not_etherBlocks_single_wolfram30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_etherBlocks_single_wolfram30

set_option linter.style.longLine false in
/-- info: 'ECA.etherBlocksLate54' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.etherBlocksLate54

set_option linter.style.longLine false in
/-- info: 'ECA.not_etherBlocks_early_wolfram54' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_etherBlocks_early_wolfram54

end ECA
