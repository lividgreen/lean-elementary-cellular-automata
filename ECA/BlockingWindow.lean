module

public import ECA.StretchColumns
import all ECA.StretchColumns

/-!
# A blocking window makes its columns eventually periodic
([RuleSpace] §4)

A local rule acts on the finitely-supported configurations of the line. A **window** is a run of
`len` consecutive cells from a cell `lo`, and the word of the window at a time is the list of its
values. The window **blocks** from a time `T` on when one step of the rule on the word does not
depend on the two cells just outside it: whatever those two cells hold, the word of the window
one step later is the same. This is a blocking word in the literature's sense (J. Kari, *Cellular
automata*, lecture notes, University of Turku, the definition before Lemma 87: a word such that
the states of a segment at all times are independent of the states outside the word); here the
window is the whole word and the check is finite.

If the window blocks, the word at time `T + j` is the `j`-th iterate of one step with both outside
cells clear applied to the word at time `T`, whatever lies outside. The words take finitely many
values and each determines the next, so once one repeats the sequence of words is eventually
periodic, and a column of the window reads one letter of the word, so **every column of the window
is eventually periodic**.

`blockingCheck` decides the finite hypothesis on the list the seed reaches: for the first `N`
words, one step on the word with every pair of values of the two outside cells is the next word,
and the `N`-th word is one of the earlier ones. The check is sufficient and not necessary: a
column can be eventually periodic at a window that does not block. The census reads the leftmost
column, at cell `0`, at the listed pairs of a table and a seed only.

## Main results

* `wordStep` — one step of a local rule on a word, given the two cells just outside it.
* `blockingCheck` — the decidable check that the window of `len` cells from `lo` at time `T`
  blocks, with the word repeating within `N` steps.
* `eventuallyPeriodic_observedColumn_of_blockingCheck` — **the decided theorem**: if the check
  accepts, every observed column at a cell of the window is eventually periodic.
* `eventuallyPeriodic_observedColumn_of_blockingCheck_nonvacuous` and
  `blockingCheck_f90_single_eq_false` — the check accepts at rule `218` from the seed `[1, 1]`,
  and rejects at rule `90` from the single seed, where the independence of the outside cells is
  checked and not assumed.
* `blockingPairs` and `eventuallyPeriodic_observedColumn_blockingCensus` — **the census**: at
  thirteen seeds of table `94` and twelve of table `218`, the column at cell `0` is eventually
  periodic.
-/

open private coe_iterate_listSeed from ECA.StretchColumns

@[expose] public section

namespace ECA

open LocalRule

/-! ## Words and one step on a word -/

/-- The value at cell `i` of a word read from cell `0` on, with the cell `-1` replaced by `a` and
the cell `w.length` by `b`; cells further out read `a` to the left and `b` to the right. -/
def wordCell (a b : ZMod 2) (w : List (ZMod 2)) (i : ℤ) : ZMod 2 :=
  if i < 0 then a else if (w.length : ℤ) ≤ i then b else w.getD i.toNat 0

/-- **One step of a local rule on a word** whose left neighbour holds `a` and whose right neighbour
holds `b`: the new values at the cells of the word. -/
def wordStep (f : LocalRule) (a b : ZMod 2) (w : List (ZMod 2)) : List (ZMod 2) :=
  (List.range w.length).map fun k : ℕ =>
    f (wordCell a b w ((k : ℤ) - 1)) (wordCell a b w (k : ℤ)) (wordCell a b w ((k : ℤ) + 1))

/-- The word of the `len` cells from `lo` of a configuration. -/
def windowWord (c : ℤ → ZMod 2) (lo : ℤ) (len : ℕ) : List (ZMod 2) :=
  (List.range len).map fun k : ℕ => c (lo + (k : ℤ))

/-- **The window blocks and its word repeats**: with `w₀` the word of the `len` cells from `lo` of
the state at time `T` from the seed `listSeed seed`, and `w_{j+1}` one step of `f` on `w_j` with
both outside cells clear, one step of `f` on `w_j` with any values of the two outside cells is
`w_{j+1}` for every `j < N`, and `w_N` is one of `w_0, …, w_{N-1}`. -/
def blockingCheck (f : LocalRule) (seed : List (ZMod 2)) (T : ℕ) (lo : ℤ) (len N : ℕ) : Bool :=
  (List.range N).all (fun j =>
    [0, 1].all fun a => [0, 1].all fun b =>
      decide (wordStep f a b ((wordStep f 0 0)^[j]
          (windowWord (listConfig ((simStep f)^[T] seed) (0 - (T : ℤ))) lo len)) =
        (wordStep f 0 0)^[j + 1]
          (windowWord (listConfig ((simStep f)^[T] seed) (0 - (T : ℤ))) lo len))) &&
  (List.range N).any (fun j =>
    decide ((wordStep f 0 0)^[N]
        (windowWord (listConfig ((simStep f)^[T] seed) (0 - (T : ℤ))) lo len) =
      (wordStep f 0 0)^[j]
        (windowWord (listConfig ((simStep f)^[T] seed) (0 - (T : ℤ))) lo len)))

/-! ## The window of a step is the step of the window -/

private theorem length_windowWord (c : ℤ → ZMod 2) (lo : ℤ) (len : ℕ) :
    (windowWord c lo len).length = len := by
  simp [windowWord]

private theorem getD_windowWord (c : ℤ → ZMod 2) (lo : ℤ) (len k : ℕ) (hk : k < len) :
    (windowWord c lo len).getD k 0 = c (lo + k) := by
  simp [windowWord, List.getD_eq_getElem?_getD, hk]

private theorem wordCell_windowWord (c : ℤ → ZMod 2) (lo : ℤ) (len : ℕ) (i : ℤ)
    (h1 : -1 ≤ i) (h2 : i ≤ len) :
    wordCell (c (lo - 1)) (c (lo + len)) (windowWord c lo len) i = c (lo + i) := by
  unfold wordCell
  rw [length_windowWord]
  by_cases h3 : i < 0
  · have : i = -1 := by omega
    subst this
    simp [sub_eq_add_neg]
  · by_cases h4 : (len : ℤ) ≤ i
    · have : i = len := by omega
      subst this
      simp [h3]
    · simp only [h3, h4, ite_false]
      have := getD_windowWord c lo len i.toNat (by omega)
      rw [this]
      congr 2
      omega

private theorem windowWord_step (f : LocalRule) (c : ℤ → ZMod 2) (lo : ℤ) (len : ℕ) :
    windowWord (LocalRuleColumns.step f c) lo len =
      wordStep f (c (lo - 1)) (c (lo + len)) (windowWord c lo len) := by
  unfold wordStep
  rw [length_windowWord]
  conv_lhs => unfold windowWord
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  simp only [LocalRuleColumns.step]
  rw [wordCell_windowWord c lo len _ (by omega) (by omega),
    wordCell_windowWord c lo len _ (by omega) (by omega),
    wordCell_windowWord c lo len _ (by omega) (by omega)]
  congr 2 <;> ring_nf

/-! ## The decided theorem -/

private theorem mem_zeroOne (a : ZMod 2) : a ∈ ([0, 1] : List (ZMod 2)) := by
  revert a
  decide

/-- **A decided blocking window makes every observed column at its cells eventually periodic.** If
`blockingCheck` accepts the parameters at a seed list, the word of the window at every time from
`T` on is the iterate of the clear-neighbour step of the word at time `T`, whatever lies outside,
the words repeat, and a column of the window reads one letter of the word. -/
theorem eventuallyPeriodic_observedColumn_of_blockingCheck (f : LocalRule) (hq : f 0 0 0 = 0)
    (seed : List (ZMod 2)) (T : ℕ) (lo : ℤ) (len N : ℕ)
    (h : blockingCheck f seed T lo len N = true) (i : ℤ) (hlo : lo ≤ i) (hhi : i < lo + len) :
    DrivenColumns.EventuallyPeriodic (observedColumn (finRule f hq) (listSeed seed) i) := by
  set c : ℕ → ℤ → ZMod 2 := fun t => ⇑((finRule f hq)^[t] (listSeed seed)) with hc
  set w0 : List (ZMod 2) :=
    windowWord (listConfig ((simStep f)^[T] seed) (0 - (T : ℤ))) lo len with hw0
  set W : ℕ → List (ZMod 2) := fun j => (wordStep f 0 0)^[j] w0 with hW
  have hWsucc : ∀ j, W (j + 1) = wordStep f 0 0 (W j) := fun j => by
    simp only [hW]
    rw [Function.iterate_succ_apply']
  simp only [blockingCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hind, m, hmN, hm⟩ := h
  -- the neighbour independence at the first `N` words
  have hind' : ∀ j, j < N → ∀ a b : ZMod 2, wordStep f a b (W j) = wordStep f 0 0 (W j) := by
    intro j hj a b
    have := hind j hj a (mem_zeroOne a) b (mem_zeroOne b)
    rw [← hWsucc] at *
    exact this
  -- every word is one of the first `N`
  have hclosed : ∀ j, ∃ n, n < N ∧ W j = W n := by
    intro j
    induction j with
    | zero => exact ⟨0, by omega, rfl⟩
    | succ j ih =>
      obtain ⟨n, hn, hjn⟩ := ih
      rw [hWsucc, hjn, ← hWsucc]
      by_cases hn1 : n + 1 < N
      · exact ⟨n + 1, hn1, rfl⟩
      · have : n + 1 = N := by omega
        rw [this]
        exact ⟨m, hmN, hm⟩
  have hind'' : ∀ j, ∀ a b : ZMod 2, wordStep f a b (W j) = wordStep f 0 0 (W j) := by
    intro j a b
    obtain ⟨n, hn, hjn⟩ := hclosed j
    rw [hjn]
    exact hind' n hn a b
  -- the window of the state at time `T + j` is the word `W j`
  have hstep : ∀ t, c (t + 1) = LocalRuleColumns.step f (c t) := by
    intro t
    simp only [hc, coe_finRule_iterate, Function.iterate_succ_apply']
  have hwin : ∀ j, windowWord (c (T + j)) lo len = W j := by
    intro j
    induction j with
    | zero =>
      simp only [hc, hW, hw0, Nat.add_zero, Function.iterate_zero, id_eq]
      rw [coe_iterate_listSeed f hq seed T]
    | succ j ih =>
      rw [← add_assoc, hstep, windowWord_step, ih, hind'', hWsucc]
  -- the words are eventually periodic
  have hper : ∀ j, m ≤ j → W (j + (N - m)) = W j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rw [show m + (N - m) = N by omega]; exact hm
    | succ j _ ih =>
      rw [show j + 1 + (N - m) = (j + (N - m)) + 1 by omega, hWsucc, ih, ← hWsucc]
  -- a column of the window reads one letter of the word
  have hcol : ∀ j, c (T + j) i = (W j).getD (i - lo).toNat 0 := by
    intro j
    rw [← hwin j, getD_windowWord _ _ _ _ (by omega)]
    congr 1
    omega
  refine ⟨N - m, T + m, by omega, fun u hu => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show T ≤ u by omega)
  have e1 : observedColumn (finRule f hq) (listSeed seed) i (T + j) = c (T + j) i := rfl
  have e2 : observedColumn (finRule f hq) (listSeed seed) i (T + j + (N - m)) =
      c (T + (j + (N - m))) i := by
    rw [← add_assoc]
    rfl
  rw [e2, e1, hcol, hcol, hper j (by omega)]

/-- **The check accepts at an instance**: rule `218` from the seed `[1, 1]` with `T = 0`, the two
cells from `0`, and the word repeating at once. -/
theorem eventuallyPeriodic_observedColumn_of_blockingCheck_nonvacuous :
    blockingCheck (wolframRule 218) [1, 1] 0 0 2 1 = true := by
  decide +kernel

/-- **The independence of the outside cells is checked, not assumed**: at rule `90` from the single
seed, the one clear cell beside the seed stays clear under clear neighbours and is not blocked, so
the check rejects. -/
theorem blockingCheck_f90_single_eq_false :
    blockingCheck (wolframRule 90) [1] 0 1 1 1 = false := by
  decide +kernel

/-! ## The census -/

/-- The twenty-five pairs of the census, a table and a seed read from cell `0`: twelve seeds of
table `218` and thirteen of table `94`. -/
def blockingPairs : List (ℕ × List (ZMod 2)) := [
   (218, [1, 1]), (218, [1, 1, 1]), (218, [1, 0, 0, 1]), (218, [1, 0, 1, 1]),
   (218, [1, 1, 0, 1]), (218, [1, 1, 1, 1]), (218, [1, 0, 0, 1, 1]), (218, [1, 0, 1, 1, 1]),
   (218, [1, 1, 0, 0, 1]), (218, [1, 1, 0, 1, 1]), (218, [1, 1, 1, 0, 1]),
   (218, [1, 1, 1, 1, 1]), (94, [1]), (94, [1, 0, 1]), (94, [1, 1, 1]), (94, [1, 0, 1, 1]),
   (94, [1, 1, 0, 1]), (94, [1, 0, 0, 0, 1]), (94, [1, 0, 0, 1, 1]), (94, [1, 0, 1, 0, 1]),
   (94, [1, 0, 1, 1, 1]), (94, [1, 1, 0, 0, 1]), (94, [1, 1, 0, 1, 1]), (94, [1, 1, 1, 0, 1]),
   (94, [1, 1, 1, 1, 1])]

theorem length_blockingPairs : blockingPairs.length = 25 := by
  decide +kernel

/-- For each pair of `blockingPairs`, the parameters `(T, lo, len)` of a window at which the check
accepts with `N = 2`, as a table, a seed, `T`, `lo` and `len`. -/
def blockingCertificates : List (ℕ × List (ZMod 2) × ℕ × ℤ × ℕ) := [
   (218, [1, 1], 0, 0, 2), (218, [1, 1, 1], 0, 0, 2), (218, [1, 0, 0, 1], 3, -1, 2),
   (218, [1, 0, 1, 1], 2, 0, 2), (218, [1, 1, 0, 1], 0, 0, 2), (218, [1, 1, 1, 1], 0, 0, 2),
   (218, [1, 0, 0, 1, 1], 3, -1, 2), (218, [1, 0, 1, 1, 1], 2, 0, 2),
   (218, [1, 1, 0, 0, 1], 0, 0, 2), (218, [1, 1, 0, 1, 1], 0, 0, 2),
   (218, [1, 1, 1, 0, 1], 0, 0, 2), (218, [1, 1, 1, 1, 1], 0, 0, 2), (94, [1], 2, -1, 3),
   (94, [1, 0, 1], 0, 0, 3), (94, [1, 1, 1], 1, 0, 3), (94, [1, 0, 1, 1], 0, 0, 3),
   (94, [1, 1, 0, 1], 2, -1, 3), (94, [1, 0, 0, 0, 1], 2, -1, 3),
   (94, [1, 0, 0, 1, 1], 8, -3, 7), (94, [1, 0, 1, 0, 1], 0, 0, 3),
   (94, [1, 0, 1, 1, 1], 0, 0, 3), (94, [1, 1, 0, 0, 1], 8, -3, 7),
   (94, [1, 1, 0, 1, 1], 2, -1, 3), (94, [1, 1, 1, 0, 1], 1, 0, 3),
   (94, [1, 1, 1, 1, 1], 9, -2, 3)]

/-- The check accepts every certificate. -/
private theorem blockingCertificates_accepted :
    blockingCertificates.all (fun c =>
      blockingCheck (wolframRule c.1) c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 2) = true := by
  decide +kernel

/-- The window of every certificate contains cell `0`. -/
private theorem blockingCertificates_window :
    blockingCertificates.all (fun c => decide (c.2.2.2.1 ≤ 0 ∧ 0 < c.2.2.2.1 + c.2.2.2.2)) =
      true := by
  decide +kernel

/-- Every pair of the census has a certificate. -/
private theorem blockingCertificates_cover :
    blockingPairs.all (fun p =>
      blockingCertificates.any (fun c => c.1 == p.1 && decide (c.2.1 = p.2))) = true := by
  decide +kernel

/-- **The leftmost column is eventually periodic at the twenty-five pairs.** Each pair of a table
and a seed has a certificate whose window contains cell `0` and whose parameters the check
accepts, and the decided theorem turns the acceptance into the eventual periodicity of the column
at cell `0`. -/
theorem eventuallyPeriodic_observedColumn_blockingCensus :
    ∀ p ∈ blockingPairs, ∀ (hq : wolframRule p.1 0 0 0 = 0),
      DrivenColumns.EventuallyPeriodic
        (observedColumn (finRule (wolframRule p.1) hq) (listSeed p.2) 0) := by
  intro p hp hq
  have h1 := List.all_eq_true.mp blockingCertificates_cover p hp
  obtain ⟨⟨N', s', T, lo, len⟩, hc, hmatch⟩ := List.any_eq_true.mp h1
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmatch
  obtain ⟨hN', hs'⟩ := hmatch
  have hacc := List.all_eq_true.mp blockingCertificates_accepted _ hc
  have hwin := List.all_eq_true.mp blockingCertificates_window _ hc
  simp only [decide_eq_true_eq] at hwin
  subst hN' hs'
  exact eventuallyPeriodic_observedColumn_of_blockingCheck _ hq _ T lo len 2 hacc 0
    hwin.1 hwin.2

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_of_blockingCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_of_blockingCheck

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_blockingCensus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_blockingCensus
