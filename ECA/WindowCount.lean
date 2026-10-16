module

public import ECA.MarkovErrorCount
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Fin.VecNotation

/-!
# The Markov error count of a factor, and a window's count against its end factors' and columns'

Extends [RuleSpace] §4 Proposition 4.2, clause (ii), the driven interior, and is registered as
[RuleSpace] §4 Proposition 4.3, clauses (ii) and (iii), row RS-8.

`MarkovErrorCount.lean`'s Markov error count answers the next state itself from the last `k` states;
this file answers instead a fixed FACTOR of the next state — a function `π` of it — and compares
the two at a local rule's window. At a positive order a window's Markov error count is at least each
of its two end factors' counts and at most their sum, which is in turn at most the sum of its two
end columns' Markov error counts. The positive order is load-bearing in the upper bound, and the end
columns' own counts give the window no lower bound. The same sandwich holds at a window that
translates at a rational speed at most one, once its content is paired with the phase of its own
schedule and the leading end reads two cells.

One new condition is minted here. The **Markov error count of a factor** is the least number of
errors, over the functions of the last `k` states, in answering a fixed function of the next state
(`factorErrorCount`); `markovErrorCount` is its case at the identity factor.

## Main results

* `factorPredictorErrors`, `factorErrorCount` — the factor form of
  `predictorErrors`/`markovErrorCount`.
  `factorErrorCount_id` recovers that count at the identity factor;
  `factorErrorCount_le_markovErrorCount` and `factorErrorCount_le_markovErrorCount_comp` bound a
  factor's count by the state's own Markov error count, directly and through the read sequence.
* `markovErrorCount_observedWindow_le_add_factorErrorCount` — at a positive order, a local rule's
  window Markov error count is at most the sum of its two end factors' counts.
  `markovErrorCount_observedWindow_le_add_columns` is the same bound through the end columns'
  Markov error counts, via `factorErrorCount_le_markovErrorCount_comp`.
* `markovErrorCount_observedWindow_zero_memory_guard` — the guard: the positive-order hypothesis is
  load-bearing.
* `markovErrorCount_observedWindow_lt_column_f170` — the guard: the two end columns give the
  window's Markov error count no lower bound.
* `movingWindow`, `markovErrorCount_movingWindow_le_add_factorErrorCount` — the translating window,
  its content paired with the phase `t % q` of its schedule, and at a positive order and a speed
  `p / q ≤ 1` its Markov error count is at most the sum of its two end factors' counts, the trailing
  cell's and the two leading cells';
  `markovErrorCount_movingWindow_le_add_factorErrorCount_nonvacuous` meets the four hypotheses at
  rule `90`.
* `markovErrorCount_movingWindow_zero_memory_guard` — the guard: the positive order is load-bearing
  at the translating window as well, where at the zero rule the phase alone changes.

## Scope

Registered as [RuleSpace] §4 Proposition 4.3, clauses (ii) and (iii), row RS-8; [RuleSpace] §4
Proposition 4.2, clause (ii) is what is extended. The window theorems, the translating window's
included, are stated at a general local rule `LocalRule.finRule f hq`, never specialized beyond the
witnesses' and guards' own rules.
-/


@[expose] public section

namespace ECA

open LocalRule

open DrivenColumns

/-! ## The Markov error count of a factor -/

/-- **How many errors a fixed law on the last `k` symbols makes against a fixed factor of the next
state**,
before horizon `T`. -/
noncomputable def factorPredictorErrors {α β : Type*} [DecidableEq β] (k : ℕ) (π : α → β)
    (L : (Fin k → α) → β) (x : ℕ → α) (T : ℕ) : ℕ :=
  ((Finset.range T).filter fun t => L (fun i => x (t + (i : ℕ))) ≠ π (x (t + k))).card

/-- **The Markov error count of a factor**: the fewest errors any law on the last `k` symbols makes
answering a fixed factor of the next state, before `T`. -/
noncomputable def factorErrorCount {α β : Type*} [DecidableEq β] (k : ℕ) (π : α → β)
    (x : ℕ → α) (T : ℕ) : ℕ :=
  ⨅ L : (Fin k → α) → β, factorPredictorErrors k π L x T

/-- **The identity factor recovers the Markov error count.** -/
theorem factorErrorCount_id {α : Type*} [DecidableEq α] (k : ℕ) (x : ℕ → α) (T : ℕ) :
    factorErrorCount k (fun a : α => a) x T = markovErrorCount k x T := rfl

/-- **A factor never errs more than the state itself does**: a law `L` for the state gives the
law `π ∘ L` for the factor, which errs only where `L` does. -/
theorem factorErrorCount_le_markovErrorCount {α β : Type*} [DecidableEq α] [DecidableEq β]
    (k : ℕ) (π : α → β) (x : ℕ → α) (T : ℕ) :
    factorErrorCount k π x T ≤ markovErrorCount k x T := by
  have hne : Nonempty α := ⟨x 0⟩
  obtain ⟨L, hL⟩ := ciInf_mem (fun L : (Fin k → α) → α => predictorErrors k L x T)
  have hsub : ((Finset.range T).filter fun t => (π ∘ L) (fun i => x (t + (i : ℕ))) ≠ π (x (t + k)))
      ⊆ (Finset.range T).filter fun t => L (fun i => x (t + (i : ℕ))) ≠ x (t + k) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply] at ht ⊢
    exact ⟨ht.1, fun hEq => ht.2 (by rw [hEq])⟩
  calc factorErrorCount k π x T ≤ factorPredictorErrors k π (π ∘ L) x T := ciInf_le' _ (π ∘ L)
    _ ≤ predictorErrors k L x T := Finset.card_le_card hsub
    _ = markovErrorCount k x T := hL

/-- **A factor of the state's own sequence never errs more than the state's own Markov error count
of the READ sequence**: a law on the read sequence's history is a law on the state's history that
reads it through `π`, with the same errors. -/
theorem factorErrorCount_le_markovErrorCount_comp {α β : Type*} [DecidableEq β]
    (k : ℕ) (π : α → β) (x : ℕ → α) (T : ℕ) :
    factorErrorCount k π x T ≤ markovErrorCount k (fun t => π (x t)) T := by
  have hne : Nonempty β := ⟨π (x 0)⟩
  obtain ⟨M, hM⟩ := ciInf_mem
    (fun M : (Fin k → β) → β => predictorErrors k M (fun t => π (x t)) T)
  calc factorErrorCount k π x T
      ≤ factorPredictorErrors k π (fun w : Fin k → α => M (fun i => π (w i))) x T :=
        ciInf_le' _ (fun w : Fin k → α => M (fun i => π (w i)))
    _ = predictorErrors k M (fun t => π (x t)) T := rfl
    _ = markovErrorCount k (fun t => π (x t)) T := hM

/-! ## The window of a local rule -/

/-- **The window's law, built from an end pair**: cell `0` by `La`, cell `Fin.last m` by `Lb`, and
every interior cell by the rule at the LAST content read (the order hypothesis `hk` names the
index). -/
private noncomputable def LocalRule.windowLawOf (f : LocalRule) {m k : ℕ}
    (hk : 0 < k) (La Lb : (Fin k → (Fin (m + 1) → ZMod 2)) → ZMod 2) :
    (Fin k → (Fin (m + 1) → ZMod 2)) → (Fin (m + 1) → ZMod 2) :=
  fun hist j =>
    if hj0 : (j : ℕ) = 0 then La hist
    else if hjm : (j : ℕ) = m then Lb hist
    else f (hist ⟨k - 1, by omega⟩ ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)
           (hist ⟨k - 1, by omega⟩ j)
           (hist ⟨k - 1, by omega⟩ ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩)

theorem markovErrorCount_observedWindow_le_add_factorErrorCount
    (f : LocalRule) (hq : f 0 0 0 = 0) (s₀ : FiniteConfiguration)
    (a : ℤ) (m : ℕ) {k : ℕ} (hk : 0 < k) (T : ℕ) :
    markovErrorCount k (observedWindow (finRule f hq) s₀ a (m + 1)) T ≤
      factorErrorCount k (fun w : Fin (m + 1) → ZMod 2 => w 0)
          (observedWindow (finRule f hq) s₀ a (m + 1)) T +
      factorErrorCount k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m))
          (observedWindow (finRule f hq) s₀ a (m + 1)) T := by
  classical
  set wseq : ℕ → (Fin (m + 1) → ZMod 2) := observedWindow (finRule f hq) s₀ a (m + 1)
    with hwseq_def
  obtain ⟨La, hLa⟩ := ciInf_mem
    (fun L : (Fin k → (Fin (m + 1) → ZMod 2)) → ZMod 2 =>
      factorPredictorErrors k (fun w : Fin (m + 1) → ZMod 2 => w 0) L wseq T)
  obtain ⟨Lb, hLb⟩ := ciInf_mem
    (fun L : (Fin k → (Fin (m + 1) → ZMod 2)) → ZMod 2 =>
      factorPredictorErrors k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) L wseq T)
  have hmiss : ∀ t ∈ Finset.range T,
      La (fun i => wseq (t + (i : ℕ))) = wseq (t + k) 0 →
      Lb (fun i => wseq (t + (i : ℕ))) = wseq (t + k) (Fin.last m) →
      windowLawOf f hk La Lb (fun i => wseq (t + (i : ℕ))) = wseq (t + k) := by
    intro t _ hAeq hBeq
    have hlast : wseq (t + (k - 1)) = wseq (t + k - 1) := by congr 1; omega
    funext j
    simp only [windowLawOf]
    split_ifs with hj0 hjm
    · have hje : j = 0 := Fin.ext hj0
      rw [hje]; exact hAeq
    · have hje : j = Fin.last m := Fin.ext (by rw [Fin.val_last]; exact hjm)
      rw [hje]; exact hBeq
    · rw [hlast]
      have hjge : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
      have hjlt : (j : ℕ) < m := by have := j.isLt; omega
      have e1 : a + ((j : ℕ) : ℤ) - 1 = a + (((j : ℕ) - 1 : ℕ) : ℤ) := by push_cast [hjge]; ring
      have e2 : a + ((j : ℕ) : ℤ) + 1 = a + (((j : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
      change f (wseq (t + k - 1) ⟨(j : ℕ) - 1, by omega⟩)
        (wseq (t + k - 1) j) (wseq (t + k - 1) ⟨(j : ℕ) + 1, by omega⟩) = wseq (t + k) j
      change f (((finRule f hq)^[t + k - 1] s₀) (a + (((j : ℕ) - 1 : ℕ) : ℤ)))
            (((finRule f hq)^[t + k - 1] s₀) (a + ((j : ℕ) : ℤ)))
            (((finRule f hq)^[t + k - 1] s₀) (a + (((j : ℕ) + 1 : ℕ) : ℤ)))
        = ((finRule f hq)^[t + k] s₀) (a + ((j : ℕ) : ℤ))
      rw [← e1, ← e2]
      conv_rhs => rw [show t + k = (t + k - 1) + 1 by omega]
      rw [Function.iterate_succ_apply', finRule_apply]
  have hsub : ((Finset.range T).filter fun t =>
        windowLawOf f hk La Lb (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k))
      ⊆ ((Finset.range T).filter fun t =>
            La (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k) 0) ∪
        ((Finset.range T).filter fun t =>
            Lb (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k) (Fin.last m)) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htT, htne⟩ := ht
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    by_contra hc
    push Not at hc
    exact htne (hmiss t (Finset.mem_range.mpr htT) (hc.1 htT) (hc.2 htT))
  have hLa' : factorPredictorErrors k (fun w : Fin (m + 1) → ZMod 2 => w 0) La wseq T =
      factorErrorCount k (fun w : Fin (m + 1) → ZMod 2 => w 0) wseq T := hLa
  have hLb' : factorPredictorErrors k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) Lb wseq T =
      factorErrorCount k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) wseq T := hLb
  calc markovErrorCount k wseq T
      ≤ predictorErrors k (windowLawOf f hk La Lb) wseq T := ciInf_le' _ (windowLawOf f hk La Lb)
    _ ≤ factorPredictorErrors k (fun w : Fin (m + 1) → ZMod 2 => w 0) La wseq T +
        factorPredictorErrors k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) Lb wseq T := by
        calc predictorErrors k (windowLawOf f hk La Lb) wseq T
            ≤ (((Finset.range T).filter fun t =>
                  La (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k) 0) ∪
                ((Finset.range T).filter fun t =>
                  Lb (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k) (Fin.last m))).card :=
              Finset.card_le_card hsub
          _ ≤ _ + _ := Finset.card_union_le _ _
    _ = factorErrorCount k (fun w : Fin (m + 1) → ZMod 2 => w 0) wseq T +
        factorErrorCount k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) wseq T := by
        rw [hLa', hLb']

/-- **The window's count-currency form through the columns**: the factors bound followed by
`factorErrorCount_le_markovErrorCount_comp` at each end, the end coordinate of the window
being the observed column at that cell. -/
theorem markovErrorCount_observedWindow_le_add_columns
    (f : LocalRule) (hq : f 0 0 0 = 0) (s₀ : FiniteConfiguration)
    (a : ℤ) (m : ℕ) {k : ℕ} (hk : 0 < k) (T : ℕ) :
    markovErrorCount k (observedWindow (finRule f hq) s₀ a (m + 1)) T ≤
      markovErrorCount k (observedColumn (finRule f hq) s₀ a) T +
      markovErrorCount k (observedColumn (finRule f hq) s₀ (a + (m : ℤ))) T := by
  have h1 := markovErrorCount_observedWindow_le_add_factorErrorCount f hq s₀ a m hk T
  have hcolA : (fun t => (fun w : Fin (m + 1) → ZMod 2 => w 0)
      (observedWindow (finRule f hq) s₀ a (m + 1) t)) = observedColumn (finRule f hq) s₀ a := by
    funext t
    simp [observedWindow, observedColumn]
  have hcolB : (fun t => (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m))
      (observedWindow (finRule f hq) s₀ a (m + 1) t)) =
      observedColumn (finRule f hq) s₀ (a + (m : ℤ)) := by
    funext t
    simp [observedWindow, observedColumn, Fin.last]
  have h2 := factorErrorCount_le_markovErrorCount_comp k (fun w : Fin (m + 1) → ZMod 2 => w 0)
    (observedWindow (finRule f hq) s₀ a (m + 1)) T
  have h3 := factorErrorCount_le_markovErrorCount_comp k
    (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m))
    (observedWindow (finRule f hq) s₀ a (m + 1)) T
  rw [hcolA] at h2
  rw [hcolB] at h3
  omega

/-! ## The translating window: the sandwich at a rational speed -/

/-- **The translating window with its phase**: at step `t`, the `n` cells from `a + ⌊p t / q⌋`
read together, paired with the phase `t % q` of the window's own schedule. At `p = 0` the content
is `observedWindow`'s. -/
def movingWindow (U : FiniteConfiguration → FiniteConfiguration) (s₀ : FiniteConfiguration) (a : ℤ)
  (p q n : ℕ) :
    ℕ → (Fin n → ZMod 2) × ℕ :=
  fun t => (fun j => (U^[t] s₀) (a + ((p * t / q : ℕ) : ℤ) + ((j : ℕ) : ℤ)), t % q)

/-- The position `⌊p t / q⌋` splits along `t = t % q + q (t / q)`. -/
private theorem mul_div_eq_mod (p q t : ℕ) (hq0 : 0 < q) :
    p * t / q = p * (t % q) / q + p * (t / q) := by
  conv_lhs => rw [← Nat.mod_add_div t q]
  rw [Nat.mul_add, mul_left_comm, Nat.add_mul_div_left _ _ hq0]

/-- The next position `⌊p (t + 1) / q⌋` splits along the same phase `t % q`, so the move this
step is read off the phase alone. -/
private theorem mul_succ_div_eq (p q t : ℕ) (hq0 : 0 < q) :
    p * (t + 1) / q = p * (t % q + 1) / q + p * (t / q) := by
  have h : t + 1 = (t % q + 1) + q * (t / q) := by have := Nat.mod_add_div t q; omega
  rw [h, Nat.mul_add, mul_left_comm, Nat.add_mul_div_left _ _ hq0]

/-- At a speed at most one, the position moves by at most one cell a step. -/
private theorem div_succ_le (p q r : ℕ) (hq0 : 0 < q) (hpq : p ≤ q) :
    p * (r + 1) / q ≤ p * r / q + 1 := by
  calc p * (r + 1) / q ≤ (p * r + q) / q := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
    _ = p * r / q + 1 := Nat.add_div_right _ hq0

/-- **The translating window's law, built from an end pair**: cell `0` by `La`, the two leading
cells by `Lb`, the move this step read off the LAST state's phase, and every other cell by the
rule at the last content — one cell further along when the window moves (the order hypothesis
`hk` names the index). -/
private noncomputable def LocalRule.movingLawOf (f : LocalRule) {m k : ℕ}
    (hk : 0 < k) (p q : ℕ)
    (La : (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → ZMod 2)
    (Lb : (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → ZMod 2 × ZMod 2) :
    (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → (Fin (m + 3) → ZMod 2) × ℕ :=
  fun hist =>
    (fun j =>
      if hj0 : (j : ℕ) = 0 then La hist
      else if hj1 : (j : ℕ) = m + 1 then (Lb hist).1
      else if hj2 : (j : ℕ) = m + 2 then (Lb hist).2
      else if p * (hist ⟨k - 1, by omega⟩).2 / q < p * ((hist ⟨k - 1, by omega⟩).2 + 1) / q then
        f ((hist ⟨k - 1, by omega⟩).1 j)
          ((hist ⟨k - 1, by omega⟩).1 ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩)
          ((hist ⟨k - 1, by omega⟩).1 ⟨(j : ℕ) + 2, by have := j.isLt; omega⟩)
      else
        f ((hist ⟨k - 1, by omega⟩).1 ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)
          ((hist ⟨k - 1, by omega⟩).1 j)
          ((hist ⟨k - 1, by omega⟩).1 ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩),
     ((hist ⟨k - 1, by omega⟩).2 + 1) % q)

/-- **The window's count at a rational speed is at most the sum of its two end factors'.** The
window's next content is one fixed function of its last content, its phase and the two end
factors: the phase says whether the window moves this step (`⌊p (t + 1) / q⌋ − ⌊p t / q⌋`
depends on `t % q` alone), every cell strictly inside has its neighbourhood inside either way, the
trailing end's next cell is its own factor, and the leading end's two cells are its
([RuleSpace] §4 Proposition 4.3's sandwich, rows RS-7 and RS-8, at a window whose ends move). -/
theorem markovErrorCount_movingWindow_le_add_factorErrorCount
    (f : LocalRule) (hq : f 0 0 0 = 0) (s₀ : FiniteConfiguration) (a : ℤ)
    {p q : ℕ} (hq0 : 0 < q) (hpq : p ≤ q) (m : ℕ) {k : ℕ} (hk : 0 < k) (T : ℕ) :
    markovErrorCount k (movingWindow (finRule f hq) s₀ a p q (m + 3)) T ≤
      factorErrorCount k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0)
          (movingWindow (finRule f hq) s₀ a p q (m + 3)) T +
      factorErrorCount k
          (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
          (movingWindow (finRule f hq) s₀ a p q (m + 3)) T := by
  classical
  set wseq : ℕ → (Fin (m + 3) → ZMod 2) × ℕ := movingWindow (finRule f hq) s₀ a p q (m + 3)
    with hwseq_def
  obtain ⟨La, hLa⟩ := ciInf_mem
    (fun L : (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → ZMod 2 =>
      factorPredictorErrors k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0) L wseq T)
  obtain ⟨Lb, hLb⟩ := ciInf_mem
    (fun L : (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → ZMod 2 × ZMod 2 =>
      factorPredictorErrors k
        (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
        L wseq T)
  have hmiss : ∀ t ∈ Finset.range T,
      La (fun i => wseq (t + (i : ℕ))) = (wseq (t + k)).1 0 →
      Lb (fun i => wseq (t + (i : ℕ))) =
        ((wseq (t + k)).1 ⟨m + 1, by omega⟩, (wseq (t + k)).1 (Fin.last (m + 2))) →
      movingLawOf f hk p q La Lb (fun i => wseq (t + (i : ℕ))) = wseq (t + k) := by
    intro t _ hAeq hBeq
    obtain ⟨u, hu⟩ : ∃ u, t + k = u + 1 := ⟨t + k - 1, by omega⟩
    rw [hu] at hAeq hBeq ⊢
    have hlast : wseq (t + (k - 1)) = wseq u := by congr 1; omega
    have hpos := mul_succ_div_eq p q u hq0
    have hpos' := mul_div_eq_mod p q u hq0
    have hmono : p * (u % q) / q ≤ p * (u % q + 1) / q :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_succ _))
    have hle := div_succ_le p q (u % q) hq0 hpq
    refine Prod.ext ?_ ?_
    · funext j
      simp only [movingLawOf]
      split_ifs with hj0 hj1 hj2 hmv
      · have hje : j = 0 := Fin.ext hj0
        rw [hje]; exact hAeq
      · have hje : j = ⟨m + 1, by omega⟩ := Fin.ext hj1
        rw [hje]; exact congrArg Prod.fst hBeq
      · have hje : j = Fin.last (m + 2) := Fin.ext (by rw [Fin.val_last]; exact hj2)
        rw [hje]; exact congrArg Prod.snd hBeq
      · -- the window moves this step
        rw [hlast] at hmv ⊢
        change p * (u % q) / q < p * (u % q + 1) / q at hmv
        have hstep : p * (u + 1) / q = p * u / q + 1 := by rw [hpos, hpos']; omega
        have hjlt : (j : ℕ) < m + 1 := by have := j.isLt; omega
        change f (((finRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + ((j : ℕ) : ℤ)))
            (((finRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + (((j : ℕ) + 1 : ℕ) : ℤ)))
            (((finRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + (((j : ℕ) + 2 : ℕ) : ℤ)))
          = ((finRule f hq)^[u + 1] s₀) (a + ((p * (u + 1) / q : ℕ) : ℤ) + ((j : ℕ) : ℤ))
        rw [hstep, Function.iterate_succ_apply', finRule_apply]
        congr 2 <;> push_cast <;> ring
      · -- the window stays this step
        rw [hlast] at hmv ⊢
        change ¬ p * (u % q) / q < p * (u % q + 1) / q at hmv
        have hstep : p * (u + 1) / q = p * u / q := by rw [hpos, hpos']; omega
        have hjge : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
        have hjlt : (j : ℕ) < m + 2 := by have := j.isLt; omega
        change f (((finRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + (((j : ℕ) - 1 : ℕ) : ℤ)))
            (((finRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + ((j : ℕ) : ℤ)))
            (((finRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + (((j : ℕ) + 1 : ℕ) : ℤ)))
          = ((finRule f hq)^[u + 1] s₀) (a + ((p * (u + 1) / q : ℕ) : ℤ) + ((j : ℕ) : ℤ))
        rw [hstep, Function.iterate_succ_apply', finRule_apply]
        congr 2 <;> push_cast [hjge] <;> ring
    · simp only [movingLawOf]
      change ((wseq (t + (k - 1))).2 + 1) % q = (u + 1) % q
      rw [hlast]
      exact Nat.mod_add_mod _ _ _
  have hsub : ((Finset.range T).filter fun t =>
        movingLawOf f hk p q La Lb (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k))
      ⊆ ((Finset.range T).filter fun t =>
            La (fun i => wseq (t + (i : ℕ))) ≠ (wseq (t + k)).1 0) ∪
        ((Finset.range T).filter fun t =>
            Lb (fun i => wseq (t + (i : ℕ))) ≠
              ((wseq (t + k)).1 ⟨m + 1, by omega⟩, (wseq (t + k)).1 (Fin.last (m + 2)))) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htT, htne⟩ := ht
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    by_contra hc
    push Not at hc
    exact htne (hmiss t (Finset.mem_range.mpr htT) (hc.1 htT) (hc.2 htT))
  have hLa' : factorPredictorErrors k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0) La wseq T =
      factorErrorCount k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0) wseq T := hLa
  have hLb' : factorPredictorErrors k
      (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
      Lb wseq T =
      factorErrorCount k
        (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
        wseq T := hLb
  calc markovErrorCount k wseq T
      ≤ predictorErrors k (movingLawOf f hk p q La Lb) wseq T :=
        ciInf_le' _ (movingLawOf f hk p q La Lb)
    _ ≤ factorPredictorErrors k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0) La wseq T +
        factorPredictorErrors k
          (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
          Lb wseq T := by
        calc predictorErrors k (movingLawOf f hk p q La Lb) wseq T
            ≤ (((Finset.range T).filter fun t =>
                  La (fun i => wseq (t + (i : ℕ))) ≠ (wseq (t + k)).1 0) ∪
                ((Finset.range T).filter fun t =>
                  Lb (fun i => wseq (t + (i : ℕ))) ≠
                    ((wseq (t + k)).1 ⟨m + 1, by omega⟩,
                      (wseq (t + k)).1 (Fin.last (m + 2))))).card :=
              Finset.card_le_card hsub
          _ ≤ _ + _ := Finset.card_union_le _ _
    _ = _ := by rw [hLa', hLb']

/-- **Both hypotheses of the translating window's bound are met at once, and the bound holds
there**: rule `90`, the single seed, start `0`, speed `1/2`, width `3`, order `1` and horizon
`4` ([RuleSpace] §4 Proposition 4.3, row RS-8, at a window whose ends move). -/
theorem markovErrorCount_movingWindow_le_add_factorErrorCount_nonvacuous :
    f90 0 0 0 = 0 ∧ 0 < 2 ∧ 1 ≤ 2 ∧ 0 < 1 ∧
      markovErrorCount 1 (movingWindow (finRule f90 hq90) (Finsupp.single 0 1) 0 1 2 3) 4 ≤
        factorErrorCount 1 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0)
            (movingWindow (finRule f90 hq90) (Finsupp.single 0 1) 0 1 2 3) 4 +
        factorErrorCount 1 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2))
            (movingWindow (finRule f90 hq90) (Finsupp.single 0 1) 0 1 2 3) 4 :=
  ⟨hq90, by norm_num, by norm_num, by norm_num,
    markovErrorCount_movingWindow_le_add_factorErrorCount f90 hq90 (Finsupp.single 0 1) 0
      (by norm_num) (by norm_num) 0 (by norm_num) 4⟩

/-! ## The guard pair -/

/-- **A repeated context with two different targets forces at least one error.** -/
private theorem one_le_markovErrorCount_of_context_ne {α : Type*} [DecidableEq α]
    (k : ℕ) (x : ℕ → α) (T : ℕ) {t₁ t₂ : ℕ} (ht₁ : t₁ < T) (ht₂ : t₂ < T)
    (hctx : (fun i : Fin k => x (t₁ + (i : ℕ))) = (fun i : Fin k => x (t₂ + (i : ℕ))))
    (hne : x (t₁ + k) ≠ x (t₂ + k)) :
    1 ≤ markovErrorCount k x T := by
  have hαne : Nonempty α := ⟨x 0⟩
  by_contra hc
  push Not at hc
  have h0 : markovErrorCount k x T = 0 := by omega
  obtain ⟨L, hL0⟩ := ciInf_mem (fun L : (Fin k → α) → α => predictorErrors k L x T)
  have hL : predictorErrors k L x T = markovErrorCount k x T := hL0
  rw [h0] at hL
  unfold predictorErrors at hL
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hL
  have hm1 : L (fun i : Fin k => x (t₁ + (i : ℕ))) = x (t₁ + k) :=
    not_not.mp (hL (Finset.mem_range.mpr ht₁))
  have hm2 : L (fun i : Fin k => x (t₂ + (i : ℕ))) = x (t₂ + k) :=
    not_not.mp (hL (Finset.mem_range.mpr ht₂))
  rw [hctx] at hm1
  exact hne (hm1.symm.trans hm2)

/-- **Guard: the positive-order hypothesis is load-bearing.** At the rule sending everything to
zero, from the single seed, the window of cells `-1, 0, 1` holds two different contents at steps
`0` and `1`, so an order-`0` law that reads nothing errs on one of them, while both end columns are
zero throughout. -/
theorem markovErrorCount_observedWindow_zero_memory_guard :
    ¬ (markovErrorCount 0
          (observedWindow (finRule (fun _ _ _ => (0 : ZMod 2)) rfl)
            (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-1) 3) 2 ≤
        markovErrorCount 0
          (observedColumn (finRule (fun _ _ _ => (0 : ZMod 2)) rfl)
            (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-1)) 2 +
        markovErrorCount 0
          (observedColumn (finRule (fun _ _ _ => (0 : ZMod 2)) rfl)
            (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) 2) := by
  classical
  set f₀ : LocalRule := fun _ _ _ => 0 with hf₀_def
  have hq₀ : f₀ 0 0 0 = 0 := rfl
  set s₀ : FiniteConfiguration := Finsupp.single (0 : ℤ) (1 : ZMod 2) with hs₀_def
  set window : ℕ → (Fin 3 → ZMod 2) := observedWindow (finRule f₀ hq₀) s₀ (-1) 3 with hwin_def
  set colA : ℕ → ZMod 2 := observedColumn (finRule f₀ hq₀) s₀ (-1) with hcolA_def
  set colB : ℕ → ZMod 2 := observedColumn (finRule f₀ hq₀) s₀ 1 with hcolB_def
  have hUzero : ∀ (s : FiniteConfiguration) (i : ℤ), finRule f₀ hq₀ s i = 0 := by
    intro s i; rw [finRule_apply]
  have hcolAzero : ∀ t, colA t = 0 := by
    intro t
    rw [hcolA_def]
    change ((finRule f₀ hq₀)^[t] s₀) (-1) = 0
    cases t with
    | zero => change s₀ (-1) = 0; exact Finsupp.single_eq_of_ne (by norm_num)
    | succ n => rw [Function.iterate_succ_apply']; exact hUzero _ _
  have hcolBzero : ∀ t, colB t = 0 := by
    intro t
    rw [hcolB_def]
    change ((finRule f₀ hq₀)^[t] s₀) 1 = 0
    cases t with
    | zero => change s₀ 1 = 0; exact Finsupp.single_eq_of_ne (by norm_num)
    | succ n => rw [Function.iterate_succ_apply']; exact hUzero _ _
  have hcolA0 : markovErrorCount 0 colA 2 = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    calc markovErrorCount 0 colA 2
        ≤ predictorErrors 0 (fun _ => 0) colA 2 := ciInf_le' _ (fun _ => 0)
      _ = 0 := by
        unfold predictorErrors
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _
        simp [hcolAzero]
  have hcolB0 : markovErrorCount 0 colB 2 = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    calc markovErrorCount 0 colB 2
        ≤ predictorErrors 0 (fun _ => 0) colB 2 := ciInf_le' _ (fun _ => 0)
      _ = 0 := by
        unfold predictorErrors
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _
        simp [hcolBzero]
  have hw0 : window 0 = ![0, 1, 0] := by
    funext j
    change s₀ (-1 + ((j : ℕ) : ℤ)) = ![(0 : ZMod 2), 1, 0] j
    fin_cases j <;> norm_num [hs₀_def, Finsupp.single_apply]
  have hw1 : window 1 = ![0, 0, 0] := by
    funext j
    change ((finRule f₀ hq₀) s₀) (-1 + ((j : ℕ) : ℤ)) = ![(0 : ZMod 2), 0, 0] j
    rw [hUzero]
    fin_cases j <;> norm_num
  have hne : window 0 ≠ window 1 := by rw [hw0, hw1]; decide
  have h1 := one_le_markovErrorCount_of_context_ne 0 window 2
    (show (0 : ℕ) < 2 by norm_num) (show (1 : ℕ) < 2 by norm_num)
    (funext (fun i => i.elim0)) hne
  rw [hcolA0, hcolB0]
  omega

/-- **Guard: the two end columns give the window's Markov error count no lower bound.** At the shift
from the state with cell `1` set, the window of cells `0` and `1` holds three different contents at
steps `0`, `1`, `2`, so a law at order one never errs in three steps, while the column at cell
`0` reads `0, 1, 0, 0` and has met `0` followed by `1` and by `0`. -/
theorem markovErrorCount_observedWindow_lt_column_f170 :
    markovErrorCount 1
        (observedWindow (finRule f170 hq170)
          (Finsupp.single (1 : ℤ) (1 : ZMod 2)) 0 2) 3 = 0 ∧
      0 < markovErrorCount 1
        (observedColumn (finRule f170 hq170)
          (Finsupp.single (1 : ℤ) (1 : ZMod 2)) 0) 3 := by
  classical
  set s₀ : FiniteConfiguration := Finsupp.single (1 : ℤ) (1 : ZMod 2) with hs₀_def
  set window : ℕ → (Fin 2 → ZMod 2) := observedWindow (finRule f170 hq170) s₀ 0 2 with hwin_def
  set col0 : ℕ → ZMod 2 := observedColumn (finRule f170 hq170) s₀ 0 with hcol0_def
  have hiter : ∀ (t : ℕ) (s : FiniteConfiguration) (j : ℤ),
      ((finRule f170 hq170)^[t] s) j = s (j + t) := by
    intro t
    induction t with
    | zero => intro s j; simp
    | succ t ih =>
      intro s j
      rw [Function.iterate_succ_apply, ih, finRule_apply]
      change s (j + (t : ℤ) + 1) = s (j + ((t + 1 : ℕ) : ℤ))
      rw [Nat.cast_succ, add_assoc]
  have hwinval : ∀ (t : ℕ) (j : Fin 2), window t j = s₀ (((j : ℕ) : ℤ) + (t : ℤ)) := by
    intro t j
    rw [hwin_def]
    change ((finRule f170 hq170)^[t] s₀) (0 + ((j : ℕ) : ℤ)) = s₀ (((j : ℕ) : ℤ) + (t : ℤ))
    rw [zero_add, hiter]
  have hcolval : ∀ t : ℕ, col0 t = s₀ ((t : ℤ)) := by
    intro t
    rw [hcol0_def]
    change ((finRule f170 hq170)^[t] s₀) 0 = s₀ (t : ℤ)
    rw [hiter, zero_add]
  have hs00 : s₀ 0 = 0 := Finsupp.single_eq_of_ne (by norm_num)
  have hs01 : s₀ 1 = 1 := Finsupp.single_eq_same
  have hs02 : s₀ 2 = 0 := Finsupp.single_eq_of_ne (by norm_num)
  have hs03 : s₀ 3 = 0 := Finsupp.single_eq_of_ne (by norm_num)
  have hs04 : s₀ 4 = 0 := Finsupp.single_eq_of_ne (by norm_num)
  have hw0 : window 0 = ![0, 1] := by
    funext j
    rw [hwinval]
    fin_cases j <;> norm_num [hs00, hs01]
  have hw1 : window 1 = ![1, 0] := by
    funext j
    rw [hwinval]
    fin_cases j <;> norm_num [hs01, hs02]
  have hw2 : window 2 = ![0, 0] := by
    funext j
    rw [hwinval]
    fin_cases j <;> norm_num [hs02, hs03]
  have hw3 : window 3 = ![0, 0] := by
    funext j
    rw [hwinval]
    fin_cases j <;> norm_num [hs03, hs04]
  have hc0 : col0 0 = 0 := by rw [hcolval]; exact hs00
  have hc1 : col0 1 = 1 := by rw [hcolval]; exact hs01
  have hc2 : col0 2 = 0 := by rw [hcolval]; exact hs02
  have hc3 : col0 3 = 0 := by rw [hcolval]; exact hs03
  refine ⟨?_, ?_⟩
  · apply le_antisymm _ (Nat.zero_le _)
    set Lgood : (Fin 1 → (Fin 2 → ZMod 2)) → (Fin 2 → ZMod 2) := fun hist =>
      if hist 0 = (![0, 1] : Fin 2 → ZMod 2) then (![1, 0] : Fin 2 → ZMod 2)
      else if hist 0 = (![1, 0] : Fin 2 → ZMod 2) then (![0, 0] : Fin 2 → ZMod 2)
      else (![0, 0] : Fin 2 → ZMod 2)
      with hLgood_def
    calc markovErrorCount 1 window 3 ≤ predictorErrors 1 Lgood window 3 := ciInf_le' _ Lgood
      _ = 0 := by
        unfold predictorErrors
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t ht
        rw [Finset.mem_range] at ht
        simp only [not_not]
        interval_cases t
        · have hc : (fun i : Fin 1 => window (0 + (i : ℕ))) = fun _ => window 0 := by
            funext i; norm_num
          change Lgood (fun i => window (0 + (i : ℕ))) = window 1
          rw [hc, hw0, hw1]
          decide
        · have hc : (fun i : Fin 1 => window (1 + (i : ℕ))) = fun _ => window 1 := by
            funext i; norm_num
          change Lgood (fun i => window (1 + (i : ℕ))) = window 2
          rw [hc, hw1, hw2]
          decide
        · have hc : (fun i : Fin 1 => window (2 + (i : ℕ))) = fun _ => window 2 := by
            funext i; norm_num
          change Lgood (fun i => window (2 + (i : ℕ))) = window 3
          rw [hc, hw2, hw3]
          decide
  · have hctx : (fun i : Fin 1 => col0 (0 + (i : ℕ))) = (fun i : Fin 1 => col0 (2 + (i : ℕ))) := by
      funext i
      fin_cases i
      change col0 0 = col0 2
      rw [hc0, hc2]
    have hne : col0 (0 + 1) ≠ col0 (2 + 1) := by
      change col0 1 ≠ col0 3
      rw [hc1, hc3]
      decide
    have h1 := one_le_markovErrorCount_of_context_ne 1 col0 3
      (show (0 : ℕ) < 3 by norm_num) (show (2 : ℕ) < 3 by norm_num) hctx hne
    omega

/-- **Guard: the positive-order hypothesis of the translating window's bound is load-bearing.**
At the rule sending everything to zero, from the single seed, the window of three cells from `5`
lies in the quiescent region and its content never changes, but its phase does: at speed `1/2` the
states at steps `0` and `1` differ in the phase alone, so an order-`0` law that reads nothing
errs on one of them, while both end factors are zero throughout. -/
theorem markovErrorCount_movingWindow_zero_memory_guard :
    ¬ (markovErrorCount 0
          (movingWindow (finRule (fun _ _ _ => (0 : ZMod 2)) rfl)
            (Finsupp.single (0 : ℤ) 1) 5 1 2 3) 2 ≤
        factorErrorCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0)
            (movingWindow (finRule (fun _ _ _ => (0 : ZMod 2)) rfl)
              (Finsupp.single (0 : ℤ) 1) 5 1 2 3) 2 +
        factorErrorCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2))
            (movingWindow (finRule (fun _ _ _ => (0 : ZMod 2)) rfl)
              (Finsupp.single (0 : ℤ) 1) 5 1 2 3) 2) := by
  classical
  set f₀ : LocalRule := fun _ _ _ => 0 with hf₀_def
  have hq₀ : f₀ 0 0 0 = 0 := rfl
  set s₀ : FiniteConfiguration := Finsupp.single (0 : ℤ) (1 : ZMod 2) with hs₀_def
  set window : ℕ → (Fin 3 → ZMod 2) × ℕ := movingWindow (finRule f₀ hq₀) s₀ 5 1 2 3
    with hwin_def
  have hUzero : ∀ (s : FiniteConfiguration) (i : ℤ), finRule f₀ hq₀ s i = 0 := by
    intro s i; rw [finRule_apply]
  have hcontent : ∀ (t : ℕ) (j : Fin 3), (window t).1 j = 0 := by
    intro t j
    change ((finRule f₀ hq₀)^[t] s₀) (5 + ((1 * t / 2 : ℕ) : ℤ) + ((j : ℕ) : ℤ)) = 0
    cases t with
    | zero =>
      change s₀ (5 + ((1 * 0 / 2 : ℕ) : ℤ) + ((j : ℕ) : ℤ)) = 0
      exact Finsupp.single_eq_of_ne (by have := j.isLt; omega)
    | succ n => rw [Function.iterate_succ_apply']; exact hUzero _ _
  have hA0 : factorErrorCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0) window 2 = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    calc factorErrorCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0) window 2
        ≤ factorPredictorErrors 0 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0) (fun _ => 0) window 2 :=
          ciInf_le' _ (fun _ => 0)
      _ = 0 := by
        unfold factorPredictorErrors
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _
        simp [hcontent]
  have hB0 : factorErrorCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2)) window 2 = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    calc factorErrorCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2)) window 2
        ≤ factorPredictorErrors 0 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2)) (fun _ => (0, 0))
            window 2 :=
          ciInf_le' _ (fun _ => (0, 0))
      _ = 0 := by
        unfold factorPredictorErrors
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _
        simp [hcontent]
  have hne : window 0 ≠ window 1 := by
    intro h
    have h2 := congrArg Prod.snd h
    change (0 : ℕ) % 2 = 1 % 2 at h2
    omega
  have h1 := one_le_markovErrorCount_of_context_ne 0 window 2
    (show (0 : ℕ) < 2 by norm_num) (show (1 : ℕ) < 2 by norm_num)
    (funext (fun i => i.elim0)) hne
  rw [hA0, hB0]
  omega

end ECA

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

/-- info: 'ECA.factorErrorCount_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.factorErrorCount_id

set_option linter.style.longLine false in
/-- info: 'ECA.factorErrorCount_le_markovErrorCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.factorErrorCount_le_markovErrorCount

set_option linter.style.longLine false in
/-- info: 'ECA.factorErrorCount_le_markovErrorCount_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.factorErrorCount_le_markovErrorCount_comp

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_observedWindow_le_add_factorErrorCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_observedWindow_le_add_factorErrorCount

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_observedWindow_le_add_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_observedWindow_le_add_columns

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_observedWindow_zero_memory_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_observedWindow_zero_memory_guard

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_observedWindow_lt_column_f170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_observedWindow_lt_column_f170

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_movingWindow_le_add_factorErrorCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_movingWindow_le_add_factorErrorCount

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_movingWindow_le_add_factorErrorCount_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_movingWindow_le_add_factorErrorCount_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.markovErrorCount_movingWindow_zero_memory_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.markovErrorCount_movingWindow_zero_memory_guard
