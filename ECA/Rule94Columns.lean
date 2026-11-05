module

public import ECA.EdgeColumns
public import ECA.ReproducedPatterns
public import ECA.Doubling
import all ECA.EdgeColumns
import all ECA.EdgeWindow
import all ECA.EndpointClasses

/-!
# Rule `94` reproduces exactly the nonzero translates of doubled patterns
([RuleSpace] §5)

A rule agreeing with rule `90` at equal adjacent cells reproduces every nonzero doubled pattern and
every translate of one. Rule `94` is such a rule, and the question is whether it reproduces
anything else. At a quiescent rule with `f 0 0 1 = 1` the window read from the leftmost set cell of
a reproduced pattern `p` is purely periodic in time at every gap, so the window of width
`diam p + 2` of the orbit of `p` is a family of purely periodic columns obeying the window
recurrence, with its first cell set and its last two cells clear. The statement that at rule `94`
such a family has the cells `2k` and `2k + 1` equal at time `0` is stated here as a proposition,
`PeriodicColumnsPaired94`, and proved by a column induction. From it, the cells of the window of
`p` come in equal pairs, so `p` is a translate of a doubled pattern.

## Main results

* `PeriodicColumnsPaired94` — the column statement, as a proposition: a family of purely periodic
  columns obeying rule `94`'s window recurrence below a width, with its first cell set and at least
  two cells clear from `d` on at time `0`, has the cells `2k` and `2k + 1` equal at time `0` for
  every pair inside the width.
* `periodicColumnsPaired94` / `periodicColumnsPaired94_nonvacuous` /
  `not_periodicColumnsPaired94_one_clear` — that proposition is true, its hypotheses meet at
  width `4`, and with one clear cell instead of two it fails at width `4`.
* `reproduces_iff_dbl_f94_of` — from that proposition, rule `94` reproduces a pattern exactly when
  it is nonzero and a translate of a doubled pattern.
* `reproduces_iff_dbl_f94` — rule `94` reproduces a pattern exactly when it is nonzero and a
  translate of a doubled pattern, with no hypothesis.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- **A family of purely periodic columns at rule `94` has its cells paired**: a family `e n j`
obeying the window recurrence of rule `94` below the width `W`, with `e 0 0 = 1`, clear cells from
`d` on at time `0` with `d + 2 ≤ W`, and every column of period `t`, has
`e 0 (2 * k) = e 0 (2 * k + 1)` at every `k` with `2 * k + 1 < W`. -/
def PeriodicColumnsPaired94 : Prop :=
  ∀ (e : ℕ → ℕ → ZMod 2) (W d t : ℕ),
    (∀ n j, j < W → e (n + 1) j =
      f94 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) →
    e 0 0 = 1 → d + 2 ≤ W → (∀ j, d ≤ j → j < W → e 0 j = 0) → 0 < t →
    (∀ n j, j < W → e (n + t) j = e n j) →
    ∀ k, 2 * k + 1 < W → e 0 (2 * k) = e 0 (2 * k + 1)

/-- Rule `94` at equal cells on the left: the two forms agree. -/
private theorem f94_aac (a c : ZMod 2) : f94 a a c = f94 a c c := by
  revert a c; decide

/-- Rule `94` at equal cells on the left and a clear cell. -/
private theorem f94_aa0 (a : ZMod 2) : f94 a a 0 = a := by
  revert a; decide

/-- Two consecutive rule `94` values zero force four equal cells. -/
private theorem f94_pairs_zero (a b c d : ZMod 2) (h1 : f94 a b c = 0) (h2 : f94 b c d = 0) :
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1) := by
  revert a b c d; decide

set_option synthInstance.maxSize 4096 in
/-- Four consecutive rule `94` values one leave two adjacent clear cells among the first five. -/
private theorem f94_chain_a (a0 a1 a2 a3 a4 a5 : ZMod 2) (h0 : f94 a0 a1 a2 = 1)
    (h1 : f94 a1 a2 a3 = 1) (h2 : f94 a2 a3 a4 = 1) (h3 : f94 a3 a4 a5 = 1) :
    (a0 = 0 ∧ a1 = 0) ∨ (a1 = 0 ∧ a2 = 0) ∨ (a2 = 0 ∧ a3 = 0) ∨ (a3 = 0 ∧ a4 = 0) := by
  revert a0 a1 a2 a3 a4 a5; decide

/-- The same with the middle pair unequal. -/
private theorem f94_chain_b (a0 a1 a2 a3 a4 a5 : ZMod 2) (h0 : f94 a0 a1 a2 = 1)
    (h1 : f94 a1 a2 a3 = 1) (h2 : f94 a2 a3 a4 = 1) (h3 : f94 a3 a4 a5 = 1) (hne : a1 ≠ a2) :
    (a2 = 0 ∧ a3 = 0) ∨ (a3 = 0 ∧ a4 = 0) ∨ (a1 = 0 ∧ a4 = 0 ∧ a5 = 0) := by
  revert a0 a1 a2 a3 a4 a5; decide

set_option synthInstance.maxSize 4096 in
/-- The same with the first pair equal and the third pair unequal. -/
private theorem f94_chain_c (a0 a1 a2 a3 a4 a5 : ZMod 2) (h0 : f94 a0 a1 a2 = 1)
    (h1 : f94 a1 a2 a3 = 1) (h2 : f94 a2 a3 a4 = 1) (h3 : f94 a3 a4 a5 = 1) (heq : a0 = a1)
    (hne : a2 ≠ a3) : a3 = 0 ∧ a4 = 0 := by
  revert a0 a1 a2 a3 a4 a5; decide

/-- **No two adjacent clear cells above an unequal pair.** In a family of purely periodic columns
at rule `94` with the pair `(b, b + 1)` equal and the pair `(b + 2, b + 3)` unequal at every time,
and the column `b + 2` not clear at every time, no two adjacent cells from `b + 2` on are clear at
the same time. -/
private theorem pairClaim94 (e : ℕ → ℕ → ZMod 2) (W t b : ℕ)
    (hr : ∀ n j, j + 2 < W → e (n + 1) (j + 2) = f94 (e n j) (e n (j + 1)) (e n (j + 2)))
    (ht : 0 < t) (hper : ∀ n j, j < W → e (n + t) j = e n j)
    (hlow : ∀ n, e n b = e n (b + 1)) (hD : ∀ n, e n (b + 2) ≠ e n (b + 3))
    (hnc : ¬ ∀ n, e n (b + 2) = 0) :
    ∀ j, b + 2 ≤ j → j + 1 < W → ∀ n, ¬(e n j = 0 ∧ e n (j + 1) = 0) := by
  have hcz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hperk : ∀ s n j, j < W → e (n + s * t) j = e n j := by
    intro s
    induction s with
    | zero => intro n j _; simp
    | succ s ih =>
      intro n j hj
      rw [Nat.succ_mul, ← add_assoc, hper _ _ hj, ih n j hj]
  have hper2 : ∀ n j, j < W → e (n + 2 * t) j = e n j := fun n j hj => hperk 2 n j hj
  have main : ∀ j, b + 2 ≤ j → j + 1 < W →
      (∀ i, b + 2 ≤ i → i < j → ∀ n, ¬(e n i = 0 ∧ e n (i + 1) = 0)) →
      ∀ m', e (m' + 2) j = 0 → e (m' + 2) (j + 1) = 0 →
        j = b + 5 ∧ e m' j = 0 ∧ e m' (j + 1) = 0 ∧ e m' (b + 2) = 0 ∧
          e (m' + 1) (b + 2) = 0 := by
    intro j hj hjW IH m' hQ0 hQ1
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    have h1 : f94 (e (m' + 1) i) (e (m' + 1) (i + 1)) (e (m' + 1) (i + 2)) = 0 :=
      (hr (m' + 1) i (by omega)).symm.trans hQ0
    have h2 : f94 (e (m' + 1) (i + 1)) (e (m' + 1) (i + 2)) (e (m' + 1) (i + 3)) = 0 :=
      (hr (m' + 1) (i + 1) (by omega)).symm.trans hQ1
    have hE := f94_pairs_zero _ _ _ _ h1 h2
    have e23 : e (m' + 1) (i + 2) = e (m' + 1) (i + 3) := by
      rcases hE with ⟨_, _, a, c⟩ | ⟨_, _, a, c⟩ <;> rw [a, c]
    have e12 : e (m' + 1) (i + 1) = e (m' + 1) (i + 2) := by
      rcases hE with ⟨_, a, c, _⟩ | ⟨_, a, c, _⟩ <;> rw [a, c]
    rcases (by omega : i = b ∨ i = b + 1 ∨ b + 2 ≤ i) with hi | hi | hi
    · exact (hD (m' + 1) (by rw [← hi]; exact e23)).elim
    · exact (hD (m' + 1) (by subst hi; exact e12)).elim
    · rcases hE with ⟨x0, x1, _, _⟩ | ⟨x0, x1, x2, x3⟩
      · exact (IH i hi (by omega) (m' + 1) ⟨x0, x1⟩).elim
      · obtain ⟨u, rfl⟩ : ∃ u, i = u + 2 := ⟨i - 2, by omega⟩
        have g0 : f94 (e m' u) (e m' (u + 1)) (e m' (u + 2)) = 1 :=
          (hr m' u (by omega)).symm.trans x0
        have g1 : f94 (e m' (u + 1)) (e m' (u + 2)) (e m' (u + 3)) = 1 :=
          (hr m' (u + 1) (by omega)).symm.trans x1
        have g2 : f94 (e m' (u + 2)) (e m' (u + 3)) (e m' (u + 4)) = 1 :=
          (hr m' (u + 2) (by omega)).symm.trans x2
        have g3 : f94 (e m' (u + 3)) (e m' (u + 4)) (e m' (u + 5)) = 1 :=
          (hr m' (u + 3) (by omega)).symm.trans x3
        rcases (by omega : u = b ∨ u = b + 1 ∨ b + 2 ≤ u) with hu | hu | hu
        · have hl : e m' u = e m' (u + 1) := by
            have := hlow m'; rw [← hu] at this; exact this
          have hd : e m' (u + 2) ≠ e m' (u + 3) := by
            have := hD m'; rw [← hu] at this; exact this
          obtain ⟨a3, a4⟩ := f94_chain_c _ _ _ _ _ _ g0 g1 g2 g3 hl hd
          exact (IH (u + 3) (by omega) (by omega) m' ⟨a3, a4⟩).elim
        · have hd : e m' (u + 1) ≠ e m' (u + 2) := by
            rw [hu]; exact hD m'
          rcases f94_chain_b _ _ _ _ _ _ g0 g1 g2 g3 hd with ⟨a2, a3⟩ | ⟨a3, a4⟩ | ⟨a1, a4, a5⟩
          · exact (IH (u + 2) (by omega) (by omega) m' ⟨a2, a3⟩).elim
          · exact (IH (u + 3) (by omega) (by omega) m' ⟨a3, a4⟩).elim
          · refine ⟨by omega, a4, a5, by rw [hu] at a1; exact a1, ?_⟩
            have hs : e (m' + 1) (b + 3) = 1 := by rw [hu] at x0; exact x0
            rcases hcz (e (m' + 1) (b + 2)) with h | h
            · exact h
            · exact (hD (m' + 1) (h.trans hs.symm)).elim
        · rcases f94_chain_a _ _ _ _ _ _ g0 g1 g2 g3 with ⟨a0, a1⟩ | ⟨a1, a2⟩ | ⟨a2, a3⟩ | ⟨a3, a4⟩
          · exact (IH u (by omega) (by omega) m' ⟨a0, a1⟩).elim
          · exact (IH (u + 1) (by omega) (by omega) m' ⟨a1, a2⟩).elim
          · exact (IH (u + 2) (by omega) (by omega) m' ⟨a2, a3⟩).elim
          · exact (IH (u + 3) (by omega) (by omega) m' ⟨a3, a4⟩).elim
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    intro hj hjW n hn
    obtain ⟨m', hm'⟩ : ∃ m', n + 2 * t = m' + 2 := ⟨n + 2 * t - 2, by omega⟩
    have q0 : e (m' + 2) j = 0 := by rw [← hm', hper2 _ _ (by omega)]; exact hn.1
    have q1 : e (m' + 2) (j + 1) = 0 := by rw [← hm', hper2 _ _ hjW]; exact hn.2
    have IH' : ∀ i, b + 2 ≤ i → i < j → ∀ n, ¬(e n i = 0 ∧ e n (i + 1) = 0) :=
      fun i hi hij n => IH i hij hi (by omega) n
    obtain ⟨hj5, -, -, -, -⟩ := main j hj hjW IH' m' q0 q1
    subst hj5
    have step : ∀ N, e (N + 2) (b + 5) = 0 → e (N + 2) (b + 5 + 1) = 0 →
        e N (b + 5) = 0 ∧ e N (b + 5 + 1) = 0 ∧ e N (b + 2) = 0 ∧ e (N + 1) (b + 2) = 0 := by
      intro N h0 h1
      obtain ⟨-, a1, a2, a3, a4⟩ := main (b + 5) hj hjW IH' N h0 h1
      exact ⟨a1, a2, a3, a4⟩
    have R : ∀ N, e N (b + 5) = 0 → e N (b + 5 + 1) = 0 → ∀ x, 1 ≤ x → x < N →
        e x (b + 2) = 0 := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ihN =>
        intro h0 h1 x hx1 hxN
        obtain ⟨n', rfl⟩ : ∃ n', N = n' + 2 := ⟨N - 2, by omega⟩
        obtain ⟨s0, s1, c0, c1⟩ := step n' h0 h1
        rcases (by omega : x = n' ∨ x = n' + 1 ∨ x < n') with hx | hx | hlt
        · rw [hx]; exact c0
        · rw [hx]; exact c1
        · exact ihN n' (by omega) s0 s1 x hx1 hlt
    have hQ : ∀ s, e (m' + 2 + s * t) (b + 5) = 0 ∧ e (m' + 2 + s * t) (b + 5 + 1) = 0 :=
      fun s => ⟨(hperk s (m' + 2) (b + 5) (by omega)).trans q0,
        (hperk s (m' + 2) (b + 5 + 1) hjW).trans q1⟩
    apply hnc
    intro x
    have hN : x + t + 1 ≤ (x + t + 1) * t := Nat.le_mul_of_pos_right _ ht
    rw [← hper x (b + 2) (by omega)]
    exact R (m' + 2 + (x + t + 1) * t) (hQ _).1 (hQ _).2 (x + t) (by omega) (by omega)

/-- **A family of purely periodic columns at rule `94` has its cells paired.** A column induction
on the pair index: the first two columns are set at every time, and an unequal pair `K` over equal
lower pairs would be unequal at every time, with its column not clear at every time, which leaves
no two adjacent clear cells from the pair on, against the two clear cells at the end of the
window. -/
theorem periodicColumnsPaired94 : PeriodicColumnsPaired94 := by
  intro e W d t hrec he0 hdW hclear ht hper k hkW
  have hW : 0 < W := by omega
  have hr : ∀ n j, j + 2 < W → e (n + 1) (j + 2) = f94 (e n j) (e n (j + 1)) (e n (j + 2)) := by
    intro n j hj
    have := hrec n (j + 2) hj
    simpa using this
  have hperk : ∀ s n j, j < W → e (n + s * t) j = e n j := by
    intro s
    induction s with
    | zero => intro n j _; simp
    | succ s ih =>
      intro n j hj
      rw [Nat.succ_mul, ← add_assoc, hper _ _ hj, ih n j hj]
  have hA0 : ∀ n, e n 0 = 1 := by
    intro n
    induction n with
    | zero => exact he0
    | succ n ih =>
      have := hrec n 0 hW
      simp only [nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, ↓reduceIte, one_ne_zero, ih] at this
      rw [this]; decide
  have hA1 : 1 < W → ∀ n, e n 1 = 1 := by
    intro h1 n
    have step : ∀ m, e (m + 1) 1 = 1 := by
      intro m
      have := hrec m 1 h1
      simp only [Nat.not_ofNat_le_one, ↓reduceIte, Std.le_refl, tsub_self, hA0 m] at this
      rw [this]
      generalize e m 1 = x
      revert x; decide
    rw [← hper n 1 h1]
    obtain ⟨m, hm⟩ : ∃ m, n + t = m + 1 := ⟨n + t - 1, by omega⟩
    rw [hm]; exact step m
  have hP : ∀ K, 2 * K + 1 < W → ∀ n, e n (2 * K) = e n (2 * K + 1) := by
    intro K
    induction K using Nat.strong_induction_on with
    | _ K IH =>
      intro hKW
      rcases Nat.eq_zero_or_pos K with rfl | hKpos
      · intro n
        simp only [Nat.mul_zero, Nat.zero_add]
        rw [hA0 n, hA1 (by omega) n]
      · by_contra hne
        push Not at hne
        obtain ⟨n0, hn0⟩ := hne
        obtain ⟨b, hb⟩ : ∃ b, b + 2 = 2 * K := ⟨2 * K - 2, by omega⟩
        have hlow : ∀ n, e n b = e n (b + 1) := by
          intro n
          have := IH (K - 1) (by omega) (by omega) n
          rwa [show 2 * (K - 1) = b by omega] at this
        have hprop : ∀ n, e n (b + 2) = e n (b + 3) → ∀ m, n ≤ m →
            e m (b + 2) = e m (b + 3) := by
          intro n hn m hm
          induction m, hm using Nat.le_induction with
          | base => exact hn
          | succ m hm ih =>
            have r1 := hr m b (by omega)
            have r2 := hr m (b + 1) (by omega)
            have ih' : e m (b + 2) = e m (b + 1 + 2) := ih
            change e (m + 1) (b + 2) = e (m + 1) (b + 1 + 2)
            rw [r1, r2, ← hlow m, ← ih']
            exact f94_aac _ _
        have hDall : ∀ n, e n (b + 2) ≠ e n (b + 3) := by
          intro n hne
          have hn0' : e n0 (b + 2) ≠ e n0 (b + 3) := by
            rw [← hb] at hn0; exact hn0
          have hle : n ≤ n * t := Nat.le_mul_of_pos_right _ ht
          have h1 := hprop n hne (n0 + n * t) (by omega)
          rw [hperk n n0 (b + 2) (by omega), hperk n n0 (b + 3) (by omega)] at h1
          exact hn0' h1
        have hnc : ¬ ∀ n, e n (b + 2) = 0 := by
          intro hall
          have Z : ∀ q, q ≤ K → (∀ n, e n (2 * q) = 0) → False := by
            intro q
            induction q with
            | zero =>
              intro _ h
              have := h 0
              rw [Nat.mul_zero, he0] at this
              exact absurd this (by decide)
            | succ q ih =>
              intro hq h
              apply ih (by omega)
              intro m
              have hpair := IH q (by omega) (by omega) m
              have r := hr m (2 * q) (by omega)
              have h1 : e (m + 1) (2 * q + 2) = 0 := by
                have := h (m + 1)
                rwa [show 2 * (q + 1) = 2 * q + 2 by ring] at this
              have h2 : e m (2 * q + 2) = 0 := by
                have := h m
                rwa [show 2 * (q + 1) = 2 * q + 2 by ring] at this
              rw [r, ← hpair, h2, f94_aa0] at h1
              exact h1
          exact Z K le_rfl (fun n => by rw [← hb]; exact hall n)
        have hc := pairClaim94 e W t b hr ht hper hlow hDall hnc (W - 2) (by omega)
          (by omega) 0
        apply hc
        refine ⟨hclear (W - 2) (by omega) (by omega), ?_⟩
        rw [show W - 2 + 1 = W - 1 by omega]
        exact hclear (W - 1) (by omega) (by omega)
  exact hP k hkW 0

/-- **The hypotheses of the paired-cells statement meet**: at width `4`, `d = 2`, `t = 2`, the
family that is `1` in columns `0` and `1` and alternates `0`, `1` in columns `2` and `3` (the
windows `1100` and `1111`) obeys the window recurrence of rule `94`, with its first cell set, its
cells from `2` clear at time `0` and every column of period `2`. -/
theorem periodicColumnsPaired94_nonvacuous (e : ℕ → ℕ → ZMod 2)
    (he : ∀ n j, e n j = if j < 2 then 1 else if n % 2 = 0 then 0 else 1) :
    (∀ n j, j < 4 → e (n + 1) j =
      f94 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) ∧
    e 0 0 = 1 ∧ 2 + 2 ≤ 4 ∧ (∀ j, 2 ≤ j → j < 4 → e 0 j = 0) ∧ 0 < 2 ∧
    (∀ n j, j < 4 → e (n + 2) j = e n j) := by
  refine ⟨?_, by simp [he], by decide, ?_, by decide, ?_⟩
  · intro n j hj
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
    · have h' : (n + 1) % 2 = 0 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
  · intro j h1 h2
    interval_cases j <;> simp [he]
  · intro n j hj
    have h' : (n + 2) % 2 = n % 2 := by omega
    simp only [he, h']

/-- **The second clear cell is needed**: at width `4`, `d = 3`, `t = 2`, the family that is `1` in
columns `0` and `1`, alternates `1`, `0` in column `2` and `0`, `1` in column `3` (the windows
`1110` and `1101`) obeys the window recurrence of rule `94`, with its first cell set, only its
cell `3` clear at time `0` and every column of period `2`, yet its cells `2` and `3` are unequal
at time `0`. -/
theorem not_periodicColumnsPaired94_one_clear (e : ℕ → ℕ → ZMod 2)
    (he : ∀ n j, e n j = if j < 2 then 1 else if j = 2 then (if n % 2 = 0 then 1 else 0)
      else (if n % 2 = 0 then 0 else 1)) :
    (∀ n j, j < 4 → e (n + 1) j =
      f94 (if 2 ≤ j then e n (j - 2) else 0) (if 1 ≤ j then e n (j - 1) else 0) (e n j)) ∧
    e 0 0 = 1 ∧ 3 < 4 ∧ (∀ j, 3 ≤ j → j < 4 → e 0 j = 0) ∧ 0 < 2 ∧
    (∀ n j, j < 4 → e (n + 2) j = e n j) ∧ e 0 2 ≠ e 0 3 := by
  refine ⟨?_, by simp [he], by decide, ?_, by decide, ?_, ?_⟩
  · intro n j hj
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
    · have h' : (n + 1) % 2 = 0 := by omega
      interval_cases j <;> (simp only [he, h, h']; decide)
  · intro j h1 h2
    interval_cases j
    simp [he]
  · intro n j hj
    have h' : (n + 2) % 2 = n % 2 := by omega
    simp only [he, h']
  · simp [he]

/-- Every set cell of a nonzero state sits at the leftmost set cell plus an offset below the
diameter. -/
private theorem exists_offset_of_ne {p : FiniteConfiguration} (hp : p ≠ 0) {i : ℤ} (hi : p i ≠ 0) :
    ∃ a : ℕ, a < p.diam ∧ i = p.leftEnd + a := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  have hmem : i ∈ p.support := Finsupp.mem_support_iff.mpr hi
  have h1 : p.support.min' hne ≤ i := Finset.min'_le _ _ hmem
  have h2 : i ≤ p.support.max' hne := Finset.le_max' _ _ hmem
  rw [FiniteConfiguration.leftEnd_eq hne]
  rw [FiniteConfiguration.diam_eq' hne]
  refine ⟨(i - p.support.min' hne).toNat, by omega, by omega⟩

/-- The value of a translate at a cell. -/
private theorem translate_apply_sub (i : ℤ) (p : FiniteConfiguration) (x : ℤ) :
    translate i p x = p (x - i) := by
  have h := Finsupp.mapDomain_apply_of_injective (add_left_injective i) p (x - i)
  rw [sub_add_cancel] at h
  exact h

/-- **Rule `94` reproduces exactly the nonzero translates of doubled patterns**, from the statement
that purely periodic window columns have their cells paired as a hypothesis: the pattern's window of
width `diam p + 2` is such a family along the orbit, so its cells come in equal pairs. -/
theorem reproduces_iff_dbl_f94_of (h : PeriodicColumnsPaired94) (p : FiniteConfiguration) :
    Reproduces (finRule f94 hq94) p ↔ p ≠ 0 ∧ ∃ x c, p = translate c (dbl x) := by
  constructor
  · intro hrep
    have hp : p ≠ 0 := hrep.1
    have h001 : f94 0 0 1 = 1 := by decide
    obtain ⟨t, ht, htp⟩ := leftWindowPeriodic f94 hq94 h001 p hrep 2
    have key := h (fun n j => ((finRule f94 hq94)^[n] p).leftWindow (p.diam + 2) j)
      (p.diam + 2) p.diam t
      (by
        intro n j hj
        rw [Function.iterate_succ_apply']
        exact FiniteConfiguration.leftWindow_finRule h001 (iterate_ne_zero hq94 h001 hp n) hj)
      (leftWindow_zero_ne hp (by omega)) (by omega)
      (by
        intro j hj1 hj2
        exact FiniteConfiguration.leftWindow_eq_zero_of_diam_le hp hj1 hj2)
      ht (fun n j _ => congrFun (htp n) j)
    have hpair : ∀ k : ℕ, 2 * k + 1 < p.diam + 2 →
        p (p.leftEnd + ((2 * k : ℕ) : ℤ)) = p (p.leftEnd + ((2 * k + 1 : ℕ) : ℤ)) := by
      intro k hk
      have := key k hk
      simp only [FiniteConfiguration.leftWindow, show 2 * k < p.diam + 2 by omega, hk, ite_true,
        Function.iterate_zero, id] at this
      exact this
    have hzero : ∀ b : ℕ, p.diam ≤ b → p (p.leftEnd + (b : ℤ)) = 0 := by
      intro b hb
      by_contra hne
      obtain ⟨a, ha, hab⟩ := exists_offset_of_ne hp hne
      have : a = b := by omega
      omega
    let g : ℤ → ℤ := fun i => p.leftEnd + 2 * i
    have hginj : Set.InjOn g (g ⁻¹' (p.support : Set ℤ)) := by
      intro a _ b _ hab
      simp only [g] at hab
      omega
    let x : FiniteConfiguration := Finsupp.comapDomain g p hginj
    have hx : ∀ i, x i = p (p.leftEnd + 2 * i) := fun i => rfl
    refine ⟨hp, x, p.leftEnd, ?_⟩
    ext j
    rw [translate_apply_sub, dbl_apply, hx]
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
      · by_cases hlt : a < p.diam + 2
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
    exact Reproduces.translate f94 hq94
      (LocalRule.DoubledAgree.reproduces_dbl f94 hq94 doubledAgree_f94 hx) c

/-- **Rule `94` reproduces exactly the nonzero translates of doubled patterns.** -/
theorem reproduces_iff_dbl_f94 (p : FiniteConfiguration) :
    Reproduces (finRule f94 hq94) p ↔ p ≠ 0 ∧ ∃ x c, p = translate c (dbl x) :=
  reproduces_iff_dbl_f94_of periodicColumnsPaired94 p

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_dbl_f94_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_dbl_f94_of

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsPaired94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsPaired94

set_option linter.style.longLine false in
/-- info: 'ECA.periodicColumnsPaired94_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.periodicColumnsPaired94_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ECA.not_periodicColumnsPaired94_one_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.not_periodicColumnsPaired94_one_clear

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_dbl_f94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_dbl_f94
