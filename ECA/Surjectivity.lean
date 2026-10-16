module

public import ECA.SurjectivityCert
public import ECA.WolframSymmetries
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs

/-!
# The elementary rules that are not surjective and not injective on the configurations of the line

A word with no preimage is a certificate that a radius-one rule is not surjective on the
configurations `ℤ → ZMod 2`, and two distinct words of one length whose spatially periodic
configurations have one image are a certificate that it is not injective. Both are checked by the
kernel over the data of `SurjectivityCert`.

## Main results

* `LocalRule.hasNoPreimage` and `not_surjective_of_hasNoPreimage` — the check on the set of pairs of
  last two cells of a preimage of the prefix read so far, its soundness at every rule, word,
  configuration and start cell (`LocalRule.hasNoPreimage_sound`), and the corollary that the rule is
  not surjective.
* `orphans_pass`, `orphans_length_le`, `mem_orphans_iff` — every entry of `orphans` passes the
  check at its rule, every word has length at most `9`, and the rule numbers of `orphans` are
  exactly those outside the numbers permutive at an end and `51`, `204` (`226` of them).
* `not_surjective_lineRule_ofWolfram` — those `226` rules are not surjective on the line.
* `LocalRule.isCollision` and `not_injective_of_collision` — the check on two words, and its
  soundness: the two periodic configurations are distinct and have the same image.
* `collisions_pass`, `collisions_length_le`, `mem_collisions_iff` — every entry of `collisions`
  passes the check at its rule, every word has length at most `4`, and the rule numbers are exactly
  those outside `{15, 51, 85, 170, 204, 240}` (`250` of them).
* `injective_lineRule_ofWolfram_iff` and `bijective_lineRule_ofWolfram_iff` — with the six
  bijections of `WolframSymmetries.lean`, a rule is injective, and a rule is bijective, on the line
  exactly when its number is one of `15`, `51`, `85`, `170`, `204`, `240`.

## Scope

Nothing here says that the thirty remaining rules are surjective beyond the six bijections, that
`9` is the least bound on the length of a word with no preimage, or anything about rules of wider
radius.
-/

@[expose] public section

namespace ECA

open LocalRule

/-! ## Not surjective -/

/-- One step of the set of pairs: after reading the output letter `o`, the pairs `(b, c)` for which
some `(a, b)` of the set has `f a b c = o`. -/
def LocalRule.pairStep (f : LocalRule) (o : ZMod 2) (S : List (ZMod 2 × ZMod 2)) :
    List (ZMod 2 × ZMod 2) :=
  (S.flatMap fun p => [0, 1].filterMap fun c => if f p.1 p.2 c = o then some (p.2, c) else none)
    |>.eraseDups

/-- The set of pairs after reading a word letter by letter. -/
def LocalRule.pairRun (f : LocalRule) :
    List (ZMod 2 × ZMod 2) → List (ZMod 2) → List (ZMod 2 × ZMod 2)
  | S, [] => S
  | S, o :: w => pairRun f (pairStep f o S) w

/-- **The check for a word with no preimage**: start from the four pairs of cells, replace the set
of pairs by `LocalRule.pairStep` for each letter of the word in order, and require that the set ends
empty. A pair is the last two cells of a preimage of the prefix read so far. -/
def LocalRule.hasNoPreimage (f : LocalRule) (w : List (ZMod 2)) : Bool :=
  (pairRun f [(0, 0), (0, 1), (1, 0), (1, 1)] w).isEmpty

private theorem LocalRule.pairRun_nonempty (f : LocalRule) (x : Configuration) :
    ∀ (w : List (ZMod 2)) (S : List (ZMod 2 × ZMod 2)) (i : ℤ),
      (x (i - 1), x i) ∈ S →
      (∀ (j : ℕ) (hj : j < w.length), lineRule f x (i + j) = w[j]) →
      (pairRun f S w).isEmpty = false := by
  intro w
  induction w with
  | nil =>
    intro S i hS _
    cases S with
    | nil => exact absurd hS (by simp)
    | cons _ _ => rfl
  | cons o w ih =>
    intro S i hS hw
    have h0 : f (x (i - 1)) (x i) (x (i + 1)) = o := by
      have := hw 0 (by simp)
      simpa [lineRule] using this
    refine ih (pairStep f o S) (i + 1) ?_ ?_
    · simp only [pairStep, List.mem_eraseDups, List.mem_flatMap, List.mem_filterMap,
        List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨(x (i - 1), x i), hS, x (i + 1), ?_, ?_⟩
      · generalize x (i + 1) = c
        revert c
        decide
      · simp [h0]
    · intro j hj
      have := hw (j + 1) (by simpa using hj)
      rw [show i + 1 + (j : ℤ) = i + ((j + 1 : ℕ) : ℤ) by push_cast; ring]
      simpa using this

/-- **Soundness of the check for a word with no preimage**, at every rule, word, configuration and
start cell: if `LocalRule.hasNoPreimage f w = true`, the configuration `x` does not have `f` values
`w` at the cells from `i₀` on. -/
theorem LocalRule.hasNoPreimage_sound (f : LocalRule) (w : List (ZMod 2))
    (h : hasNoPreimage f w = true) (x : Configuration) (i₀ : ℤ) :
    ¬ ∀ (j : ℕ) (hj : j < w.length), lineRule f x (i₀ + j) = w[j] := by
  intro hw
  have hS : (x (i₀ - 1), x i₀) ∈ [((0 : ZMod 2), (0 : ZMod 2)), (0, 1), (1, 0), (1, 1)] := by
    generalize x (i₀ - 1) = a
    generalize x i₀ = b
    revert a b
    decide
  have := pairRun_nonempty f x w _ i₀ hS hw
  unfold hasNoPreimage at h
  rw [h] at this
  exact Bool.noConfusion this

/-- **A word with no preimage makes the rule not surjective on the line**: the configuration that
reads `w` from cell `0` and `0` elsewhere has no preimage. -/
theorem not_surjective_of_hasNoPreimage (f : LocalRule)
    (w : List (ZMod 2)) (h : hasNoPreimage f w = true) : ¬ Function.Surjective (lineRule f) := by
  intro hs
  obtain ⟨y, hy⟩ := hs (fun i => if 0 ≤ i then w.getD i.toNat 0 else 0)
  refine hasNoPreimage_sound f w h y 0 fun j hj => ?_
  have := congrFun hy ((0 : ℤ) + j)
  rw [this]
  simp [List.getElem?_eq_getElem hj]

/-! ### The data -/

/-- A word of bits read as a word over `ZMod 2`. -/
def toWord (w : List Nat) : List (ZMod 2) := w.map fun b => (b : ZMod 2)

/-- The Boolean check of one entry of `orphans`. -/
def orphanOk (e : Nat × List Nat) : Bool :=
  decide (e.1 < 256) && hasNoPreimage (LocalRule.ofWolfram (Fin.ofNat 256 e.1)) (toWord e.2)

/-- The kernel decision that every entry of `orphans` passes `orphanOk`. -/
theorem orphans_all : orphans.all orphanOk = true := by decide +kernel

/-- **Every entry of `orphans` passes the check at its rule.** -/
theorem orphans_pass : ∀ e ∈ orphans, ∃ h : e.1 < 256,
    hasNoPreimage (LocalRule.ofWolfram ⟨e.1, h⟩) (toWord e.2) = true := by
  intro e he
  have := List.all_eq_true.mp orphans_all e he
  simp only [orphanOk, Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨this.1, ?_⟩
  have h2 := this.2
  rwa [show Fin.ofNat 256 e.1 = ⟨e.1, this.1⟩ from Fin.ext (Nat.mod_eq_of_lt this.1)] at h2

/-- **Every word of `orphans` has length at most `9`.** -/
theorem orphans_length_le : ∀ e ∈ orphans, e.2.length ≤ 9 := by decide +kernel

/-- **The rule numbers of `orphans` are exactly the numbers outside the permutive ones and
`51`, `204`.** -/
theorem mem_orphans_iff (n : Fin 256) :
    (∃ e ∈ orphans, e.1 = (n : Nat)) ↔
      ¬ (LeftPermutive (LocalRule.ofWolfram n) ∨ RightPermutive (LocalRule.ofWolfram n) ∨ n = 51 ∨ n
        = 204) := by
  revert n
  decide +kernel

/-- **There are `226` such numbers, one entry each.** -/
theorem orphans_length : orphans.length = 226 := by decide +kernel

/-- No rule number occurs twice in `orphans`. -/
theorem orphans_nodup : (orphans.map Prod.fst).Nodup := by decide +kernel

/-- **Rules not surjective on the line**: every rule that is not permutive at an end and is not
`51` or `204` is not surjective on the configurations of the line. -/
theorem not_surjective_lineRule_ofWolfram (n : Fin 256)
    (h : ¬ (LeftPermutive (LocalRule.ofWolfram n) ∨ RightPermutive (LocalRule.ofWolfram n) ∨ n = 51
      ∨ n = 204)) :
    ¬ Function.Surjective (lineRule (LocalRule.ofWolfram n)) := by
  obtain ⟨e, he, hen⟩ := (mem_orphans_iff n).mpr h
  obtain ⟨hlt, hpass⟩ := orphans_pass e he
  have : (⟨e.1, hlt⟩ : Fin 256) = n := Fin.ext hen
  rw [this] at hpass
  exact not_surjective_of_hasNoPreimage _ _ hpass

/-! ## Not injective -/

/-- The value of `f` at the cyclic neighbourhood of position `r` in a word of length `p`. -/
def LocalRule.cyclicValue (f : LocalRule) (u : List (ZMod 2)) (r : Nat) : ZMod 2 :=
  f (u.getD ((r + u.length - 1) % u.length) 0) (u.getD r 0) (u.getD ((r + 1) % u.length) 0)

/-- **The check for a collision**: the words have one positive length, are distinct, and at every
position the value of `f` at the cyclic neighbourhood in `u` equals the value at the cyclic
neighbourhood in `v`. -/
def LocalRule.isCollision (f : LocalRule) (u v : List (ZMod 2)) : Bool :=
  decide (u.length = v.length) && decide (0 < u.length) && decide (u ≠ v) &&
    (List.range u.length).all fun r => decide (cyclicValue f u r = cyclicValue f v r)

/-- The configuration repeating a word of positive length with period its length. -/
def periodic (u : List (ZMod 2)) (i : ℤ) : ZMod 2 := u.getD (i % (u.length : ℤ)).toNat 0

private theorem emod_pred (p : Nat) (hp : 0 < p) (i : ℤ) :
    ((i - 1) % (p : ℤ)).toNat = ((i % p).toNat + p - 1) % p := by
  have h0 : 0 ≤ i % (p : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : i % (p : ℤ) < p := Int.emod_lt_of_pos _ (by omega)
  have hi : i - 1 = (i % p - 1) + p * (i / p) := by
    have := Int.emod_add_mul_ediv i p
    omega
  rw [hi, Int.add_mul_emod_self_left]
  generalize i % (p : ℤ) = r at *
  obtain ⟨k, rfl⟩ : ∃ k : Nat, r = k := ⟨r.toNat, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : ((0 : Nat) : ℤ) - 1 = (p - 1 : Nat) + p * (-1) := by
      push_cast [Nat.cast_sub hp]; ring
    rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    simp only [Int.toNat_natCast, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    have : (k + p - 1) % p = k - 1 := by
      rw [show k + p - 1 = (k - 1) + p by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [Int.toNat_natCast]
    omega

private theorem emod_succ (p : Nat) (hp : 0 < p) (i : ℤ) :
    ((i + 1) % (p : ℤ)).toNat = ((i % p).toNat + 1) % p := by
  have h0 : 0 ≤ i % (p : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : i % (p : ℤ) < p := Int.emod_lt_of_pos _ (by omega)
  have hi : i + 1 = (i % p + 1) + p * (i / p) := by
    have := Int.emod_add_mul_ediv i p
    omega
  rw [hi, Int.add_mul_emod_self_left]
  generalize i % (p : ℤ) = r at *
  obtain ⟨k, rfl⟩ : ∃ k : Nat, r = k := ⟨r.toNat, by omega⟩
  simp only [Int.toNat_natCast]
  rcases Nat.lt_or_ge (k + 1) p with h | h
  · rw [Int.emod_eq_of_lt (by omega) (by omega), Nat.mod_eq_of_lt h]; omega
  · have : k + 1 = p := by omega
    subst this
    simp

private theorem LocalRule.lineRule_periodic (f : LocalRule) (u : List (ZMod 2))
    (hp : 0 < u.length) (i : ℤ) :
    lineRule f (periodic u) i = cyclicValue f u (i % (u.length : ℤ)).toNat := by
  simp only [lineRule, periodic, cyclicValue, emod_pred _ hp, emod_succ _ hp]

/-- **Soundness of the check for a collision**: if it passes, `LocalRule.lineRule f` is not
injective — the two configurations repeating `u` and `v` are distinct and have the same image. -/
theorem not_injective_of_collision (f : LocalRule) (u v : List (ZMod 2))
    (h : isCollision f u v = true) : ¬ Function.Injective (lineRule f) := by
  simp only [isCollision, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨hlen, hpos⟩, hne⟩, hall⟩ := h
  intro hinj
  apply hne
  have hpos' : 0 < v.length := hlen ▸ hpos
  have heq : lineRule f (periodic u) = lineRule f (periodic v) := by
    funext i
    rw [lineRule_periodic f u hpos, lineRule_periodic f v hpos', ← hlen]
    exact hall _ (by
      have := Int.emod_lt_of_pos i (show (0 : ℤ) < u.length by exact_mod_cast hpos)
      have h0 := Int.emod_nonneg i (show (u.length : ℤ) ≠ 0 by exact_mod_cast hpos.ne')
      omega)
  have hp := congrFun (hinj heq)
  refine List.ext_getElem hlen fun r hr hr' => ?_
  have := hp (r : ℤ)
  simp only [periodic, ← hlen] at this
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hr)] at this
  simpa [Int.toNat_natCast, List.getElem?_eq_getElem hr, List.getElem?_eq_getElem hr'] using this

/-! ### The data -/

/-- The Boolean check of one entry of `collisions`. -/
def collisionOk (e : Nat × List Nat × List Nat) : Bool :=
  decide (e.1 < 256) && isCollision (LocalRule.ofWolfram (Fin.ofNat 256 e.1)) (toWord e.2.1) (toWord
    e.2.2)

/-- The kernel decision that every entry of `collisions` passes `collisionOk`. -/
theorem collisions_all : collisions.all collisionOk = true := by decide +kernel

/-- **Every entry of `collisions` passes the check at its rule.** -/
theorem collisions_pass : ∀ e ∈ collisions, ∃ h : e.1 < 256,
    isCollision (LocalRule.ofWolfram ⟨e.1, h⟩) (toWord e.2.1) (toWord e.2.2) = true := by
  intro e he
  have := List.all_eq_true.mp collisions_all e he
  simp only [collisionOk, Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨this.1, ?_⟩
  have h2 := this.2
  rwa [show Fin.ofNat 256 e.1 = ⟨e.1, this.1⟩ from Fin.ext (Nat.mod_eq_of_lt this.1)] at h2

/-- **Every word of `collisions` has length at most `4`.** -/
theorem collisions_length_le :
    ∀ e ∈ collisions, e.2.1.length ≤ 4 ∧ e.2.2.length ≤ 4 := by decide +kernel

/-- **The rule numbers of `collisions` are exactly the numbers outside
`{15, 51, 85, 170, 204, 240}`.** -/
theorem mem_collisions_iff (n : Fin 256) :
    (∃ e ∈ collisions, e.1 = (n : Nat)) ↔
      n ∉ ({15, 51, 85, 170, 204, 240} : Finset (Fin 256)) := by
  revert n
  decide +kernel

/-- **There are `250` such numbers, one entry each.** -/
theorem collisions_length : collisions.length = 250 := by decide +kernel

/-- No rule number occurs twice in `collisions`. -/
theorem collisions_nodup : (collisions.map Prod.fst).Nodup := by decide +kernel

/-- **A rule outside the six is not injective on the line.** -/
theorem not_injective_lineRule_ofWolfram (n : Fin 256)
    (h : n ∉ ({15, 51, 85, 170, 204, 240} : Finset (Fin 256))) :
    ¬ Function.Injective (lineRule (LocalRule.ofWolfram n)) := by
  obtain ⟨e, he, hen⟩ := (mem_collisions_iff n).mpr h
  obtain ⟨hlt, hpass⟩ := collisions_pass e he
  have : (⟨e.1, hlt⟩ : Fin 256) = n := Fin.ext hen
  rw [this] at hpass
  exact not_injective_of_collision _ _ _ hpass

/-- **Injective on the line exactly at the six bijections.** -/
theorem injective_lineRule_ofWolfram_iff (n : Fin 256) :
    Function.Injective (lineRule (LocalRule.ofWolfram n)) ↔
      n ∈ ({15, 51, 85, 170, 204, 240} : Finset (Fin 256)) := by
  refine ⟨fun h => by_contra fun hn => not_injective_lineRule_ofWolfram n hn h, fun h => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact bijective_lineRule_ofWolfram_15.1
  · exact bijective_lineRule_ofWolfram_51.1
  · exact bijective_lineRule_ofWolfram_85.1
  · exact bijective_lineRule_ofWolfram_170.1
  · exact bijective_lineRule_ofWolfram_204.1
  · exact bijective_lineRule_ofWolfram_240.1

/-- **Bijective on the line exactly at the six bijections.** -/
theorem bijective_lineRule_ofWolfram_iff (n : Fin 256) :
    Function.Bijective (lineRule (LocalRule.ofWolfram n)) ↔
      n ∈ ({15, 51, 85, 170, 204, 240} : Finset (Fin 256)) := by
  refine ⟨fun h => (injective_lineRule_ofWolfram_iff n).mp h.1, fun h => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact bijective_lineRule_ofWolfram_15
  · exact bijective_lineRule_ofWolfram_51
  · exact bijective_lineRule_ofWolfram_85
  · exact bijective_lineRule_ofWolfram_170
  · exact bijective_lineRule_ofWolfram_204
  · exact bijective_lineRule_ofWolfram_240

end ECA
