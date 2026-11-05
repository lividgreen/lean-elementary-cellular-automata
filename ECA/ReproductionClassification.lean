module

public import ECA.WolframNumber
public import ECA.BoundedGaps
public import ECA.EdgeWindow
public import ECA.EdgeColumns
public import ECA.Rule110Bound
public import ECA.Rule106

/-!
# Which quiescent radius-one rules reproduce a pattern
([RuleSpace] §5)

A quiescent radius-one rule is `LocalRule.ofWolfram n` at a Wolfram number `n < 256` with
`LocalRule.ofWolfram n 0 0 0 = 0`. Such a rule reproduces some pattern without bound exactly when
its number is one of seventeen. Outside the fifty-four growing numbers every orbit has bounded
diameter, which forbids reproduction; of the fifty-four, seventeen reproduce a pattern and the
other thirty-seven are covered by the non-reproduction theorems for the numbers of `gapClassA`,
`gapClassB`, `gapClassC` and `gapClassD`, and for `54`, `30`, `86`, `110` and `124`.

## Main results

* `reproducingNumbers` — the seventeen numbers.
* `reproduces_iff_mem` — **the classification**: a quiescent radius-one rule reproduces some
  pattern exactly when its Wolfram number is in `reproducingNumbers`.
* `reproducing_card` — exactly seventeen quiescent numbers are in the list.
* `reproducingNumbers_quiescent_growing` — every number of the list is quiescent and growing.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- **The seventeen reproducing numbers**: the Wolfram numbers of the quiescent radius-one rules
that reproduce a pattern. -/
def reproducingNumbers : List ℕ :=
  [18, 22, 26, 60, 82, 90, 94, 102, 106, 120, 122, 126, 146, 150, 154, 210, 218]

/-- The thirty-seven growing numbers covered by the non-reproduction theorems. -/
private def nonReproducingNumbers : List ℕ :=
  gapClassA ++ gapClassB ++ gapClassC ++ gapClassD ++ [54, 30, 86, 110, 124]

/-- The fifty-four growing quiescent numbers are the seventeen and the thirty-seven, with no
number in both and none left over. -/
private theorem growing_partition :
    (∀ n : Fin 256, Quiescent (LocalRule.ofWolfram n) → Growing n →
      (n : ℕ) ∈ reproducingNumbers ∨ (n : ℕ) ∈ nonReproducingNumbers) ∧
    (∀ n : Fin 256, ((n : ℕ) ∈ reproducingNumbers ∨ (n : ℕ) ∈ nonReproducingNumbers) →
      Quiescent (LocalRule.ofWolfram n) ∧ Growing n) ∧
    (∀ n : Fin 256, (n : ℕ) ∈ reproducingNumbers → (n : ℕ) ∉ nonReproducingNumbers) ∧
    reproducingNumbers.length = 17 ∧ nonReproducingNumbers.length = 37 ∧
    nonReproducingNumbers.Nodup := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Every number of the list is quiescent and growing. -/
theorem reproducingNumbers_quiescent_growing :
    ∀ n : Fin 256, (n : ℕ) ∈ reproducingNumbers →
      Quiescent (LocalRule.ofWolfram n) ∧ Growing n :=
  fun n h => growing_partition.2.1 n (Or.inl h)

/-- Exactly seventeen quiescent Wolfram numbers are in `reproducingNumbers`. -/
theorem reproducing_card :
    (Finset.univ.filter fun n : Fin 256 =>
      Quiescent (LocalRule.ofWolfram n) ∧ (n : ℕ) ∈ reproducingNumbers).card = 17 := by
  decide +kernel

private theorem finRule_congr {f g : LocalRule} (h : f = g) (hf : f 0 0 0 = 0) (hg : g 0 0 0 = 0) :
    finRule f hf = finRule g hg := by
  subst h
  rfl

private theorem ofWolfram_mem_fifteen : ∀ n : Fin 256, (n : ℕ) ∈ reproducingNumbers →
    (n : ℕ) ≠ 106 → (n : ℕ) ≠ 120 → LocalRule.ofWolfram n ∈ fifteen := by
  decide +kernel

private theorem not_reproduces_of_mem_nonReproducingNumbers (m : ℕ)
    (hm : m ∈ nonReproducingNumbers) (hq : wolframRule m 0 0 0 = 0) (p : FiniteConfiguration) :
    ¬ Reproduces (finRule (wolframRule m) hq) p := by
  simp only [nonReproducingNumbers, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with ((((hA | hB) | hC) | hD) | rfl | rfl | rfl | rfl | rfl)
  · exact not_reproduces_gapClasses m (List.mem_append_left _ hA) hq p
  · exact not_reproduces_gapClasses m (List.mem_append_right _ hB) hq p
  · exact not_reproduces_gapClassC m hC hq p
  · exact not_reproduces_gapClassD m hD hq p
  · exact not_reproduces_wolfram54 hq p
  · exact not_reproduces_wolfram30 hq p
  · exact not_reproduces_wolfram86 hq p
  · exact not_reproduces_wolfram110 hq p
  · exact not_reproduces_wolfram124 hq p

private theorem reproduces_of_eq_106_or_120 (m : ℕ) (hm : m = 106 ∨ m = 120)
    (hq : wolframRule m 0 0 0 = 0) : ∃ p, Reproduces (finRule (wolframRule m) hq) p := by
  rcases hm with rfl | rfl
  · exact ⟨_, reproduces_wolfram106 hq⟩
  · exact ⟨_, reproduces_wolfram120 hq⟩

/-- **The classification.** A quiescent radius-one rule reproduces some pattern without bound
exactly when its Wolfram number is one of the seventeen in `reproducingNumbers`. -/
theorem reproduces_iff_mem (n : Fin 256) (hq : LocalRule.ofWolfram n 0 0 0 = 0) :
    (∃ p, Reproduces (finRule (LocalRule.ofWolfram n) hq) p) ↔ (n : ℕ) ∈ reproducingNumbers := by
  have hw : LocalRule.ofWolfram n = wolframRule n := LocalRule.ofWolfram_eq_wolframRule n
  have hq' : wolframRule n 0 0 0 = 0 := hw ▸ hq
  have hc := finRule_congr hw hq hq'
  constructor
  · rintro ⟨p, hp⟩
    by_contra hn
    by_cases hg : Growing n
    · have hs := growing_partition.1 n hq hg
      have hnr : (n : ℕ) ∈ nonReproducingNumbers := hs.resolve_left hn
      rw [hc] at hp
      exact not_reproduces_of_mem_nonReproducingNumbers _ hnr hq' p hp
    · exact not_reproduces_of_diamBounded _
        (diamBounded_of_not_growing (LocalRule.ofWolfram n) hq hg) p hp
  · intro hn
    by_cases h106 : (n : ℕ) = 106
    · rw [hc]
      exact reproduces_of_eq_106_or_120 _ (Or.inl h106) hq'
    by_cases h120 : (n : ℕ) = 120
    · rw [hc]
      exact reproduces_of_eq_106_or_120 _ (Or.inr h120) hq'
    exact reproduces_of_mem_fifteen _ hq (ofWolfram_mem_fifteen n hn h106 h120)

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.reproduces_iff_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproduces_iff_mem

set_option linter.style.longLine false in
/-- info: 'ECA.reproducing_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproducing_card

set_option linter.style.longLine false in
/-- info: 'ECA.reproducingNumbers_quiescent_growing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.reproducingNumbers_quiescent_growing
