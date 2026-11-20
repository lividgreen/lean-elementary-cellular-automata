module

public import ECA.Dilation
public import ECA.EndpointClasses

/-!
# A sliding block code that rule `222` conserves

A cell of rule `222` is `0` after a step exactly when its neighbourhood was `000` or `101`. So a
pair of holes of the pattern `10101` — two clear cells, each between two set ones, sharing the
middle set cell — is carried through a step unchanged, and a pair that the step produces was
already there: the two holes came from `000` or `101` around each, and the middle cell cannot have
been clear, since `000` on both sides would have cleared it.

* `FiniteConfiguration.holePairs` — the sliding block code of window five that marks, by a `1` at
  the cell `i`, the pattern `10101` read from `i - 1` to `i + 3`.
* `FiniteConfiguration.holePairs_apply`, `FiniteConfiguration.holePairs_zero` and
  `FiniteConfiguration.holePairs_translate` — its local rule, its value at the zero state, and its
  commuting with translation.
* `holePairs_finRule_f222` — the marked set is unchanged by every step of rule `222`.
-/

@[expose] public section

namespace ECA

namespace FiniteConfiguration

/-- The cells `i` at which `s` reads `10101` from `i - 1` to `i + 3`, marked `1`. -/
noncomputable def holePairs (s : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.onFinset (s.support.image (· + 1))
    (fun i => s (i - 1) * (1 + s i) * s (i + 1) * (1 + s (i + 2)) * s (i + 3)) (by
      intro i hi
      refine Finset.mem_image.mpr ⟨i - 1, ?_, by ring⟩
      rw [Finsupp.mem_support_iff]
      intro h
      exact hi (by rw [h]; ring))

/-- The sliding block code's local rule, a window of five cells. -/
theorem holePairs_apply (s : FiniteConfiguration) (i : ℤ) :
    holePairs s i = s (i - 1) * (1 + s i) * s (i + 1) * (1 + s (i + 2)) * s (i + 3) := by
  simp [holePairs, Finsupp.onFinset_apply]

/-- The zero state has no mark. -/
theorem holePairs_zero : holePairs 0 = 0 := by
  ext i
  simp [holePairs_apply]

/-- The reading of a translate is the translate of the reading. -/
theorem holePairs_translate (k : ℤ) (s : FiniteConfiguration) :
    holePairs (translate k s) = translate k (holePairs s) := by
  have hap : ∀ (t : FiniteConfiguration) (x : ℤ), translate k t x = t (x - k) := by
    intro t x
    have h := Finsupp.mapDomain_apply_of_injective (add_left_injective k) t (x - k)
    rw [sub_add_cancel] at h
    exact h
  ext x
  simp only [holePairs_apply, hap]
  rw [show x - 1 - k = x - k - 1 by ring, show x + 1 - k = x - k + 1 by ring,
    show x + 2 - k = x - k + 2 by ring, show x + 3 - k = x - k + 3 by ring]

end FiniteConfiguration

/-- **Rule `222` conserves the pattern `10101`**: the marked set of a state is unchanged by a step.
A cell is `0` after a step exactly when its neighbourhood was `000` or `101`, so the two holes and
the three set cells of a mark persist; and if the image has a mark, its two holes came from `000`
or `101` around each, which share the middle cell, and `000` there would have cleared it. -/
theorem holePairs_finRule_f222 (s : FiniteConfiguration) :
    FiniteConfiguration.holePairs (LocalRule.finRule f222 hq222 s) =
      FiniteConfiguration.holePairs s := by
  ext i
  have e : ∀ j, LocalRule.finRule f222 hq222 s j = f222 (s (j - 1)) (s j) (s (j + 1)) :=
    fun j => LocalRule.finRule_apply f222 hq222 s j
  rw [FiniteConfiguration.holePairs_apply, FiniteConfiguration.holePairs_apply, e (i - 1), e i,
    e (i + 1), e (i + 2), e (i + 3)]
  rw [show i - 1 - 1 = i - 2 by ring, show i - 1 + 1 = i by ring, show i + 1 - 1 = i by ring,
    show i + 1 + 1 = i + 2 by ring, show i + 2 - 1 = i + 1 by ring,
    show i + 2 + 1 = i + 3 by ring, show i + 3 - 1 = i + 2 by ring,
    show i + 3 + 1 = i + 4 by ring]
  generalize s (i - 2) = a
  generalize s (i - 1) = b
  generalize s i = c
  generalize s (i + 1) = d
  generalize s (i + 2) = e'
  generalize s (i + 3) = g
  generalize s (i + 4) = h
  revert a b c d e' g h
  decide

end ECA
