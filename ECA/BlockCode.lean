module

public import ECA.Dilation
public import ECA.EndpointClasses
import all ECA.EndpointClasses

/-!
# Sliding block codes conserved by a step of a quiescent radius-one rule

A sliding block code of window `L` reads the cells `i` to `i + L - 1` through a local rule `g`
that sends the zero window to zero. A step of a quiescent rule `f` leaves the code unchanged
exactly where `g` takes the same value on the step's image of the window's middle and on the
middle itself, a finite identity over the `L + 2` cells a step reads, so it is decided at each
table.

* `FiniteConfiguration.blockCode` and `FiniteConfiguration.blockCode_apply` — the code of a
  finite configuration and its local rule.
* `LocalRule.blockCode_finRule_carry` — the criterion with two local rules: if `h` of the image of
  every window of `L + 2` cells is `g` of its middle `L` cells, a step takes the code of `h` to the
  code of `g`.
* `LocalRule.blockCode_finRule` — the criterion for one local rule: if `g` agrees on the image of
  every window of `L + 2` cells and on its middle `L` cells, a step conserves the code.
* `LocalRule.blockCode_finRule_nonvacuous` and `LocalRule.blockCode_finRule_carry_nonvacuous` —
  the hypotheses of the two criteria hold together, at table `206` with a code that is not zero
  and at table `50` with the codes of `100110` and `011001`.
* `blockCode_finRule_f206`, `blockCode_finRule_f220`, `blockCode_finRule_f202`,
  `blockCode_finRule_f216`, `blockCode_finRule_f50` and `blockCode_finRule_f178` — the six
  instances: tables at which a step conserves a code, the local rule sending the zero window to
  zero. The codes mark the patterns `10`, `01`, `110`, `011` and, at the last two tables, the
  pair `100110`, `011001`.
* `code100110`, `code011001`, `FiniteConfiguration.slipPhases` — the two codes separately, and
  the pair they make, with `FiniteConfiguration.slipPhases_zero` and
  `FiniteConfiguration.slipPhases_translate`.
* `slipPhases_finRule_f50` and `slipPhases_finRule_f178` — a step at table `50` or `178` takes the
  pair of codes to the swapped pair, and `swap_slipPhases_ne` — a nonzero pair is not its own
  swap, no cell carrying both marks.
* `growingPart_f50_eq_ne_zero` and `growingPart_f178_eq_ne_zero` — at tables `50` and `178` with
  the support diameter, the growing part is the nonzero states.
* `growingPart_f206_eq_ne_zero` and `growingPart_f220_eq_ne_zero` — at tables `206` and `220`, one
  end of a nonzero state moving out one cell a step and the other staying, the growing part is the
  nonzero states.
* `LocalRule.iterate_finRule_pair` — two adjacent set cells stay set along the orbit of a rule whose
  local rule gives `1` at `011`, `111` and `110`.
* `LocalRule.mem_growingPart_of_leftTap_pair` and `LocalRule.mem_growingPart_of_rightTap_pair` — a
  state with two adjacent set cells is in the growing part under the support diameter when the
  table keeps the pair and moves the left (right) end out one cell a step.
* `mem_growingPart_f202_of_pair` and `mem_growingPart_f216_of_pair` — at tables `202` and `216` a
  state with two adjacent set cells is in the growing part, with
  `mem_growingPart_f202_of_pair_nonvacuous` its hypotheses holding together; the growing part is
  not the nonzero states there, a single set cell moving without growing.
-/

@[expose] public section

namespace ECA

namespace FiniteConfiguration

/-- The sliding block code of window `L` with local rule `g`, `g` sending the zero window to
zero: the cell `i` of the image is `g` of the cells `i` to `i + L - 1`. -/
noncomputable def blockCode (L : ℕ) (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (s : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.onFinset ((Finset.range L).biUnion fun k => s.support.image (· - (k : ℤ)))
    (fun i => g (fun k : Fin L => s (i + (k : ℕ)))) (by
      intro i hi
      by_contra hcon
      apply hi
      have h0 : (fun k : Fin L => s (i + (k : ℕ))) = 0 := by
        funext k
        by_contra hk
        exact hcon (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr k.2,
          Finset.mem_image.mpr ⟨i + (k : ℕ), Finsupp.mem_support_iff.mpr hk, by ring⟩⟩)
      rw [h0]
      exact hg)

/-- The sliding block code's local rule, a window of `L` cells. -/
theorem blockCode_apply (L : ℕ) (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (s : FiniteConfiguration) (i : ℤ) :
    blockCode L g hg s i = g (fun k : Fin L => s (i + (k : ℕ))) := by
  simp [blockCode, Finsupp.onFinset_apply]

end FiniteConfiguration

namespace LocalRule

/-- **The criterion with two local rules**: a step of a quiescent rule carries the sliding block
code of `h` to the sliding block code of `g` when `h` of the step's image of any window of `L + 2`
cells equals `g` of the window's middle `L` cells. -/
theorem blockCode_finRule_carry (f : LocalRule) (hq : f 0 0 0 = 0) {L : ℕ}
    (g h : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0) (hh : h 0 = 0)
    (hloc : ∀ u : Fin (L + 2) → ZMod 2,
      h (fun k : Fin L => f (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩) (u ⟨k + 2, by omega⟩)) =
        g (fun k : Fin L => u ⟨k + 1, by omega⟩))
    (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode L h hh (finRule f hq s) =
      FiniteConfiguration.blockCode L g hg s := by
  ext i
  rw [FiniteConfiguration.blockCode_apply, FiniteConfiguration.blockCode_apply]
  have hu := hloc (fun j : Fin (L + 2) => s (i - 1 + (j : ℕ)))
  have e1 : (fun k : Fin L => finRule f hq s (i + (k : ℕ))) =
      fun k : Fin L => f (s (i - 1 + ((⟨k, by omega⟩ : Fin (L + 2)) : ℕ)))
        (s (i - 1 + ((⟨k + 1, by omega⟩ : Fin (L + 2)) : ℕ)))
        (s (i - 1 + ((⟨k + 2, by omega⟩ : Fin (L + 2)) : ℕ))) := by
    funext k
    rw [finRule_apply]
    congr 2 <;> push_cast <;> ring_nf
  have e2 : (fun k : Fin L => s (i + (k : ℕ))) =
      fun k : Fin L => s (i - 1 + ((⟨k + 1, by omega⟩ : Fin (L + 2)) : ℕ)) := by
    funext k
    congr 1
    push_cast
    ring
  rw [e1, e2]
  exact hu

/-- **The criterion**: a step of a quiescent rule conserves a sliding block code when its local
rule takes the same value on the step's image of every window of `L + 2` cells (the `L` cells
the image reads) and on the window's middle `L` cells. -/
theorem blockCode_finRule (f : LocalRule) (hq : f 0 0 0 = 0) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hloc : ∀ u : Fin (L + 2) → ZMod 2,
      g (fun k : Fin L => f (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩) (u ⟨k + 2, by omega⟩)) =
        g (fun k : Fin L => u ⟨k + 1, by omega⟩))
    (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode L g hg (finRule f hq s) =
      FiniteConfiguration.blockCode L g hg s :=
  blockCode_finRule_carry f hq g g hg hg hloc s

end LocalRule

/-- Rule `50`. -/
def f50 : LocalRule := wolframRule 50

/-- Rule `178`. -/
def f178 : LocalRule := wolframRule 178

/-- Rule `206`. -/
def f206 : LocalRule := wolframRule 206

/-- Rule `216`. -/
def f216 : LocalRule := wolframRule 216

/-- Rule `220`. -/
def f220 : LocalRule := wolframRule 220

/-- Rule `50` is quiescent. -/
theorem hq50 : f50 0 0 0 = 0 := by decide

/-- Rule `178` is quiescent. -/
theorem hq178 : f178 0 0 0 = 0 := by decide

/-- Rule `206` is quiescent. -/
theorem hq206 : f206 0 0 0 = 0 := by decide

/-- Rule `216` is quiescent. -/
theorem hq216 : f216 0 0 0 = 0 := by decide

/-- Rule `220` is quiescent. -/
theorem hq220 : f220 0 0 0 = 0 := by decide

/-- The local rule of the code marking the pattern `10`: a window of two cells. -/
def codeF206 : (Fin 2 → ZMod 2) → ZMod 2 := fun v => v 0 * (1 + v 1)

/-- The local rule of the code marking the pattern `01`: a window of two cells. -/
def codeF220 : (Fin 2 → ZMod 2) → ZMod 2 := fun v => (1 + v 0) * v 1

/-- The local rule of the code marking the pattern `110`: a window of three cells. -/
def codeF202 : (Fin 3 → ZMod 2) → ZMod 2 := fun v => v 0 * v 1 * (1 + v 2)

/-- The local rule of the code marking the pattern `011`: a window of three cells. -/
def codeF216 : (Fin 3 → ZMod 2) → ZMod 2 := fun v => (1 + v 0) * v 1 * v 2

/-- The local rule of the code marking the patterns `100110` and `011001`: a window of six
cells. -/
def codeF50 : (Fin 6 → ZMod 2) → ZMod 2 := fun v =>
  v 0 * (1 + v 1) * (1 + v 2) * v 3 * v 4 * (1 + v 5) +
    (1 + v 0) * v 1 * v 2 * (1 + v 3) * (1 + v 4) * v 5

/-- The local rule of the code at table `178`: the same two patterns as at table `50`. -/
def codeF178 : (Fin 6 → ZMod 2) → ZMod 2 := codeF50

/-- The code of table `206` sends the zero window to zero. -/
theorem codeF206_zero : codeF206 0 = 0 := by decide

/-- The code of table `220` sends the zero window to zero. -/
theorem codeF220_zero : codeF220 0 = 0 := by decide

/-- The code of table `202` sends the zero window to zero. -/
theorem codeF202_zero : codeF202 0 = 0 := by decide

/-- The code of table `216` sends the zero window to zero. -/
theorem codeF216_zero : codeF216 0 = 0 := by decide

/-- The code of table `50` sends the zero window to zero. -/
theorem codeF50_zero : codeF50 0 = 0 := by decide

/-- The code of table `178` sends the zero window to zero. -/
theorem codeF178_zero : codeF178 0 = 0 := by decide

/-- The local rule of the code marking the pattern `100110`: a window of six cells. -/
def code100110 : (Fin 6 → ZMod 2) → ZMod 2 := fun v =>
  v 0 * (1 + v 1) * (1 + v 2) * v 3 * v 4 * (1 + v 5)

/-- The local rule of the code marking the pattern `011001`: a window of six cells. -/
def code011001 : (Fin 6 → ZMod 2) → ZMod 2 := fun v =>
  (1 + v 0) * v 1 * v 2 * (1 + v 3) * (1 + v 4) * v 5

/-- The code of the pattern `100110` sends the zero window to zero. -/
theorem code100110_zero : code100110 0 = 0 := by decide

/-- The code of the pattern `011001` sends the zero window to zero. -/
theorem code011001_zero : code011001 0 = 0 := by decide

/-- **Table `206` conserves the pattern `10`.** -/
theorem blockCode_finRule_f206 (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode 2 codeF206 codeF206_zero (LocalRule.finRule f206 hq206 s) =
      FiniteConfiguration.blockCode 2 codeF206 codeF206_zero s :=
  LocalRule.blockCode_finRule f206 hq206 codeF206 codeF206_zero (by decide +kernel) s

/-- **Table `220` conserves the pattern `01`.** -/
theorem blockCode_finRule_f220 (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode 2 codeF220 codeF220_zero (LocalRule.finRule f220 hq220 s) =
      FiniteConfiguration.blockCode 2 codeF220 codeF220_zero s :=
  LocalRule.blockCode_finRule f220 hq220 codeF220 codeF220_zero (by decide +kernel) s

/-- **Table `202` conserves the pattern `110`.** -/
theorem blockCode_finRule_f202 (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode 3 codeF202 codeF202_zero (LocalRule.finRule f202 hq202 s) =
      FiniteConfiguration.blockCode 3 codeF202 codeF202_zero s :=
  LocalRule.blockCode_finRule f202 hq202 codeF202 codeF202_zero (by decide +kernel) s

/-- **Table `216` conserves the pattern `011`.** -/
theorem blockCode_finRule_f216 (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode 3 codeF216 codeF216_zero (LocalRule.finRule f216 hq216 s) =
      FiniteConfiguration.blockCode 3 codeF216 codeF216_zero s :=
  LocalRule.blockCode_finRule f216 hq216 codeF216 codeF216_zero (by decide +kernel) s

/-- **Table `50` conserves the patterns `100110` and `011001`.** -/
theorem blockCode_finRule_f50 (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode 6 codeF50 codeF50_zero (LocalRule.finRule f50 hq50 s) =
      FiniteConfiguration.blockCode 6 codeF50 codeF50_zero s :=
  LocalRule.blockCode_finRule f50 hq50 codeF50 codeF50_zero (by decide +kernel) s

/-- **Table `178` conserves the patterns `100110` and `011001`.** -/
theorem blockCode_finRule_f178 (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode 6 codeF178 codeF178_zero (LocalRule.finRule f178 hq178 s) =
      FiniteConfiguration.blockCode 6 codeF178 codeF178_zero s :=
  LocalRule.blockCode_finRule f178 hq178 codeF178 codeF178_zero (by decide +kernel) s

namespace FiniteConfiguration

/-- The two phases of a slip: the sliding block codes marking `100110` and `011001`, read as a
pair. -/
noncomputable def slipPhases (s : FiniteConfiguration) :
    FiniteConfiguration × FiniteConfiguration :=
  (blockCode 6 code100110 code100110_zero s, blockCode 6 code011001 code011001_zero s)

/-- A sliding block code takes the zero state to the zero state. -/
private theorem blockCode_zero (L : ℕ) (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0) :
    blockCode L g hg 0 = 0 := by
  ext i
  rw [blockCode_apply]
  have h0 : (fun k : Fin L => (0 : FiniteConfiguration) (i + (k : ℕ))) = 0 := by
    funext k
    simp
  rw [h0]
  exact hg

/-- A translate's cell is the cell shifted back. -/
private theorem translate_apply_cell (k : ℤ) (t : FiniteConfiguration) (x : ℤ) :
    translate k t x = t (x - k) := by
  have h := Finsupp.mapDomain_apply_of_injective (add_left_injective k) t (x - k)
  rw [sub_add_cancel] at h
  exact h

/-- A sliding block code commutes with translation. -/
private theorem blockCode_translate (L : ℕ) (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (k : ℤ) (s : FiniteConfiguration) :
    blockCode L g hg (translate k s) = translate k (blockCode L g hg s) := by
  ext x
  rw [translate_apply_cell k (blockCode L g hg s) x, blockCode_apply, blockCode_apply]
  congr 1
  funext j
  rw [translate_apply_cell]
  congr 1
  ring

/-- The pair of phases of the zero state is the zero pair. -/
theorem slipPhases_zero : slipPhases 0 = 0 :=
  Prod.ext (blockCode_zero 6 code100110 code100110_zero)
    (blockCode_zero 6 code011001 code011001_zero)

/-- The reading of a translate is the pair of translates. -/
theorem slipPhases_translate (k : ℤ) (s : FiniteConfiguration) :
    slipPhases (translate k s) = (translate k (slipPhases s).1, translate k (slipPhases s).2) :=
  Prod.ext (blockCode_translate 6 code100110 code100110_zero k s)
    (blockCode_translate 6 code011001 code011001_zero k s)

end FiniteConfiguration

/-- **A step of table `50` swaps the two phases of the slip**: the code marking `100110` of the
image is the code marking `011001` of the state, and conversely. -/
theorem slipPhases_finRule_f50 (s : FiniteConfiguration) :
    FiniteConfiguration.slipPhases (LocalRule.finRule f50 hq50 s) =
      Prod.swap (FiniteConfiguration.slipPhases s) :=
  Prod.ext
    (LocalRule.blockCode_finRule_carry f50 hq50 code011001 code100110 code011001_zero
      code100110_zero (by decide +kernel) s)
    (LocalRule.blockCode_finRule_carry f50 hq50 code100110 code011001 code100110_zero
      code011001_zero (by decide +kernel) s)

/-- **A step of table `178` swaps the two phases of the slip**: the code marking `100110` of the
image is the code marking `011001` of the state, and conversely. -/
theorem slipPhases_finRule_f178 (s : FiniteConfiguration) :
    FiniteConfiguration.slipPhases (LocalRule.finRule f178 hq178 s) =
      Prod.swap (FiniteConfiguration.slipPhases s) :=
  Prod.ext
    (LocalRule.blockCode_finRule_carry f178 hq178 code011001 code100110 code011001_zero
      code100110_zero (by decide +kernel) s)
    (LocalRule.blockCode_finRule_carry f178 hq178 code100110 code011001 code100110_zero
      code011001_zero (by decide +kernel) s)

/-- No window carries both marks. -/
private theorem code100110_mul_code011001 (v : Fin 6 → ZMod 2) :
    code100110 v * code011001 v = 0 := by
  revert v
  decide +kernel

/-- **A nonzero pair of phases is not its own swap**: no cell carries both marks, so the two
readings agree only where both are zero. -/
theorem swap_slipPhases_ne (s : FiniteConfiguration)
    (hs : FiniteConfiguration.slipPhases s ≠ 0) :
    Prod.swap (FiniteConfiguration.slipPhases s) ≠ FiniteConfiguration.slipPhases s := by
  intro h
  apply hs
  have h2 : (FiniteConfiguration.slipPhases s).2 = (FiniteConfiguration.slipPhases s).1 :=
    congrArg Prod.fst h
  have hz : ∀ i, (FiniteConfiguration.slipPhases s).1 i = 0 := by
    intro i
    have hi : (FiniteConfiguration.slipPhases s).2 i = (FiniteConfiguration.slipPhases s).1 i :=
      congrArg (fun x : FiniteConfiguration => x i) h2
    have hm : (FiniteConfiguration.slipPhases s).1 i * (FiniteConfiguration.slipPhases s).2 i =
        0 := by
      simp only [FiniteConfiguration.slipPhases, FiniteConfiguration.blockCode_apply]
      exact code100110_mul_code011001 _
    rw [hi] at hm
    revert hm
    generalize (FiniteConfiguration.slipPhases s).1 i = a
    revert a
    decide
  refine Prod.ext (by ext i; exact hz i) ?_
  ext i
  exact (congrArg (fun x : FiniteConfiguration => x i) h2).trans (hz i)

/-- **The growing part of rule `50` under the support diameter is the nonzero states**
([RuleSpace] §2 Proposition 2.13(i) at rule `50`, whose endpoint moves are exact, one cell at each
side: `001` and `100` both give `1`). -/
theorem growingPart_f50_eq_ne_zero :
    Nonautonomous.GrowingPart (LocalRule.finRule f50 hq50) FiniteConfiguration.diam =
      {s | s ≠ 0} := by
  have h1 : f50 0 0 1 = 1 := by decide
  have h2 : f50 1 0 0 = 1 := by decide
  refine growingPart_eq_ne_zero (U := LocalRule.finRule f50 hq50)
    (fun {s} => ⟨fun h => ?_, fun h => ?_⟩)
    (fun {s} hne hne' => LocalRule.finRule_min'_of_leftTap (f := f50) (hq := hq50)
      h1 hne hne')
    (fun {s} hne hne' => LocalRule.finRule_max'_of_rightTap (f := f50) (hq := hq50)
      h2 hne hne')
  · by_contra hs
    exact LocalRule.finRule_ne_zero_of_leftTap (f := f50) (hq := hq50) h1 hs h
  · subst h
    ext i
    rw [LocalRule.finRule_apply]
    simpa using hq50

/-- **The growing part of rule `178` under the support diameter is the nonzero states**
([RuleSpace] §2 Proposition 2.13(i) at rule `178`, whose endpoint moves are exact, one cell at each
side: `001` and `100` both give `1`). -/
theorem growingPart_f178_eq_ne_zero :
    Nonautonomous.GrowingPart (LocalRule.finRule f178 hq178) FiniteConfiguration.diam =
      {s | s ≠ 0} := by
  have h1 : f178 0 0 1 = 1 := by decide
  have h2 : f178 1 0 0 = 1 := by decide
  refine growingPart_eq_ne_zero (U := LocalRule.finRule f178 hq178)
    (fun {s} => ⟨fun h => ?_, fun h => ?_⟩)
    (fun {s} hne hne' => LocalRule.finRule_min'_of_leftTap (f := f178) (hq := hq178)
      h1 hne hne')
    (fun {s} hne hne' => LocalRule.finRule_max'_of_rightTap (f := f178) (hq := hq178)
      h2 hne hne')
  · by_contra hs
    exact LocalRule.finRule_ne_zero_of_leftTap (f := f178) (hq := hq178) h1 hs h
  · subst h
    ext i
    rw [LocalRule.finRule_apply]
    simpa using hq178

/-- A quiescent rule's step takes a nonzero state to a state whose diameter has grown by
`(a + b).toNat`, when the two ends move by `a` and `b`: the growing part under the support diameter
is then the nonzero states. -/
private theorem growingPart_eq_ne_zero_of_moves {U : FiniteConfiguration → FiniteConfiguration}
    {a b : ℤ}
    (hUeqZero : ∀ {s : FiniteConfiguration}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : FiniteConfiguration} (hne : s.support.Nonempty) (hne' : (U
      s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : FiniteConfiguration} (hne : s.support.Nonempty) (hne' : (U
      s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (hab : 0 < (a + b).toNat) :
    Nonautonomous.GrowingPart U FiniteConfiguration.diam = {s | s ≠ 0} := by
  ext s
  constructor
  · intro hs h
    subst h
    obtain ⟨k, hk⟩ := hs 0
    rw [Function.iterate_fixed (hUeqZero.mpr rfl) k] at hk
    simp [FiniteConfiguration.diam] at hk
  · intro hs N
    refine ⟨N + 1, ?_⟩
    rw [FiniteConfiguration.diam_iterate_of_moves hUeqZero hUmin' hUmax' hs]
    nlinarith

/-- A step of a quiescent rule takes the zero state to itself. -/
private theorem finRule_eq_zero_of_eq_zero (f : LocalRule) (hq : f 0 0 0 = 0)
    {s : FiniteConfiguration} (h : s = 0) : LocalRule.finRule f hq s = 0 := by
  subst h
  ext i
  rw [LocalRule.finRule_apply]
  simpa using hq

/-- **The growing part of rule `206` under the support diameter is the nonzero states**: the left
end of a nonzero state moves out one cell a step (`001` gives `1`) and the right end stays
(`100` gives `0`, `010` and `110` give `1`), so the diameter grows by one a step. -/
theorem growingPart_f206_eq_ne_zero :
    Nonautonomous.GrowingPart (LocalRule.finRule f206 hq206) FiniteConfiguration.diam =
      {s | s ≠ 0} := by
  have h1 : f206 0 0 1 = 1 := by decide
  have h2 : f206 1 0 0 = 0 := by decide
  have h3 : f206 0 1 0 = 1 := by decide
  have h4 : f206 1 1 0 = 1 := by decide
  refine growingPart_eq_ne_zero_of_moves (U := LocalRule.finRule f206 hq206) (a := 1) (b := 0)
    (fun {s} => ⟨fun h => ?_, fun h => finRule_eq_zero_of_eq_zero f206 hq206 h⟩)
    (fun {s} hne hne' => LocalRule.finRule_min'_of_leftTap (f := f206) (hq := hq206)
      h1 hne hne')
    (fun {s} hne hne' => by
      rw [LocalRule.finRule_max'_of_rightHold (f := f206) (hq := hq206) h2 h3 h4 hne hne',
        add_zero])
    (by decide)
  by_contra hs
  exact LocalRule.finRule_ne_zero_of_leftTap (f := f206) (hq := hq206) h1 hs h

/-- **The growing part of rule `220` under the support diameter is the nonzero states**, the mirror
of rule `206`: the right end moves out one cell a step (`100` gives `1`) and the left end stays
(`001` gives `0`, `010` and `011` give `1`). -/
theorem growingPart_f220_eq_ne_zero :
    Nonautonomous.GrowingPart (LocalRule.finRule f220 hq220) FiniteConfiguration.diam =
      {s | s ≠ 0} := by
  have h1 : f220 1 0 0 = 1 := by decide
  have h2 : f220 0 0 1 = 0 := by decide
  have h3 : f220 0 1 0 = 1 := by decide
  have h4 : f220 0 1 1 = 1 := by decide
  refine growingPart_eq_ne_zero_of_moves (U := LocalRule.finRule f220 hq220) (a := 0) (b := 1)
    (fun {s} => ⟨fun h => ?_, fun h => finRule_eq_zero_of_eq_zero f220 hq220 h⟩)
    (fun {s} hne hne' => by
      rw [LocalRule.finRule_min'_of_leftHold (f := f220) (hq := hq220) h2 h3 h4 hne hne',
        sub_zero])
    (fun {s} hne hne' => LocalRule.finRule_max'_of_rightTap (f := f220) (hq := hq220)
      h1 hne hne')
    (by decide)
  by_contra hs
  exact LocalRule.finRule_ne_zero_of_rightTap (f := f220) (hq := hq220) h1 hs h

/-- A cell of a finite configuration is `0` or `1`. -/
private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- Two adjacent set cells stay set after a step of a rule whose local rule gives `1` at `011`,
`111` and `110`. -/
private theorem pair_finRule {f : LocalRule} {hq : f 0 0 0 = 0} (h1 : f 0 1 1 = 1)
    (h2 : f 1 1 1 = 1) (h3 : f 1 1 0 = 1) {s : FiniteConfiguration} {i : ℤ} (h0 : s i = 1)
    (h0' : s (i + 1) = 1) :
    LocalRule.finRule f hq s i = 1 ∧ LocalRule.finRule f hq s (i + 1) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [LocalRule.finRule_apply, h0, h0']
    rcases zmod_two_cases (s (i - 1)) with h | h <;> rw [h]
    · exact h1
    · exact h2
  · rw [LocalRule.finRule_apply, show i + 1 - 1 = i by ring, h0, h0']
    rcases zmod_two_cases (s (i + 1 + 1)) with h | h <;> rw [h]
    · exact h3
    · exact h2

namespace LocalRule

/-- **Two adjacent set cells stay set along the orbit** of a quiescent rule whose local rule gives
`1` at `011`, `111` and `110`. -/
theorem iterate_finRule_pair {f : LocalRule} {hq : f 0 0 0 = 0} (h1 : f 0 1 1 = 1)
    (h2 : f 1 1 1 = 1) (h3 : f 1 1 0 = 1) {s : FiniteConfiguration} {i : ℤ} (h0 : s i = 1)
    (h0' : s (i + 1) = 1) (k : ℕ) :
    ((LocalRule.finRule f hq)^[k] s) i = 1 ∧ ((LocalRule.finRule f hq)^[k] s) (i + 1) = 1 := by
  induction k with
  | zero => exact ⟨h0, h0'⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact pair_finRule h1 h2 h3 ih.1 ih.2

/-- **A state with two adjacent set cells is in the growing part** when the left end moves out one
cell a step and the pair persists: the diameter is at least the distance from the moving end to
the pair. -/
theorem mem_growingPart_of_leftTap_pair {f : LocalRule} {hq : f 0 0 0 = 0}
    (h0 : f 0 0 1 = 1) (h1 : f 0 1 1 = 1) (h2 : f 1 1 1 = 1) (h3 : f 1 1 0 = 1)
    {s : FiniteConfiguration} {i : ℤ} (hi : s i = 1) (hi' : s (i + 1) = 1) :
    s ∈ Nonautonomous.GrowingPart (LocalRule.finRule f hq) FiniteConfiguration.diam := by
  have hne : ∀ k : ℕ, ((LocalRule.finRule f hq)^[k] s).support.Nonempty := fun k =>
    ⟨i, Finsupp.mem_support_iff.mpr (by rw [(iterate_finRule_pair h1 h2 h3 hi hi' k).1]; decide)⟩
  have hmin : ∀ (k : ℕ) (hk : ((LocalRule.finRule f hq)^[k] s).support.Nonempty),
      ((LocalRule.finRule f hq)^[k] s).support.min' hk = s.support.min' (hne 0) - k := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have e : (LocalRule.finRule f hq)^[k + 1] s =
          LocalRule.finRule f hq ((LocalRule.finRule f hq)^[k] s) :=
        Function.iterate_succ_apply' _ _ _
      have hk' : (LocalRule.finRule f hq ((LocalRule.finRule f hq)^[k] s)).support.Nonempty := by
        rw [← e]
        exact hk
      rw [min'_congr (congrArg Finsupp.support e) hk hk',
        LocalRule.finRule_min'_of_leftTap (f := f) (hq := hq) h0 (hne k) hk', ih (hne k)]
      push_cast
      ring
  intro N
  refine ⟨N + (s.support.min' (hne 0) - i).toNat, ?_⟩
  have hmax : i + 1 ≤ ((LocalRule.finRule f hq)^[N + (s.support.min' (hne 0) - i).toNat] s
      ).support.max' (hne _) :=
    Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr
      (by rw [(iterate_finRule_pair h1 h2 h3 hi hi' _).2]; decide))
  have := hmin (N + (s.support.min' (hne 0) - i).toNat) (hne _)
  rw [FiniteConfiguration.diam, dite_eq_left (hne _), this]
  omega

/-- **A state with two adjacent set cells is in the growing part**, the mirror: the right end
moves out one cell a step. -/
theorem mem_growingPart_of_rightTap_pair {f : LocalRule} {hq : f 0 0 0 = 0}
    (h0 : f 1 0 0 = 1) (h1 : f 0 1 1 = 1) (h2 : f 1 1 1 = 1) (h3 : f 1 1 0 = 1)
    {s : FiniteConfiguration} {i : ℤ} (hi : s i = 1) (hi' : s (i + 1) = 1) :
    s ∈ Nonautonomous.GrowingPart (LocalRule.finRule f hq) FiniteConfiguration.diam := by
  have hne : ∀ k : ℕ, ((LocalRule.finRule f hq)^[k] s).support.Nonempty := fun k =>
    ⟨i, Finsupp.mem_support_iff.mpr (by rw [(iterate_finRule_pair h1 h2 h3 hi hi' k).1]; decide)⟩
  have hmax : ∀ (k : ℕ) (hk : ((LocalRule.finRule f hq)^[k] s).support.Nonempty),
      ((LocalRule.finRule f hq)^[k] s).support.max' hk = s.support.max' (hne 0) + k := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have e : (LocalRule.finRule f hq)^[k + 1] s =
          LocalRule.finRule f hq ((LocalRule.finRule f hq)^[k] s) :=
        Function.iterate_succ_apply' _ _ _
      have hk' : (LocalRule.finRule f hq ((LocalRule.finRule f hq)^[k] s)).support.Nonempty := by
        rw [← e]
        exact hk
      rw [max'_congr (congrArg Finsupp.support e) hk hk',
        LocalRule.finRule_max'_of_rightTap (f := f) (hq := hq) h0 (hne k) hk', ih (hne k)]
      push_cast
      ring
  intro N
  refine ⟨N + (i - s.support.max' (hne 0)).toNat, ?_⟩
  have hmin : ((LocalRule.finRule f hq)^[N + (i - s.support.max' (hne 0)).toNat] s
      ).support.min' (hne _) ≤ i :=
    Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr
      (by rw [(iterate_finRule_pair h1 h2 h3 hi hi' _).1]; decide))
  have := hmax (N + (i - s.support.max' (hne 0)).toNat) (hne _)
  rw [FiniteConfiguration.diam, dite_eq_left (hne _), this]
  omega

end LocalRule

/-- **A state with two adjacent set cells is in the growing part of rule `202` under the support
diameter**: two adjacent `1`s never change (`011`, `110` and `111` give `1`) and the left end of
the support moves out one cell a step (`001` gives `1`), so the diameter is unbounded along the
orbit. The growing part is not the nonzero states at this table: a single `1` moves one cell a
step and does not grow (`010` gives `0`). -/
theorem mem_growingPart_f202_of_pair (s : FiniteConfiguration) (i : ℤ) (h0 : s i = 1)
    (h1 : s (i + 1) = 1) :
    s ∈ Nonautonomous.GrowingPart (LocalRule.finRule f202 hq202) FiniteConfiguration.diam :=
  LocalRule.mem_growingPart_of_leftTap_pair (f := f202) (hq := hq202) (by decide) (by decide)
    (by decide) (by decide) h0 h1

/-- **A state with two adjacent set cells is in the growing part of rule `216` under the support
diameter**, the mirror of rule `202`: two adjacent `1`s never change and the right end of the
support moves out one cell a step (`100` gives `1`). -/
theorem mem_growingPart_f216_of_pair (s : FiniteConfiguration) (i : ℤ) (h0 : s i = 1)
    (h1 : s (i + 1) = 1) :
    s ∈ Nonautonomous.GrowingPart (LocalRule.finRule f216 hq216) FiniteConfiguration.diam :=
  LocalRule.mem_growingPart_of_rightTap_pair (f := f216) (hq := hq216) (by decide) (by decide)
    (by decide) (by decide) h0 h1

/-- **The pair lemma's hypotheses are jointly satisfiable**, at table `202`: the state `11` has a
set cell at `0` and at `1`. -/
theorem mem_growingPart_f202_of_pair_nonvacuous :
    ∃ (s : FiniteConfiguration) (i : ℤ), s i = 1 ∧ s (i + 1) = 1 :=
  ⟨Finsupp.single 0 1 + Finsupp.single 1 1, 0, by simp, by simp⟩

namespace LocalRule

/-- **The criterion's hypotheses are jointly satisfiable**, at table `206` with the code of the
pattern `10`: the table is quiescent, its local rule sends the zero window to zero, the finite
identity holds at every window, and the code of a lone set cell is not zero. -/
theorem blockCode_finRule_nonvacuous :
    f206 0 0 0 = 0 ∧ codeF206 0 = 0 ∧
      (∀ u : Fin (2 + 2) → ZMod 2,
        codeF206 (fun k : Fin 2 => f206 (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩)
            (u ⟨k + 2, by omega⟩)) = codeF206 (fun k : Fin 2 => u ⟨k + 1, by omega⟩)) ∧
      ∃ s : FiniteConfiguration,
        FiniteConfiguration.blockCode 2 codeF206 codeF206_zero s ≠ 0 := by
  refine ⟨hq206, codeF206_zero, by decide +kernel, Finsupp.single 0 1, ?_⟩
  intro h
  have h0 := congrArg (fun x : FiniteConfiguration => x 0) h
  simp only [FiniteConfiguration.blockCode_apply, Finsupp.coe_zero, Pi.zero_apply] at h0
  revert h0
  simp [codeF206]


/-- **The two-rule criterion's hypotheses are jointly satisfiable**, at table `50` with `g` the
code of the pattern `100110` and `h` the code of `011001`: the table is quiescent, both local rules
send the zero window to zero, the finite identity holds at every window, and the code of `100110`
reads a state at which it is not zero. -/
theorem blockCode_finRule_carry_nonvacuous :
    f50 0 0 0 = 0 ∧ code100110 0 = 0 ∧ code011001 0 = 0 ∧
      (∀ u : Fin (6 + 2) → ZMod 2,
        code011001 (fun k : Fin 6 => f50 (u ⟨k, by omega⟩) (u ⟨k + 1, by omega⟩)
            (u ⟨k + 2, by omega⟩)) = code100110 (fun k : Fin 6 => u ⟨k + 1, by omega⟩)) ∧
      ∃ s : FiniteConfiguration,
        FiniteConfiguration.blockCode 6 code100110 code100110_zero s ≠ 0 := by
  refine ⟨hq50, code100110_zero, code011001_zero, by decide +kernel,
    Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1, ?_⟩
  intro h
  have h0 := congrArg (fun x : FiniteConfiguration => x 0) h
  simp only [FiniteConfiguration.blockCode_apply, Finsupp.coe_zero, Pi.zero_apply] at h0
  revert h0
  simp [code100110]

end LocalRule

end ECA
