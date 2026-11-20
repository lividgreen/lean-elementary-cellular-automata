module

public import ECA.BlockCode

/-!
# A table forcing a `1` from one end conserves no sliding block code but zero

A quiescent table is **left-forcing** when every neighbourhood whose left cell is `1` gives `1`,
and **right-forcing** when every neighbourhood whose right cell is `1` gives `1`. At a left-forcing
table a run of `1`s moves right at speed one, whatever stands to its right, so after `L` steps a
run of `L` cells beside a window has overwritten it; the mirror holds at a right-forcing table. A
sliding block code of window `L` that a step conserves is then conserved along `L` steps, and
reads the window before the steps and the all-ones window after them, so it takes one value on
every window, which is its value on the zero window, zero.

* `LocalRule.blockCode_eq_zero_of_leftForcing` and `LocalRule.blockCode_eq_zero_of_rightForcing` —
  at a left-forcing (right-forcing) quiescent table, a sliding block code of any window conserved
  by a step is the zero code.
* `LocalRule.blockCode_eq_zero_of_leftForcing_nonvacuous` — the hypotheses of the left-forcing
  statement hold together, at table `254` with window `1` and the zero local rule.
* `blockCode_forcing_load_bearing` — table `50`, which forces on neither side, conserves a code
  that is not zero.
* `blockCode_eq_zero_f242`, `blockCode_eq_zero_f246`, `blockCode_eq_zero_f248`,
  `blockCode_eq_zero_f250`, `blockCode_eq_zero_f252` and `blockCode_eq_zero_f254` — the six
  left-forcing tables of the radius-one rules, and `blockCode_eq_zero_f186`,
  `blockCode_eq_zero_f190`, `blockCode_eq_zero_f234` and `blockCode_eq_zero_f238` — four
  right-forcing tables: a conserved sliding block code of any window is zero.
-/

@[expose] public section

namespace ECA

namespace LocalRule

/-- A sliding block code conserved by one step is conserved by any number of steps. -/
private theorem blockCode_iterate_finRule (f : LocalRule) (hq : f 0 0 0 = 0) {L : ℕ}
    (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s)
    (t : ℕ) (s : FiniteConfiguration) :
    FiniteConfiguration.blockCode L g hg ((finRule f hq)^[t] s) =
      FiniteConfiguration.blockCode L g hg s := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', hcons, ih]

/-- A table with a neighbour forcing a `1` carries the `1` along: after `t` steps a cell is `1`
when the cell `t` places away in the forcing direction was. -/
private theorem iterate_finRule_apply_eq_one (f : LocalRule) (hq : f 0 0 0 = 0) (e : ℤ)
    (hforce : ∀ (x : FiniteConfiguration) (i : ℤ), x (i + e) = 1 → finRule f hq x i = 1)
    (t : ℕ) (s : FiniteConfiguration) (i : ℤ) (h : s (i + t * e) = 1) :
    (finRule f hq)^[t] s i = 1 := by
  induction t generalizing i with
  | zero => simpa using h
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    apply hforce
    apply ih
    rw [show i + e + (t : ℤ) * e = i + ((t + 1 : ℕ) : ℤ) * e by push_cast; ring]
    exact h

/-- The finite configuration with the window `w` on the cells `0` to `L - 1`, ones on the `L` cells
from `d` on, and zeros elsewhere, for an offset `d` between `-L` and `L`. -/
private noncomputable def windowState (L : ℕ) (w : Fin L → ZMod 2) (d : ℤ)
    (hd : -(L : ℤ) ≤ d ∧ d ≤ L) : FiniteConfiguration :=
  Finsupp.onFinset (Finset.Icc (-(L : ℤ)) (2 * L))
    (fun i => if h : 0 ≤ i ∧ i < L then w ⟨i.toNat, by omega⟩
      else if d ≤ i ∧ i < d + L then 1 else 0) (by
      intro i hi
      by_contra hcon
      apply hi
      rw [Finset.mem_Icc] at hcon
      have h1 : ¬ (0 ≤ i ∧ i < L) := by omega
      have h2 : ¬ (d ≤ i ∧ i < d + L) := by omega
      simp [h1, h2])

private theorem windowState_window (L : ℕ) (w : Fin L → ZMod 2) (d : ℤ)
    (hd : -(L : ℤ) ≤ d ∧ d ≤ L) (k : Fin L) :
    windowState L w d hd (0 + (k : ℕ)) = w k := by
  have h : 0 ≤ (0 : ℤ) + (k : ℕ) ∧ (0 : ℤ) + (k : ℕ) < L := by
    have := k.2
    omega
  simp only [windowState, Finsupp.onFinset_apply]
  rw [dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  ext
  simp

private theorem windowState_ones (L : ℕ) (w : Fin L → ZMod 2) (d : ℤ)
    (hd : -(L : ℤ) ≤ d ∧ d ≤ L) (i : ℤ) (h1 : d ≤ i) (h2 : i < d + L) (h3 : ¬ (0 ≤ i ∧ i < L)) :
    windowState L w d hd i = 1 := by
  simp [windowState, Finsupp.onFinset_apply, h3, h1, h2]

/-- **The core**: at a quiescent table in which a `1` at the cell `e` away (`e = 1` or `e = -1`)
forces a `1`, a conserved sliding block code takes at every window the value it takes at the
all-ones window. -/
private theorem blockCode_apply_eq_ones (f : LocalRule) (hq : f 0 0 0 = 0) (e : ℤ)
    (he : e = 1 ∨ e = -1)
    (hforce : ∀ (x : FiniteConfiguration) (i : ℤ), x (i + e) = 1 → finRule f hq x i = 1)
    {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s)
    (w : Fin L → ZMod 2) : g w = g (fun _ => 1) := by
  have hd : -(L : ℤ) ≤ (L : ℤ) * e ∧ (L : ℤ) * e ≤ L := by
    rcases he with rfl | rfl <;> constructor <;> omega
  set x := windowState L w ((L : ℤ) * e) hd with hx
  have h0 := blockCode_iterate_finRule f hq g hg hcons L x
  have h1 := congrArg (fun y : FiniteConfiguration => y 0) h0
  simp only [FiniteConfiguration.blockCode_apply] at h1
  have hw : (fun k : Fin L => x (0 + (k : ℕ))) = w := by
    funext k
    exact windowState_window L w _ hd k
  have hones : (fun k : Fin L => (finRule f hq)^[L] x (0 + (k : ℕ))) = fun _ => 1 := by
    funext k
    apply iterate_finRule_apply_eq_one f hq e hforce L x
    have hk := k.2
    have hne : (0 : ℤ) + (k : ℕ) + (L : ℤ) * e = (L : ℤ) * e + (k : ℕ) := by ring
    rw [hne]
    apply windowState_ones L w _ hd
    · omega
    · omega
    · rcases he with rfl | rfl <;> omega
  rw [hw, hones] at h1
  exact h1.symm

/-- **A left-forcing table conserves no sliding block code but zero.** If the quiescent table `f`
gives `1` at every neighbourhood whose left cell is `1`, and a step of `f` leaves the sliding block
code of window `L` with local rule `g` unchanged at every finite configuration, then `g` is zero at
every window: the code reads a window before `L` steps and the all-ones window after them, since
`L` cells of ones to the left of the window overwrite it. -/
theorem blockCode_eq_zero_of_leftForcing (f : LocalRule) (hq : f 0 0 0 = 0)
    (hforce : ∀ b c, f 1 b c = 1) {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 := by
  have hf : ∀ (x : FiniteConfiguration) (i : ℤ), x (i + -1) = 1 → finRule f hq x i = 1 := by
    intro x i hx
    rw [← sub_eq_add_neg] at hx
    rw [finRule_apply, hx]
    exact hforce _ _
  have h1 : ∀ w, g w = g (fun _ => 1) := fun w =>
    blockCode_apply_eq_ones f hq (-1) (Or.inr rfl) hf g hg hcons w
  funext w
  rw [h1 w, ← h1 0]
  exact hg

/-- **A right-forcing table conserves no sliding block code but zero**: the mirror of
`blockCode_eq_zero_of_leftForcing`, the `L` cells of ones standing to the right of the window and
moving left. -/
theorem blockCode_eq_zero_of_rightForcing (f : LocalRule) (hq : f 0 0 0 = 0)
    (hforce : ∀ a b, f a b 1 = 1) {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (finRule f hq s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 := by
  have hf : ∀ (x : FiniteConfiguration) (i : ℤ), x (i + 1) = 1 → finRule f hq x i = 1 := by
    intro x i hx
    rw [finRule_apply, hx]
    exact hforce _ _
  have h1 : ∀ w, g w = g (fun _ => 1) := fun w =>
    blockCode_apply_eq_ones f hq 1 (Or.inl rfl) hf g hg hcons w
  funext w
  rw [h1 w, ← h1 0]
  exact hg

/-- **The left-forcing statement's hypotheses are jointly satisfiable**, at table `254` with window
`1` and the zero local rule: the table is quiescent and left-forcing, the local rule sends the zero
window to zero, and a step conserves its code. The conclusion forces the code to be zero, so this
shows only that the forcing and the conservation hypotheses are consistent. -/
theorem blockCode_eq_zero_of_leftForcing_nonvacuous :
    f254 0 0 0 = 0 ∧ (∀ b c, f254 1 b c = 1) ∧ (0 : (Fin 1 → ZMod 2) → ZMod 2) 0 = 0 ∧
      ∀ s : FiniteConfiguration,
        FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _)
            (finRule f254 hq254 s) =
          FiniteConfiguration.blockCode 1 (0 : (Fin 1 → ZMod 2) → ZMod 2) (Pi.zero_apply _) s := by
  refine ⟨hq254, by decide, Pi.zero_apply _, fun s => ?_⟩
  ext i
  rw [FiniteConfiguration.blockCode_apply, FiniteConfiguration.blockCode_apply]
  rfl

end LocalRule

/-- **Table `50` forces on neither side and conserves a code that is not zero**: neither a `1` at
the left of the neighbourhood nor a `1` at its right gives `1` at every table entry, and the code
of the patterns `100110` and `011001` it conserves (`blockCode_finRule_f50`) reads `1` at the
window `100110`. -/
theorem blockCode_forcing_load_bearing :
    ¬ (∀ b c, f50 1 b c = 1) ∧ ¬ (∀ a b, f50 a b 1 = 1) ∧ codeF50 ≠ 0 := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have h1 := congrFun h (fun k : Fin 6 => if k = 0 ∨ k = 3 ∨ k = 4 then (1 : ZMod 2) else 0)
  revert h1
  decide

/-- Rule `242`. -/
def f242 : LocalRule := wolframRule 242

/-- Rule `242` is quiescent. -/
theorem hq242 : f242 0 0 0 = 0 := by decide

/-- Rule `246`. -/
def f246 : LocalRule := wolframRule 246

/-- Rule `246` is quiescent. -/
theorem hq246 : f246 0 0 0 = 0 := by decide

/-- Rule `248`. -/
def f248 : LocalRule := wolframRule 248

/-- Rule `248` is quiescent. -/
theorem hq248 : f248 0 0 0 = 0 := by decide

/-- Rule `250`. -/
def f250 : LocalRule := wolframRule 250

/-- Rule `250` is quiescent. -/
theorem hq250 : f250 0 0 0 = 0 := by decide

/-- Rule `252`. -/
def f252 : LocalRule := wolframRule 252

/-- Rule `252` is quiescent. -/
theorem hq252 : f252 0 0 0 = 0 := by decide

/-- Rule `186`. -/
def f186 : LocalRule := wolframRule 186

/-- Rule `186` is quiescent. -/
theorem hq186 : f186 0 0 0 = 0 := by decide

/-- Rule `190`. -/
def f190 : LocalRule := wolframRule 190

/-- Rule `190` is quiescent. -/
theorem hq190 : f190 0 0 0 = 0 := by decide

/-- Rule `234`. -/
def f234 : LocalRule := wolframRule 234

/-- Rule `234` is quiescent. -/
theorem hq234 : f234 0 0 0 = 0 := by decide

/-- Rule `238`. -/
def f238 : LocalRule := wolframRule 238

/-- Rule `238` is quiescent. -/
theorem hq238 : f238 0 0 0 = 0 := by decide

/-- **Table `242` conserves no sliding block code but zero**: it is left-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f242 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f242 hq242 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_leftForcing f242 hq242 (by decide) g hg hcons

/-- **Table `246` conserves no sliding block code but zero**: it is left-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f246 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f246 hq246 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_leftForcing f246 hq246 (by decide) g hg hcons

/-- **Table `248` conserves no sliding block code but zero**: it is left-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f248 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f248 hq248 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_leftForcing f248 hq248 (by decide) g hg hcons

/-- **Table `250` conserves no sliding block code but zero**: it is left-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f250 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f250 hq250 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_leftForcing f250 hq250 (by decide) g hg hcons

/-- **Table `252` conserves no sliding block code but zero**: it is left-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f252 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f252 hq252 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_leftForcing f252 hq252 (by decide) g hg hcons

/-- **Table `254` conserves no sliding block code but zero**: it is left-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f254 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f254 hq254 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_leftForcing f254 hq254 (by decide) g hg hcons

/-- **Table `186` conserves no sliding block code but zero**: it is right-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f186 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f186 hq186 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_rightForcing f186 hq186 (by decide) g hg hcons

/-- **Table `190` conserves no sliding block code but zero**: it is right-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f190 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f190 hq190 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_rightForcing f190 hq190 (by decide) g hg hcons

/-- **Table `234` conserves no sliding block code but zero**: it is right-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f234 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f234 hq234 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_rightForcing f234 hq234 (by decide) g hg hcons

/-- **Table `238` conserves no sliding block code but zero**: it is right-forcing, so a code of
any window that a step leaves unchanged is the zero code. -/
theorem blockCode_eq_zero_f238 {L : ℕ} (g : (Fin L → ZMod 2) → ZMod 2) (hg : g 0 = 0)
    (hcons : ∀ s : FiniteConfiguration,
      FiniteConfiguration.blockCode L g hg (LocalRule.finRule f238 hq238 s) =
        FiniteConfiguration.blockCode L g hg s) :
    g = 0 :=
  LocalRule.blockCode_eq_zero_of_rightForcing f238 hq238 (by decide) g hg hcons

end ECA
