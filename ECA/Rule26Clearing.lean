module

public import ECA.ConservedCodeTransfer
public import ECA.ParityEmulation
public import ECA.ReproductionBracket

/-!
# Rules `26` and `82` clear windows from a held suffix of one parity

A quiescent table clears windows when the cells of any finite configuration on an interval extend
to a finite configuration whose orbit reads zeros there (the predicate
`LocalRule.ClearsWindows`), and a table that clears windows conserves no sliding block
code but zero (`LocalRule.ClearsWindows.conservesNoCode`).
Rule `26` agrees with rule `90` off the neighbourhood `110`, and rule `82` is rule `26` read in a
mirror, `f82 a b c = f26 c b a`.

The hypothesis taken here, `LocalRule.EventuallyOneParitySuffix`, is that every finite
configuration reaches, after some steps of the table, a state whose part from some cell on is of
one parity and whose orbit agrees, from then on, with that part's own orbit on every cell the
part's left end can reach moving left at one cell a step.
Over a part of one parity a table that agrees with rule `90` off adjacent cells follows rule `90`
and doubles (`FiniteConfiguration.OneParity.iterate_two_pow_add`), so after a power of two of
further steps, beyond the spread of the part and of the window, the window reads zeros
(`LocalRule.exists_iterate_zero_of_oneParitySuffix`).
Clearing is invariant under reflecting the line (`LocalRule.ClearsWindows.mirror`), which carries
it from rule `26` to rule `82`.

## Main results

* `LocalRule.EventuallyOneParitySuffix` — the hypothesis.
* `LocalRule.exists_iterate_zero_of_oneParitySuffix` — a held suffix of one parity clears any
  window at one configuration, and `LocalRule.exists_iterate_zero_of_oneParitySuffix_nonvacuous`
  shows its three hypotheses hold together.
* `LocalRule.ClearsWindows.mirror` and `f82_eq_mirror_f26` — clearing passes from rule `26` to
  rule `82`.
* `clearsWindows_f26_of_eventuallyOneParitySuffix` and
  `clearsWindows_f82_of_eventuallyOneParitySuffix` — the hypothesis gives that rules `26` and `82`
  clear windows.
* `conservesNoCode_f26_f82_of_eventuallyOneParitySuffix` — and so rules `26` and `82` conserve no
  sliding block code but zero, with the hypothesis as the one condition.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- Every finite configuration reaches, after some steps of the table, a state whose part from some
cell on is of one parity and whose orbit agrees, from then on, with that part's own orbit on every
cell the part's left end can reach moving left at one cell a step. -/
def LocalRule.EventuallyOneParitySuffix (f : LocalRule) (hq : f 0 0 0 = 0) : Prop :=
  ∀ z : FiniteConfiguration, ∃ (n : ℕ) (q : ℤ),
    OneParity (((finRule f hq)^[n] z).filter (fun i => q ≤ i)) ∧
      ∀ (m : ℕ) (i : ℤ), q - m ≤ i →
        ((finRule f hq)^[n + m] z) i =
          ((finRule f hq)^[m] (((finRule f hq)^[n] z).filter (fun i => q ≤ i))) i

/-! ## A held suffix of one parity clears a window -/

/-- **A held suffix of one parity clears any window.** Where a table agrees with rule `90` off
adjacent cells, a finite configuration whose part from the cell `q` on is of one parity after `n`
steps, and whose orbit agrees with that part's own orbit on every cell from `q - m` on at `m`
further steps, reads zeros on any interval at some time: after a power of two of further steps,
beyond the spread of the part and of the interval around `q`, the doubling of rule `90` over one
parity leaves two translated copies of the part, both away from the interval. -/
theorem LocalRule.exists_iterate_zero_of_oneParitySuffix (f : LocalRule)
    (h : AgreesOffAdjacent f) (z : FiniteConfiguration) (n : ℕ) (q : ℤ)
    (hone : OneParity (((finRule f h.1)^[n] z).filter (fun i => q ≤ i)))
    (hheld : ∀ (m : ℕ) (i : ℤ), q - m ≤ i →
      ((finRule f h.1)^[n + m] z) i =
        ((finRule f h.1)^[m] (((finRule f h.1)^[n] z).filter (fun i => q ≤ i))) i)
    (a b : ℤ) :
    ∃ k : ℕ, ∀ i, a ≤ i → i ≤ b → ((finRule f h.1)^[k] z) i = 0 := by
  set s : FiniteConfiguration := ((finRule f h.1)^[n] z).filter (fun i => q ≤ i) with hs
  set B : ℕ := s.support.sup (fun i => i.natAbs) with hB
  have hBs : ∀ j, s j ≠ 0 → j.natAbs ≤ B := fun j hj =>
    Finset.le_sup (f := fun i : ℤ => i.natAbs) (Finsupp.mem_support_iff.mpr hj)
  refine ⟨n + 2 ^ (B + a.natAbs + b.natAbs + q.natAbs), fun i hi1 hi2 => ?_⟩
  have hlt : B + a.natAbs + b.natAbs + q.natAbs <
      2 ^ (B + a.natAbs + b.natAbs + q.natAbs) := Nat.lt_two_pow_self
  generalize hMdef : B + a.natAbs + b.natAbs + q.natAbs = M at hlt ⊢
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = 2 ^ M := ⟨_, rfl⟩
  have hP : (2 : ℤ) ^ M = P := by rw [hPdef]; push_cast; rfl
  rw [← hPdef] at hlt ⊢
  have hq : q - ((P : ℕ) : ℤ) ≤ i := by omega
  rw [hheld P i hq, hPdef]
  have e : (finRule f h.1)^[2 ^ M + 0] s i =
      ((finRule f h.1)^[0] s) (i - 2 ^ M) + ((finRule f h.1)^[0] s) (i + 2 ^ M) :=
    FiniteConfiguration.OneParity.iterate_two_pow_add f h s hone M 0 i
  rw [Nat.add_zero] at e
  rw [e, Function.iterate_zero, id_eq]
  have hl : s (i - 2 ^ M) = 0 := by
    by_contra hc
    have := hBs _ hc
    rw [hP] at this
    omega
  have hr : s (i + 2 ^ M) = 0 := by
    by_contra hc
    have := hBs _ hc
    rw [hP] at this
    omega
  rw [hl, hr, add_zero]

/-- The three hypotheses of `LocalRule.exists_iterate_zero_of_oneParitySuffix` hold together: rule
`90` meets the agreement, and the configuration with one set cell, at no step and from the cell
`0` on, is its own part of one parity, which its orbit follows. -/
theorem LocalRule.exists_iterate_zero_of_oneParitySuffix_nonvacuous :
    ∃ h : AgreesOffAdjacent f90,
      OneParity (((finRule f90 h.1)^[0] (Finsupp.single (0 : ℤ) (1 : ZMod 2))).filter
          (fun i => (0 : ℤ) ≤ i)) ∧
        ∀ (m : ℕ) (i : ℤ), (0 : ℤ) - m ≤ i →
          ((finRule f90 h.1)^[0 + m] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i =
            ((finRule f90 h.1)^[m] (((finRule f90 h.1)^[0]
              (Finsupp.single (0 : ℤ) (1 : ZMod 2))).filter (fun i => (0 : ℤ) ≤ i))) i := by
  have hfilt : (Finsupp.single (0 : ℤ) (1 : ZMod 2)).filter (fun i => (0 : ℤ) ≤ i) =
      Finsupp.single (0 : ℤ) (1 : ZMod 2) := by
    rw [Finsupp.filter_eq_self_iff]
    intro i hi
    have := (Finsupp.single_apply_ne_zero.1 hi).1
    omega
  refine ⟨agreesOffAdjacent_f90, ?_, ?_⟩
  · rw [Function.iterate_zero, id_eq, hfilt]
    intro i j hi hj
    have hi' := (Finsupp.single_apply_ne_zero.1 hi).1
    have hj' := (Finsupp.single_apply_ne_zero.1 hj).1
    rw [hi', hj', sub_self]
    exact ⟨0, by simp⟩
  · intro m i _
    rw [Function.iterate_zero, id_eq, hfilt, zero_add]

/-! ## Clearing under the reflection of the line -/

/-- The configuration read backwards: the cell `i` holds what the cell `-i` held. -/
private noncomputable def reflect (s : FiniteConfiguration) : FiniteConfiguration :=
  Finsupp.equivMapDomain (Equiv.neg ℤ) s

private theorem reflect_apply (s : FiniteConfiguration) (i : ℤ) : reflect s i = s (-i) := by
  simp [reflect, Finsupp.equivMapDomain_apply]

private theorem finRule_mirror_reflect (f : LocalRule) (hq : f 0 0 0 = 0)
    (s : FiniteConfiguration) :
    finRule (fun a b c => f c b a) hq (reflect s) = reflect (finRule f hq s) := by
  ext i
  rw [finRule_apply]
  simp only [reflect_apply]
  rw [finRule_apply, show -(i - 1) = -i + 1 by ring, show -(i + 1) = -i - 1 by ring]

private theorem iterate_finRule_mirror_reflect (f : LocalRule) (hq : f 0 0 0 = 0)
    (s : FiniteConfiguration) (t : ℕ) :
    (finRule (fun a b c => f c b a) hq)^[t] (reflect s) = reflect ((finRule f hq)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      finRule_mirror_reflect]

/-- **Clearing windows is invariant under the mirror**: a table that clears windows has its mirror,
the table `fun a b c => f c b a`, clear windows, by reflecting the line and the interval. -/
theorem LocalRule.ClearsWindows.mirror {f : LocalRule} {hq : f 0 0 0 = 0}
    (h : f.ClearsWindows hq) : LocalRule.ClearsWindows (fun a b c => f c b a) hq := by
  intro a b x
  obtain ⟨z, hz, k, hk⟩ := h (-b) (-a) (reflect x)
  refine ⟨reflect z, fun i hi1 hi2 => ?_, k, fun i hi1 hi2 => ?_⟩
  · rw [reflect_apply]
    have := hz (-i) (by omega) (by omega)
    rw [reflect_apply, neg_neg] at this
    exact this
  · rw [iterate_finRule_mirror_reflect, reflect_apply]
    exact hk (-i) (by omega) (by omega)

/-- Rule `82` is rule `26` read in a mirror. -/
theorem f82_eq_mirror_f26 : f82 = fun a b c => f26 c b a := by
  funext a b c
  revert a b c
  unfold f82 f26
  decide

private theorem clearsWindows_congr {f g : LocalRule} {hf : f 0 0 0 = 0} {hg : g 0 0 0 = 0}
    (e : f = g) (h : f.ClearsWindows hf) : g.ClearsWindows hg := by
  subst e
  exact h

private theorem agreesOffAdjacent_f26' : AgreesOffAdjacent f26 := by
  unfold AgreesOffAdjacent f26; decide

/-! ## Rules `26` and `82` -/

/-- **The held suffix of one parity gives that rule `26` clears windows**: the cells of a finite
configuration on an interval extend, by zeros, to a finite configuration that reaches a held
suffix of one parity, from which the window reads zeros after a power of two of further steps. -/
theorem clearsWindows_f26_of_eventuallyOneParitySuffix
    (h : LocalRule.EventuallyOneParitySuffix f26 hq26) : LocalRule.ClearsWindows f26 hq26 := by
  intro a b x
  set z : FiniteConfiguration := x.filter (fun i => a ≤ i ∧ i ≤ b) with hz
  obtain ⟨n, q, hone, hheld⟩ := h z
  obtain ⟨k, hk⟩ := LocalRule.exists_iterate_zero_of_oneParitySuffix f26 agreesOffAdjacent_f26' z
    n q hone hheld a b
  exact ⟨z, fun i h1 h2 => Finsupp.filter_apply_pos _ _ ⟨h1, h2⟩, k, hk⟩

/-- **The held suffix of one parity gives that rule `82` clears windows**: rule `82` is rule `26`
read in a mirror, and clearing windows passes to the mirror. -/
theorem clearsWindows_f82_of_eventuallyOneParitySuffix
    (h : LocalRule.EventuallyOneParitySuffix f26 hq26) : LocalRule.ClearsWindows f82 hq82 :=
  clearsWindows_congr f82_eq_mirror_f26.symm
    (clearsWindows_f26_of_eventuallyOneParitySuffix h).mirror

/-- **Rules `26` and `82` conserve no sliding block code but zero**, with the held suffix of one
parity at rule `26` as the one hypothesis: a table that clears windows conserves no such code
(`LocalRule.ClearsWindows.conservesNoCode`). -/
theorem conservesNoCode_f26_f82_of_eventuallyOneParitySuffix
    (h : LocalRule.EventuallyOneParitySuffix f26 hq26) :
    LocalRule.ConservesNoCode f26 hq26 ∧ LocalRule.ConservesNoCode f82 hq82 :=
  ⟨(clearsWindows_f26_of_eventuallyOneParitySuffix h).conservesNoCode,
    (clearsWindows_f82_of_eventuallyOneParitySuffix h).conservesNoCode⟩

/-- info:
'ECA.LocalRule.exists_iterate_zero_of_oneParitySuffix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.LocalRule.exists_iterate_zero_of_oneParitySuffix

/-- info:
'ECA.clearsWindows_f26_of_eventuallyOneParitySuffix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.clearsWindows_f26_of_eventuallyOneParitySuffix

/-- info:
'ECA.clearsWindows_f82_of_eventuallyOneParitySuffix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.clearsWindows_f82_of_eventuallyOneParitySuffix

/-- info:
'ECA.conservesNoCode_f26_f82_of_eventuallyOneParitySuffix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f26_f82_of_eventuallyOneParitySuffix

end ECA
