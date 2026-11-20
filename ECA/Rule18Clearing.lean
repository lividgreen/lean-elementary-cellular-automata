module

public import ECA.ConservedCodeTransfer
public import ECA.ParityEmulation
public import ECA.KinkMonotone
public import ErgodicTheory.Rule18Annihilation
public import ErgodicTheory.Rule18Lift

/-!
# Rule `18` clears windows under Jen's kink annihilation

`ECA.ConservedCodeTransfer` takes the clearing of windows by rule `18` as a named hypothesis.
This module reduces that hypothesis to Jen's kink annihilation (Jen 1990, as Sabrié and Törmä
2023, §4 state it), `Rule18Kinks.JenAnnihilation`, the classical statement it leaves named: a
finitely supported configuration has, after some number of steps of rule `18`, at most one kink.

Given the cells of a finite configuration on an interval, extend them by one set cell to the right
of the interval, at one of the two nearest cells whose distance from the first set cell is even,
so that the kink count of the extension is even. The kink count keeps its parity under rule `18`
(`Rule18Kinks.kinks_step_rule18_mod_two`), so Jen's theorem leaves the extension, after some
steps, with no kink, hence of one parity (`FiniteConfiguration.kinkCount_eq_zero_iff`). Over the
states of one parity rule `18` follows rule `90` and doubles
(`FiniteConfiguration.OneParity.iterate_two_pow_add`): after a power of two of steps, beyond the
spread of the support around the interval, the interval reads zeros.

## Main results

* `clearsWindows_f18_of_jenAnnihilation` — Jen's kink annihilation gives that rule `18` clears
  windows.
* `conservesNoCode_f18_f146_f126_of_jenAnnihilation` — and so rules `18`, `146` and `126` conserve
  no sliding block code but zero (`conservesNoCode_f18_f146_f126`), with Jen's kink annihilation as
  the one hypothesis.
* `clearsWindows_f18` — rule `18` clears windows, with no hypothesis: the classical proof of Jen's
  kink annihilation, `Rule18Kinks.jenAnnihilation`, discharges the hypothesis.
* `conservesNoCode_f18_f146_f126'` — rules `18`, `146` and `126` conserve no sliding block code but
  zero, with no hypothesis.
-/

@[expose] public section

namespace ECA

open FiniteConfiguration LocalRule

/-- One step of the table `f18` on a finite configuration is one step of rule `18` on the
configuration, read as a function of the line. -/
private theorem coe_finRule_f18 (s : FiniteConfiguration) :
    ⇑(finRule f18 hq18 s) = LocalRuleColumns.step Rule18Kinks.rule18 ⇑s :=
  funext fun i => finRule_apply f18 hq18 s i

/-- A finite configuration has finitely many set cells, as a function of the line. -/
private theorem finite_support_coe (z : FiniteConfiguration) : (Function.support ⇑z).Finite :=
  z.support.finite_toSet.subset fun _ hi => Finsupp.mem_support_iff.mpr hi

/-- The parity of the kink count is kept along the orbit of rule `18`. -/
private theorem kinkCount_iterate_f18_mod_two (z : FiniteConfiguration) (n : ℕ) :
    kinkCount ((finRule f18 hq18)^[n] z) % 2 = kinkCount z % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', kinkCount_eq_kinks, coe_finRule_f18,
      Rule18Kinks.kinks_step_rule18_mod_two _ (finite_support_coe _), ← kinkCount_eq_kinks]
    exact ih

/-- The cells of a finite configuration on an interval extend to a finite configuration with an
even kink count. -/
private theorem exists_even_kinks_extension (a b : ℤ) (x : FiniteConfiguration) :
    ∃ z : FiniteConfiguration, (∀ i, a ≤ i → i ≤ b → z i = x i) ∧ kinkCount z % 2 = 0 := by
  set z₀ : FiniteConfiguration := x.filter (fun i => a ≤ i ∧ i ≤ b) with hz₀
  have hz₀a : ∀ i, z₀ i ≠ 0 → a ≤ i ∧ i ≤ b := by
    intro i hi
    by_contra h
    exact hi (Finsupp.filter_apply_neg _ _ h)
  have hz₀x : ∀ i, a ≤ i → i ≤ b → z₀ i = x i := fun i h1 h2 =>
    Finsupp.filter_apply_pos _ _ ⟨h1, h2⟩
  by_cases h0 : z₀ = 0
  · refine ⟨z₀, hz₀x, ?_⟩
    rw [h0]
    unfold kinkCount
    simp
  · have hne : z₀.support.Nonempty := Finsupp.support_nonempty_iff.mpr h0
    set a₀ := z₀.support.min' hne with ha₀
    have ha₀z : z₀ a₀ ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hne)
    have ha₀b := hz₀a a₀ ha₀z
    obtain ⟨e, he, hpar⟩ : ∃ e : ℤ, b < e ∧ (e - a₀) % 2 = 0 := by
      by_cases h : (b + 1 - a₀) % 2 = 0
      · exact ⟨b + 1, by omega, h⟩
      · exact ⟨b + 2, by omega, by omega⟩
    have hsingle : ∀ i, i ≠ e → (Finsupp.single e (1 : ZMod 2)) i = 0 := fun i hi => by
      rw [Finsupp.single_apply]
      exact ite_eq_right_iff.mpr fun h => absurd h.symm hi
    have hze : z₀ e = 0 := by
      by_contra h
      have := (hz₀a e h).2
      omega
    obtain ⟨z, hzdef⟩ : ∃ z : FiniteConfiguration, z = z₀ + Finsupp.single e 1 := ⟨_, rfl⟩
    have hza : ∀ i, z i = z₀ i + Finsupp.single e (1 : ZMod 2) i := fun i => by
      rw [hzdef, Finsupp.add_apply]
    refine ⟨z, fun i h1 h2 => ?_, ?_⟩
    · rw [hza, hsingle i (by omega), add_zero, hz₀x i h1 h2]
    · rw [kinkCount_eq_kinks]
      have hlo : ∀ i, z i ≠ 0 → a₀ ≤ i := by
        intro i hi
        by_cases hie : i = e
        · omega
        · rw [hza, hsingle i hie, add_zero] at hi
          exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hi)
      have hhi : ∀ i, z i ≠ 0 → i ≤ e := by
        intro i hi
        by_cases hie : i = e
        · omega
        · rw [hza, hsingle i hie, add_zero] at hi
          have := (hz₀a i hi).2
          omega
      have h1 := Rule18Kinks.kinks_mod_two_of_extremes ⇑z (finite_support_coe _) a₀ e
        (by rw [hza, hsingle a₀ (by omega), add_zero]; exact ha₀z)
        (by rw [hza, hze, Finsupp.single_eq_same, zero_add]; decide)
        hlo hhi
      omega

/-- Under Jen's kink annihilation, a finite configuration with an even kink count reaches a
configuration of one parity along the orbit of rule `18`. -/
private theorem exists_oneParity_iterate_f18 (h : Rule18Kinks.JenAnnihilation)
    (z : FiniteConfiguration) (hz : kinkCount z % 2 = 0) :
    ∃ n, OneParity ((finRule f18 hq18)^[n] z) := by
  obtain ⟨n, hn⟩ := h ⇑z (finite_support_coe z)
  refine ⟨n, (kinkCount_eq_zero_iff _).1 ?_⟩
  have e : ⇑((finRule f18 hq18)^[n] z) = (LocalRuleColumns.step Rule18Kinks.rule18)^[n] ⇑z :=
    coe_finRule_iterate f18 hq18 n z
  have h1 : kinkCount ((finRule f18 hq18)^[n] z) ≤ 1 := by
    rw [kinkCount_eq_kinks, e]
    exact hn
  have h2 := kinkCount_iterate_f18_mod_two z n
  omega

/-- A state of one parity has its interval cleared by rule `18` after a power of two of steps. -/
private theorem exists_zero_window_f18 (s : FiniteConfiguration) (hs : OneParity s) (a b : ℤ) :
    ∃ M : ℕ, ∀ i, a ≤ i → i ≤ b → (finRule f18 hq18)^[2 ^ M] s i = 0 := by
  set B : ℕ := s.support.sup (fun i => i.natAbs) with hB
  have hBs : ∀ j, s j ≠ 0 → j.natAbs ≤ B := fun j hj =>
    Finset.le_sup (f := fun i : ℤ => i.natAbs) (Finsupp.mem_support_iff.mpr hj)
  refine ⟨B + a.natAbs + b.natAbs, fun i hi1 hi2 => ?_⟩
  have hlt : B + a.natAbs + b.natAbs < 2 ^ (B + a.natAbs + b.natAbs) := Nat.lt_two_pow_self
  generalize hMdef : B + a.natAbs + b.natAbs = M at hlt ⊢
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = 2 ^ M := ⟨_, rfl⟩
  have hP : (2 : ℤ) ^ M = P := by rw [hPdef]; push_cast; rfl
  rw [← hPdef] at hlt
  have e : (finRule f18 hq18)^[2 ^ M + 0] s i =
      ((finRule f18 hq18)^[0] s) (i - 2 ^ M) + ((finRule f18 hq18)^[0] s) (i + 2 ^ M) :=
    FiniteConfiguration.OneParity.iterate_two_pow_add f18 agreesOffAdjacent_f18 s hs M 0 i
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

/-- **Jen's kink annihilation gives that rule `18` clears windows**: the cells of a finite
configuration on an interval extend to a finite configuration with an even kink count, which Jen's
theorem and the parity of the kinks bring to one parity, where the doubling of rule `90` clears
the interval. -/
theorem clearsWindows_f18_of_jenAnnihilation (h : Rule18Kinks.JenAnnihilation) :
    LocalRule.ClearsWindows f18 hq18 := by
  intro a b x
  obtain ⟨z, hz, hev⟩ := exists_even_kinks_extension a b x
  obtain ⟨n, hn⟩ := exists_oneParity_iterate_f18 h z hev
  obtain ⟨M, hM⟩ := exists_zero_window_f18 _ hn a b
  refine ⟨z, hz, 2 ^ M + n, fun i hi1 hi2 => ?_⟩
  rw [Function.iterate_add_apply]
  exact hM i hi1 hi2

/-- **Rules `18`, `146` and `126` conserve no sliding block code but zero**, under Jen's kink
annihilation. -/
theorem conservesNoCode_f18_f146_f126_of_jenAnnihilation (h : Rule18Kinks.JenAnnihilation) :
    LocalRule.ConservesNoCode f18 hq18 ∧ LocalRule.ConservesNoCode f146 hq146 ∧
      LocalRule.ConservesNoCode f126 hq126 :=
  conservesNoCode_f18_f146_f126 (clearsWindows_f18_of_jenAnnihilation h)

/-- **Rule `18` clears every window**, with no hypothesis: the classical theorem
`Rule18Kinks.jenAnnihilation`, Jen's kink annihilation for rule `18`, is the hypothesis of
`clearsWindows_f18_of_jenAnnihilation`. -/
theorem clearsWindows_f18 : LocalRule.ClearsWindows f18 hq18 :=
  clearsWindows_f18_of_jenAnnihilation Rule18Kinks.jenAnnihilation

/-- **Rules `18`, `146` and `126` conserve no sliding block code but zero**, with no hypothesis:
`conservesNoCode_f18_f146_f126_of_jenAnnihilation` applied to the classical theorem
`Rule18Kinks.jenAnnihilation`. -/
theorem conservesNoCode_f18_f146_f126' :
    LocalRule.ConservesNoCode f18 hq18 ∧ LocalRule.ConservesNoCode f146 hq146 ∧
      LocalRule.ConservesNoCode f126 hq126 :=
  conservesNoCode_f18_f146_f126_of_jenAnnihilation Rule18Kinks.jenAnnihilation

/-- info:
'ECA.clearsWindows_f18_of_jenAnnihilation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.clearsWindows_f18_of_jenAnnihilation

/-- info:
'ECA.conservesNoCode_f18_f146_f126_of_jenAnnihilation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f18_f146_f126_of_jenAnnihilation

/-- info:
'ECA.clearsWindows_f18' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.clearsWindows_f18

/-- info:
'ECA.conservesNoCode_f18_f146_f126'' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.conservesNoCode_f18_f146_f126'

end ECA
