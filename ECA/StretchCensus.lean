module

public import ECA.StretchColumns
public import ECA.StretchCensusData

/-!
# The stretch census: every column eventually periodic at thirty-two tables from sixteen seeds
([RuleSpace] §4 Proposition 4.6)

The decided form of the stretch theorem (`eventuallyPeriodic_observedColumn_of_stretchCheck`)
applies at a list of parameters, and the data module lists, for each of the thirty-two quiescent
tables with a closed form and each of the sixteen nonzero seeds of diameter at most five read from
cell `0`, parameters `(T, P, lo, hi, dL, dR)` at which the check accepts. Two kernel evaluations
decide that every listed certificate is accepted and that every pair has one, and together with
the decided theorem they give the census.

## Main results

* `eventuallyPeriodic_observedColumn_stretchCensus` — **the census**: at each of the thirty-two
  tables and each of the sixteen seeds, every observed column is eventually periodic.
* `length_stretchTables` and `length_smallSeeds` — the sizes of the two lists the census runs over.
-/

@[expose] public section

namespace ECA

open LocalRule

theorem length_stretchTables : stretchTables.length = 32 := by
  decide +kernel

theorem length_smallSeeds : smallSeeds.length = 16 := by
  decide +kernel

/-- The check accepts every certificate of the data module that belongs to the table `N`. -/
private def acceptedAt (N : ℕ) : Bool :=
  (stretchCertificates.filter (fun c => c.1 == N)).all (fun c =>
    stretchCheck (wolframRule c.1) c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1
      c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2)

private theorem acceptedAt_28 : acceptedAt 28 = true := by
  decide +kernel

private theorem acceptedAt_50 : acceptedAt 50 = true := by
  decide +kernel

private theorem acceptedAt_54 : acceptedAt 54 = true := by
  decide +kernel

private theorem acceptedAt_58 : acceptedAt 58 = true := by
  decide +kernel

private theorem acceptedAt_62 : acceptedAt 62 = true := by
  decide +kernel

private theorem acceptedAt_70 : acceptedAt 70 = true := by
  decide +kernel

private theorem acceptedAt_78 : acceptedAt 78 = true := by
  decide +kernel

private theorem acceptedAt_92 : acceptedAt 92 = true := by
  decide +kernel

private theorem acceptedAt_114 : acceptedAt 114 = true := by
  decide +kernel

private theorem acceptedAt_118 : acceptedAt 118 = true := by
  decide +kernel

private theorem acceptedAt_156 : acceptedAt 156 = true := by
  decide +kernel

private theorem acceptedAt_158 : acceptedAt 158 = true := by
  decide +kernel

private theorem acceptedAt_178 : acceptedAt 178 = true := by
  decide +kernel

private theorem acceptedAt_186 : acceptedAt 186 = true := by
  decide +kernel

private theorem acceptedAt_188 : acceptedAt 188 = true := by
  decide +kernel

private theorem acceptedAt_190 : acceptedAt 190 = true := by
  decide +kernel

private theorem acceptedAt_198 : acceptedAt 198 = true := by
  decide +kernel

private theorem acceptedAt_202 : acceptedAt 202 = true := by
  decide +kernel

private theorem acceptedAt_206 : acceptedAt 206 = true := by
  decide +kernel

private theorem acceptedAt_214 : acceptedAt 214 = true := by
  decide +kernel

private theorem acceptedAt_216 : acceptedAt 216 = true := by
  decide +kernel

private theorem acceptedAt_220 : acceptedAt 220 = true := by
  decide +kernel

private theorem acceptedAt_222 : acceptedAt 222 = true := by
  decide +kernel

private theorem acceptedAt_230 : acceptedAt 230 = true := by
  decide +kernel

private theorem acceptedAt_234 : acceptedAt 234 = true := by
  decide +kernel

private theorem acceptedAt_238 : acceptedAt 238 = true := by
  decide +kernel

private theorem acceptedAt_242 : acceptedAt 242 = true := by
  decide +kernel

private theorem acceptedAt_246 : acceptedAt 246 = true := by
  decide +kernel

private theorem acceptedAt_248 : acceptedAt 248 = true := by
  decide +kernel

private theorem acceptedAt_250 : acceptedAt 250 = true := by
  decide +kernel

private theorem acceptedAt_252 : acceptedAt 252 = true := by
  decide +kernel

private theorem acceptedAt_254 : acceptedAt 254 = true := by
  decide +kernel

/-- Every table of the census has all its certificates accepted, one kernel decision per table. -/
private theorem acceptedAt_tables : ∀ N ∈ stretchTables, acceptedAt N = true := by
  intro N hN
  simp only [stretchTables, List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact acceptedAt_28
  · exact acceptedAt_50
  · exact acceptedAt_54
  · exact acceptedAt_58
  · exact acceptedAt_62
  · exact acceptedAt_70
  · exact acceptedAt_78
  · exact acceptedAt_92
  · exact acceptedAt_114
  · exact acceptedAt_118
  · exact acceptedAt_156
  · exact acceptedAt_158
  · exact acceptedAt_178
  · exact acceptedAt_186
  · exact acceptedAt_188
  · exact acceptedAt_190
  · exact acceptedAt_198
  · exact acceptedAt_202
  · exact acceptedAt_206
  · exact acceptedAt_214
  · exact acceptedAt_216
  · exact acceptedAt_220
  · exact acceptedAt_222
  · exact acceptedAt_230
  · exact acceptedAt_234
  · exact acceptedAt_238
  · exact acceptedAt_242
  · exact acceptedAt_246
  · exact acceptedAt_248
  · exact acceptedAt_250
  · exact acceptedAt_252
  · exact acceptedAt_254

/-- Every pair of a table and a seed of the census has a certificate. -/
private theorem stretchCertificates_cover :
    stretchTables.all (fun N => smallSeeds.all (fun s =>
      stretchCertificates.any (fun c => c.1 == N && decide (c.2.1 = s)))) = true := by
  decide +kernel

/-- **Every column is eventually periodic at the thirty-two tables from the sixteen seeds.** Each
pair of a table and a seed has a certificate whose parameters the check accepts, and the decided
theorem turns the acceptance into the eventual periodicity of every observed column. -/
theorem eventuallyPeriodic_observedColumn_stretchCensus :
    ∀ N ∈ stretchTables, ∀ (hq : wolframRule N 0 0 0 = 0), ∀ s ∈ smallSeeds, ∀ i : ℤ,
      DrivenColumns.EventuallyPeriodic
        (observedColumn (finRule (wolframRule N) hq) (listSeed s) i) := by
  intro N hN hq s hs i
  have h1 := List.all_eq_true.mp stretchCertificates_cover N hN
  have h2 := List.all_eq_true.mp h1 s hs
  obtain ⟨⟨N', s', T, P, lo, hi, dL, dR⟩, hc, hmatch⟩ := List.any_eq_true.mp h2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmatch
  obtain ⟨hN', hs'⟩ := hmatch
  subst hN' hs'
  have hacc := List.all_eq_true.mp (acceptedAt_tables N' hN) _
    (List.mem_filter.mpr ⟨hc, by simp⟩)
  exact eventuallyPeriodic_observedColumn_of_stretchCheck _ hq _ T P lo hi dL dR hacc i

end ECA

set_option linter.style.longLine false in
/-- info: 'ECA.eventuallyPeriodic_observedColumn_stretchCensus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECA.eventuallyPeriodic_observedColumn_stretchCensus
