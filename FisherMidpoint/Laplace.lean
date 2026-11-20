module
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Uniqueness of the law from locally equal Laplace transforms -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped Topology

namespace FisherMidpoint

/-- Local exponential moments of each real projection suffice on a real Banach space. -/
theorem law_of_local_mgf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ L : StrongDual ℝ E, ∀ᶠ t : ℝ in 𝓝 0,
      t ∈ integrableExpSet L μ ∧ t ∈ integrableExpSet L ν ∧ mgf L μ t = mgf L ν t) :
    μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  let U := interior (integrableExpSet L μ) ∩ interior (integrableExpSet L ν)
  have h0 : (0:ℝ) ∈ U :=
    ⟨mem_interior_iff_mem_nhds.mpr ((h L).mono fun _ ht ↦ ht.1),
      mem_interior_iff_mem_nhds.mpr ((h L).mono fun _ ht ↦ ht.2.1)⟩
  have hX : AnalyticOnNhd ℂ (complexMGF L μ) {z : ℂ | z.re ∈ U} :=
    analyticOnNhd_complexMGF.mono (fun _ hx ↦ hx.1)
  have hY : AnalyticOnNhd ℂ (complexMGF L ν) {z : ℂ | z.re ∈ U} :=
    analyticOnNhd_complexMGF.mono (fun _ hx ↦ hx.2)
  have eqn : EqOn (complexMGF L μ) (complexMGF L ν) {z : ℂ | z.re ∈ U} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY
      ((convex_integrableExpSet.interior.inter convex_integrableExpSet.interior).linear_preimage reLm).isPreconnected
      (z₀ := 0) (by simpa using h0) ?_
    have hreal : ∃ᶠ t : ℝ in 𝓝[≠] 0, complexMGF L μ t = complexMGF L ν t := by
      apply Filter.Eventually.frequently
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (h L)] with t ht
      rw [complexMGF_ofReal, complexMGF_ofReal, ht.2.2]
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨s,hs,hv⟩ := hreal
    refine ⟨fun n ↦ (s n : ℂ), ?_, hv⟩
    rw [tendsto_nhdsWithin_iff] at hs ⊢
    exact ⟨by simpa [Function.comp_def] using (continuous_ofReal.tendsto _).comp hs.1, by simpa using hs.2⟩
  have z := eqn (show I ∈ {z : ℂ | z.re ∈ U} by simpa using h0)
  simpa only [charFunDual_apply, complexMGF, mul_comm I] using z

end FisherMidpoint
