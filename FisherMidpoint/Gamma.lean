module
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

/-! # The gamma Laplace transform and its exact domain -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
namespace FisherMidpoint

private theorem gamma_mass {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, gammaPDFReal a r x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (gammaPDFReal_nonneg ha hr))
    (measurable_gammaPDFReal a r).aestronglyMeasurable]
  change (∫⁻ x, gammaPDF a r x).toReal = 1
  rw [lintegral_gammaPDF_eq_one ha hr, ENNReal.toReal_one]

private theorem gamma_meas (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

private theorem gamma_toReal {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    (gammaPDF a r x).toReal = gammaPDFReal a r x :=
  ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)

theorem gamma_mgf {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    mgf id (gammaMeasure a r) t = (r/(r-t))^a := by
  have hrt := sub_pos.mpr ht
  have density (x : ℝ) : gammaPDFReal a r x * exp (t*x) =
      (r/(r-t))^a * gammaPDFReal a (r-t) x := by
    by_cases hx : 0 ≤ x
    · simp only [gammaPDFReal,ite_eq_left hx, div_rpow hr.le hrt.le]
      rw [mul_assoc,← exp_add,show -(r*x)+t*x = -((r-t)*x) by ring]
      field_simp [(rpow_pos_of_pos hrt a).ne']
    · simp [gammaPDFReal,hx]
  rw [mgf,gammaMeasure, integral_withDensity_eq_integral_toReal_smul (gamma_meas a r)
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top)) _]
  simp_rw [id_eq,smul_eq_mul,gamma_toReal ha hr,density]
  rw [integral_const_mul,gamma_mass ha hrt,mul_one]

theorem gamma_domain {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ exp (t*x)) (gammaMeasure a r) ↔ t < r := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  refine ⟨fun hint ↦ ?_,fun ht ↦ (mgf_pos_iff (X := id)).mp (by
    rw [gamma_mgf ha hr ht]; positivity)⟩
  by_contra! hrt
  rw [gammaMeasure,integrable_withDensity_iff_integrable_smul' (gamma_meas a r)
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))] at hint
  simp_rw [smul_eq_mul,gamma_toReal ha hr] at hint
  let c := r^a / Gamma a
  have hc : 0 < c := div_pos (rpow_pos_of_pos hr _) (Gamma_pos_of_pos ha)
  have hmono : IntegrableOn (fun x : ℝ ↦ c * x^(a-1)) (Ioi 1) := by
    apply hint.integrableOn.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := by change 1 < x at hx; linarith
    have hpos := rpow_nonneg hx0 (a-1)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le hpos)]
    simp only [gammaPDFReal,ite_eq_left hx0, mul_assoc, ←exp_add]
    change c * x ^ (a-1) ≤ c * (x ^ (a-1) * exp _)
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hpos
      (one_le_exp (by nlinarith [mul_nonneg (sub_nonneg.mpr hrt) hx0]))) hc.le
  have hrpow : IntegrableOn (fun x : ℝ ↦ x^(a-1)) (Ioi 1) := by
    simpa [IntegrableOn,←mul_assoc,hc.ne'] using hmono.const_mul c⁻¹
  have bad := (integrableOn_Ioi_rpow_iff zero_lt_one).mp hrpow
  linarith

end FisherMidpoint
