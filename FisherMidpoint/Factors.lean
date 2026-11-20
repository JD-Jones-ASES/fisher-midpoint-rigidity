module
public import FisherMidpoint.Gamma
public import FisherMidpoint.Laplace
public import Mathlib.MeasureTheory.Measure.Tilted

/-! # Independent Gaussian and gamma coordinates and exponential tilting -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology
namespace FisherMidpoint

/-- Log-partition of the unit-variance centered coordinate in affine natural parameter. -/
def axisCGF (l u : ℝ) : ℝ := if l = 0 then u^2/2 else u/l - log (1+l*u)/l^2

/-- The Gaussian axis has mean `u`. A nonzero axis is a fixed invertible affine
image of a gamma variable of shape `1/l²` and rate `1+l*u`. -/
def factor (l u : ℝ) : Measure ℝ :=
  if l = 0 then gaussianReal u 1 else
    (gammaMeasure (1/l^2) (1+l*u)).map (fun y : ℝ ↦ 1/l + (-l)*y)

theorem factor_probability (l u : ℝ) (h : 0 < 1+l*u) : IsProbabilityMeasure (factor l u) := by
  by_cases hl : l = 0
  · simp [factor,hl]; infer_instance
  · rw [factor,ite_eq_right hl]
    let := isProbabilityMeasure_gammaMeasure (show 0 < 1/l^2 by positivity) h
    constructor
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,Set.preimage_univ,measure_univ]

private theorem gamma_affine_mgf {l u t : ℝ} (hl : l ≠ 0) :
    mgf id (factor l u) t = exp (t*(1/l)) * mgf id (gammaMeasure (1/l^2) (1+l*u)) ((-l)*t) := by
  rw [factor,ite_eq_right hl,mgf_id_map (by fun_prop),mgf_const_add]
  exact congrArg (_ * ·) (mgf_const_mul (X := id) (-l))

theorem factor_mgf {l u t : ℝ} (hu : 0 < 1+l*u) (ht : 0 < 1+l*(u+t)) :
    mgf id (factor l u) t = exp (axisCGF l (u+t)-axisCGF l u) := by
  by_cases hl : l = 0
  · subst l; simp [factor,mgf_id_gaussianReal,axisCGF]; ring_nf
  rw [gamma_affine_mgf hl,gamma_mgf (by positivity) hu (by linarith)]
  rw [show 1+l*u - -l*t = 1+l*(u+t) by ring,
    Real.rpow_def_of_pos (div_pos hu ht), ← exp_add, log_div hu.ne' ht.ne']
  simp only [axisCGF, ite_eq_right hl]
  congr 1
  ring

theorem factor_domain {l u t : ℝ} (hu : 0 < 1+l*u) :
    Integrable (fun x : ℝ ↦ exp (t*x)) (factor l u) ↔ 0 < 1+l*(u+t) := by
  let := factor_probability l u hu
  change Integrable (fun x ↦ exp (t*id x)) (factor l u) ↔ _
  rw [← mgf_pos_iff (X := id)]
  refine ⟨fun h ↦ ?_,fun ht ↦ (factor_mgf hu ht) ▸ exp_pos _⟩
  by_cases hl : l = 0
  · simp [hl]
  · have ha : 0 < 1/l^2 := by positivity
    let := isProbabilityMeasure_gammaMeasure ha hu
    rw [gamma_affine_mgf hl] at h
    have pos := (mul_pos_iff_of_pos_left (exp_pos _)).mp h
    have hdom := (gamma_domain ha hu).mp ((mgf_pos_iff (X := id)).mp pos)
    linarith

variable {ι : Type*} [Fintype ι]

def productLaw (l u : ι → ℝ) : Measure (ι → ℝ) := Measure.pi (fun i ↦ factor (l i) (u i))

def admissible (l u : ι → ℝ) : Prop := ∀ i, 0 < 1 + l i * u i

def pairing (v x : ι → ℝ) : ℝ := ∑ i, v i * x i

theorem product_probability {l u : ι → ℝ} (hu : admissible l u) :
    IsProbabilityMeasure (productLaw l u) := by
  let _ (i : ι) := factor_probability (l i) (u i) (hu i)
  unfold productLaw; infer_instance

theorem product_integral {l u : ι → ℝ} (hu : admissible l u) (v : ι → ℝ) :
    ∫ x, exp (pairing v x) ∂productLaw l u = ∏ i, mgf id (factor (l i) (u i)) (v i) := by
  let _ (i : ι) := factor_probability (l i) (u i) (hu i)
  simp only [pairing,Real.exp_sum,productLaw,mgf,id_eq]
  exact integral_fintype_prod_eq_prod (μ := fun i ↦ factor (l i) (u i)) (fun i (x : ℝ) ↦ exp (v i*x))

theorem product_laplace {l u v : ι → ℝ} (hu : admissible l u) (hv : admissible l (u+v)) :
    ∫ x, exp (pairing v x) ∂productLaw l u = exp (∑ i, (axisCGF (l i) (u i+v i)-axisCGF (l i) (u i))) := by
  rw [product_integral hu,Real.exp_sum]
  exact Finset.prod_congr rfl (fun i _ ↦ factor_mgf (hu i) (hv i))

theorem product_domain {l u : ι → ℝ} (hu : admissible l u) (v : ι → ℝ) :
    Integrable (fun x ↦ exp (pairing v x)) (productLaw l u) ↔ admissible l (u+v) := by
  let := product_probability hu
  have eqn : mgf (pairing v) (productLaw l u) 1 = ∏ i, mgf id (factor (l i) (u i)) (v i) := by
    simp [mgf,product_integral hu]
  have iff' := mgf_pos_iff (μ := productLaw l u) (X := pairing v) (t := 1)
  simp only [one_mul] at iff'
  rw [←iff',eqn]
  constructor
  · intro h i
    have hi := (Finset.prod_ne_zero_iff.mp h.ne' i (Finset.mem_univ _))
    have pos := lt_of_le_of_ne mgf_nonneg hi.symm
    let := factor_probability (l i) (u i) (hu i)
    exact (factor_domain (hu i)).mp ((mgf_pos_iff (X := id)).mp pos)
  · intro h
    exact Finset.prod_pos fun i _ ↦ (factor_mgf (hu i) (h i)) ▸ exp_pos _

end FisherMidpoint
