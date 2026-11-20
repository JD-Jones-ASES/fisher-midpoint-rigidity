module
public import FisherMidpoint.Factors

/-! # Local identification determines the maximal tilted family -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology
namespace FisherMidpoint
variable {ι : Type*} [Fintype ι]

def laplace (μ : Measure (ι → ℝ)) (u : ι → ℝ) : ℝ := ∫ x, exp (pairing u x) ∂μ

theorem pairing_smul (t : ℝ) (u x : ι → ℝ) : pairing (t • u) x = t*pairing u x := by
  simp [pairing,Finset.mul_sum,mul_assoc]

theorem pairing_add (u v x : ι → ℝ) : pairing (u+v) x = pairing u x + pairing v x := by
  simp [pairing,add_mul,Finset.sum_add_distrib]

theorem law_of_local_laplace {μ ν : Measure (ι → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ᶠ v in 𝓝 0, 0 < laplace μ v ∧ laplace μ v = laplace ν v) : μ = ν := by
  classical
  apply law_of_local_mgf
  intro L
  let b (i : ι) := L (Pi.single i 1)
  have repr (x : ι → ℝ) : L x = pairing b x := by
    rw [← L.sum_comp_single ℝ (fun _ : ι ↦ ℝ) x]
    unfold pairing
    apply Finset.sum_congr rfl
    intro i _
    have z := (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι ↦ ℝ) i)).map_smul (x i) (1:ℝ)
    simpa [b,smul_eq_mul,mul_comm] using z
  have line (m : Measure (ι → ℝ)) (t : ℝ) : mgf L m t = laplace m (t • b) := by
    simp only [mgf,laplace,pairing_smul,repr]
  have lim : Tendsto (fun t : ℝ ↦ t • b) (𝓝 0) (𝓝 0) := by
    have con : Continuous (fun t : ℝ ↦ t • b) := by fun_prop
    simpa only [zero_smul] using con.tendsto (0:ℝ)
  filter_upwards [lim h] with t ht
  have pos : 0 < mgf L μ t := (line μ t) ▸ ht.1
  have eqn := (line μ t).trans (ht.2.trans (line ν t).symm)
  exact ⟨mgf_pos_iff.mp pos, mgf_pos_iff.mp (eqn ▸ pos),eqn⟩

@[simp] theorem axisCGF_zero (l : ℝ) : axisCGF l 0 = 0 := by simp [axisCGF]

omit [Fintype ι] in
theorem admissible_zero (l : ι → ℝ) : admissible l 0 := by simp [admissible]

theorem admissible_near {l u : ι → ℝ} (h : admissible l u) :
    ∀ᶠ v in 𝓝 (0 : ι → ℝ), admissible l (u+v) := by
  rw [show (fun v ↦ admissible l (u+v)) = fun v ↦ ∀ i, 0 < 1+l i*(u i+v i) by rfl,
    Filter.eventually_all]
  intro i
  exact (isOpen_lt continuous_const (by fun_prop : Continuous (fun v : ι → ℝ ↦ 1+l i*(u i+v i)))).mem_nhds
    (by simpa using h i)

theorem base_laplace {l v : ι → ℝ} (hv : admissible l v) :
    laplace (productLaw l 0) v = exp (∑ i, axisCGF (l i) (v i)) := by
  simpa [laplace] using product_laplace (admissible_zero l) (v := v) (by simpa using hv)

theorem tilt_product {l u v : ι → ℝ} (hu : admissible l u) (hv : admissible l (u+v)) :
    (productLaw l u).tilted (pairing v) = productLaw l (u+v) := by
  let := product_probability hu
  let := product_probability hv
  let := isProbabilityMeasure_tilted ((product_domain hu v).mpr hv)
  apply law_of_local_laplace
  filter_upwards [admissible_near hv] with w hw
  have h' : admissible l (u+(v+w)) := by simpa [add_assoc] using hw
  have eqn : laplace ((productLaw l u).tilted (pairing v)) w =
      laplace (productLaw l u) (v+w) / laplace (productLaw l u) v := by
    unfold laplace
    rw [integral_exp_tilted]
    simp only [Pi.add_apply,pairing_add]
  rw [eqn]
  unfold laplace
  rw [product_laplace hu h',product_laplace hu hv,product_laplace hv hw,←Real.exp_sub]
  refine ⟨exp_pos _,congrArg exp ?_⟩
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply,add_assoc]; ring

end FisherMidpoint
