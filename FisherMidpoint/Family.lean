module
public import FisherMidpoint.Rigidity
public import FisherMidpoint.Potential
public import FisherMidpoint.Tilts

/-! # Identification of the sufficient-statistic law from the midpoint test -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Topology InnerProductSpace BigOperators ContDiff
namespace FisherMidpoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The log-Laplace transform of the sufficient statistic at the reference member. -/
def cumulant [MeasurableSpace H] (μ : Measure H) (u : H) : ℝ :=
  log (∫ y, exp ⟪u,y⟫_ℝ ∂μ)

/-- Natural parameters are measured relative to the reference member at `p`.
The expectation coordinate is the gradient of the actual log-Laplace transform. -/
structure MeanCoordinates [MeasurableSpace H] (μ : Measure H) (Ω : Set H) (F G : H → H) (p : H) : Prop where
  finite : ∀ x ∈ Ω, Integrable (fun y ↦ exp ⟪F x-F p,y⟫_ℝ) μ
  mean : ∀ x ∈ Ω, HasFDerivAt (cumulant μ) (innerSL ℝ (G x)) (F x-F p)

variable {ι : Type*} [Fintype ι]

def statistic (B : OrthonormalBasis ι ℝ H) (F G : H → H) (p y : H) (i : ι) : ℝ :=
  ⟪jac F p (B i),y-G p⟫_ℝ

theorem continuous_statistic (B : OrthonormalBasis ι ℝ H) (F G : H → H) (p : H) :
    Continuous (statistic B F G p) := continuous_pi fun i ↦ by unfold statistic; fun_prop

theorem statistic_bijective {Ω : Set H} {F G : H → H} {p : H} (A : FisherChart Ω F G)
    (hp : p ∈ Ω) (B : OrthonormalBasis ι ℝ H) : Function.Bijective (statistic B F G p) := by
  let f (a : H) := jac G p a + G p
  have full : Function.Bijective f := (Equiv.addRight (G p)).bijective.comp (A.expectedInv p hp).bijective
  have eqn : statistic B F G p ∘ f = B.toBasis.equivFun := by
    funext a i
    change ⟪jac F p (B i),jac G p a + G p-G p⟫_ℝ = _
    rw [add_sub_cancel_right,real_inner_comm,A.metric p hp,real_inner_comm]
    exact (B.repr_apply_apply a i).symm
  exact (Function.Bijective.of_comp_iff _ full).mp (eqn ▸ B.toBasis.equivFun.bijective)

private theorem centered_integral [MeasurableSpace H] {μ : Measure H} [IsProbabilityMeasure μ]
    (v m : H) (hv : Integrable (fun y ↦ exp ⟪v,y⟫_ℝ) μ) :
    ∫ y, exp ⟪v,y-m⟫_ℝ ∂μ = exp (cumulant μ v - ⟪m,v⟫_ℝ) := by
  have h := mgf_pos (t := 1) (X := fun y ↦ ⟪v,y⟫_ℝ) (by simpa using hv)
  simp only [mgf,one_mul] at h
  simp only [inner_sub_right,exp_sub,integral_div,cumulant,exp_log h,real_inner_comm m v]

private theorem potential_deriv [MeasurableSpace H] {μ : Measure H} {Ω : Set H} {F G : H → H}
    {p x : H} (reg : DifferentiableAt ℝ F x) (M : MeanCoordinates μ Ω F G p) (hx : x ∈ Ω) :
    HasFDerivAt (fun y ↦ cumulant μ (F y-F p) - ⟪G p,F y-F p⟫_ℝ)
      ((innerSL ℝ (G x-G p)).comp (jac F x)) x := by
  have dz := reg.hasFDerivAt.sub_const (F p)
  have d := ((M.mean x hx).comp x dz).sub ((innerSL ℝ (G p)).hasFDerivAt.comp x dz)
  convert d using 1
  · rfl
  · ext a; simp

open EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "I" => Fin (Module.finrank ℝ E)

/-- A scalar midpoint observation on one patch identifies one affine transformation of the
actual law. Its complete maximal tilt domain and every tilted product are explicit. -/
theorem fisher_factorization {Ω : Set E} {F G : E → E} {p : E} (μ : Measure E) [IsProbabilityMeasure μ]
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω) (A : FisherChart Ω F G)
    (M : MeanCoordinates μ Ω F G p) (test : ∀ q ∈ Ω, LongitudinalAt F G q) :
    ∃ (B : OrthonormalBasis I ℝ E) (l : I → ℝ),
      Function.Bijective (statistic B F G p) ∧
      μ.map (statistic B F G p) = productLaw l 0 ∧
      ∀ u : I → ℝ,
        (Integrable (fun y ↦ exp (pairing u y)) (μ.map (statistic B F G p)) ↔ admissible l u) ∧
        (admissible l u → (μ.map (statistic B F G p)).tilted (pairing u) = productLaw l u) := by
  classical
  obtain ⟨B,l,axes⟩ := midpoint_axes ho hc A test hp
  let Y := statistic B F G p
  have contY := continuous_statistic B F G p
  have prY : IsProbabilityMeasure (μ.map Y) := by
    constructor; rw [Measure.map_apply contY.measurable MeasurableSet.univ,Set.preimage_univ,measure_univ]
  have base : IsProbabilityMeasure (productLaw l 0) := product_probability (admissible_zero l)
  let value (x : E) := cumulant μ (F x-F p) - ⟪G p,F x-F p⟫_ℝ
  have pot := integrate_potential ho hc hp (fun x hx ↦ (A.natural x hx).of_le (by decide))
    (fun x hx ↦ (A.expected x hx).of_le (by decide)) B l axes (A.metric p hp) value
    (fun x hx ↦ potential_deriv ((A.natural x hx).differentiableAt (by decide)) M hx)
  have zero : value p = 0 := by simp [value,cumulant]
  have natural := integrate_axes ho hc hp (fun x hx ↦ (A.natural x hx).of_le (by decide)) B.toBasis l
    (fun x hx h i ↦ by simpa using (axes x hx h i).1)
  let cut (u : I → ℝ) := p + ∑ i, inverseAxis (l i) (u i) • B i
  have coord (u : I → ℝ) (i : I) : B.repr (cut u-p) i = inverseAxis (l i) (u i) := by
    rw [←B.coe_toBasis_repr_apply]; simp [cut,map_sum]
  have cut0 : cut 0 = p := by simp [cut]
  have contCut : ContinuousAt cut 0 := by
    apply continuousAt_const.add
    apply tendsto_finsetSum
    intro i _
    have ci : ContinuousAt (fun u : I → ℝ ↦ inverseAxis (l i) (u i)) (0 : I → ℝ) :=
      (inverseAxis_continuous_zero (l i)).comp (f := fun u : I → ℝ ↦ u i) (x := (0:I → ℝ))
        (continuous_apply i).continuousAt
    exact ci.smul (continuousAt_const (y := B i))
  have law : μ.map Y = productLaw l 0 := by
    apply law_of_local_laplace
    have near := contCut.tendsto ((cut0 ▸ ho.mem_nhds hp) : Ω ∈ 𝓝 (cut 0))
    have dom : ∀ᶠ u in 𝓝 (0:I → ℝ), admissible l u := by simpa using admissible_near (admissible_zero l)
    filter_upwards [near,dom] with u hx hu
    have nval : F (cut u)-F p = ∑ i, u i • jac F p (B i) := by
      rw [natural _ hx,add_sub_cancel_left]
      simp only [axisMap,map_sum,map_smul,B.coe_toBasis,B.coe_toBasis_repr_apply,coord]
      exact Finset.sum_congr rfl fun i _ ↦ congrArg (· • jac F p (B i)) (sExp_inverse (hu i))
    have pair (y : E) : pairing u (Y y) = ⟪F (cut u)-F p,y-G p⟫_ℝ := by
      simp [nval,pairing,Y,statistic,sum_inner,real_inner_smul_left]
    have eval : laplace (μ.map Y) u = exp (∑ i, axisCGF (l i) (u i)) := by
      unfold laplace
      have continuousWeight : Continuous (fun x : I → ℝ ↦ exp (pairing u x)) := by unfold pairing; fun_prop
      rw [integral_map contY.measurable.aemeasurable continuousWeight.aestronglyMeasurable]
      change (∫ y, exp (pairing u (Y y)) ∂μ) = _
      simp_rw [pair]
      rw [centered_integral _ _ (M.finite _ hx)]
      change exp (value (cut u)) = _
      rw [pot _ hx,zero,zero_add]; simp only [coord]
      congr 1
      exact Finset.sum_congr rfl (fun i _ ↦ primitive_inverse (hu i))
    rw [eval,base_laplace hu]
    exact ⟨exp_pos _,rfl⟩
  refine ⟨B,l,statistic_bijective A hp B,law,?_⟩
  intro u
  change (Integrable _ (μ.map Y) ↔ _) ∧ (_ → (μ.map Y).tilted _ = _)
  rw [law]
  exact ⟨by simpa using product_domain (admissible_zero l) u,fun hu ↦ by
    simpa using tilt_product (u := 0) (v := u) (admissible_zero l) (by simpa using hu)⟩

end FisherMidpoint
