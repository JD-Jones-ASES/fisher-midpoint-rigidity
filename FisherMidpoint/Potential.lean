module
public import FisherMidpoint.Integration
public import FisherMidpoint.Factors

/-! # Integrating the log-partition in Fisher coordinates -/

@[expose] public section
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology InnerProductSpace BigOperators ContDiff
namespace FisherMidpoint

/-- Primitive of the normalized affine coordinate in Fisher arclength. -/
def primitive (l t : ℝ) : ℝ := if l = 0 then t^2/2 else (exp (l*t)-1-l*t)/l^2

def inverseAxis (l u : ℝ) : ℝ := if l = 0 then u else log (1+l*u)/l

@[simp] theorem primitive_zero (l : ℝ) : primitive l 0 = 0 := by simp [primitive]

@[simp] theorem inverseAxis_zero (l : ℝ) : inverseAxis l 0 = 0 := by simp [inverseAxis]

theorem inverseAxis_continuous_zero (l : ℝ) : ContinuousAt (inverseAxis l) 0 := by
  by_cases hl : l = 0
  · subst l; change ContinuousAt (fun u ↦ inverseAxis 0 u) 0
    simp only [inverseAxis,ite_true]; fun_prop
  · change ContinuousAt (fun u ↦ inverseAxis l u) 0
    simp only [inverseAxis,ite_eq_right hl]
    apply ContinuousAt.div_const
    apply ContinuousAt.log <;> first | fun_prop | simp

theorem sExp_inverse {l u : ℝ} (hu : 0 < 1+l*u) : sExp l (inverseAxis l u) = u := by
  by_cases hl : l = 0
  · simp [sExp,inverseAxis,hl]
  simp only [sExp,inverseAxis,ite_eq_right hl]
  rw [show l*(log (1+l*u)/l) = log (1+l*u) by field_simp,exp_log hu]
  field_simp; ring

theorem primitive_inverse {l u : ℝ} (hu : 0 < 1+l*u) :
    primitive l (inverseAxis l u) = axisCGF l u := by
  by_cases hl : l = 0
  · simp [primitive,inverseAxis,axisCGF,hl]
  simp only [primitive,inverseAxis,axisCGF,ite_eq_right hl]
  rw [show l*(log (1+l*u)/l) = log (1+l*u) by field_simp,exp_log hu]
  field_simp; ring

theorem primitive_deriv (l t : ℝ) : HasDerivAt (primitive l) (sExp l t) t := by
  by_cases hl : l = 0
  · subst l; convert (((hasDerivAt_id' t).pow 2).div_const 2) using 1
    · funext; simp [primitive]
    · simp [sExp]
  · have a := (hasDerivAt_id' t).const_mul l
    convert (((a.exp.sub_const 1).sub a).div_const (l^2)) using 1
    · funext; simp [primitive,hl]
    · simp [sExp,hl]; field_simp

theorem sExp_opposite (l t : ℝ) : exp (l*t) * sExp (-l) t = sExp l t := by
  by_cases hl : l = 0
  · simp [sExp,hl]
  · simp only [sExp,ite_eq_right hl,ite_eq_right (neg_ne_zero.mpr hl),neg_mul,exp_neg]
    field_simp [exp_ne_zero (l*t)]; ring

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [Fintype ι]

omit [FiniteDimensional ℝ H] in
theorem axisMap_coord (B : Module.Basis ι ℝ H) (l : ι → ℝ) (x : H) (i : ι) :
    B.repr (axisMap B l x) i = sExp (l i) (B.repr x i) := by
  classical
  simp [axisMap,map_sum,Module.Basis.repr_self,Finsupp.single_apply]

variable {Ω : Set H} {F G : H → H} {p : H}

theorem integrate_potential (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : ∀ x ∈ Ω, ContDiffAt ℝ 2 F x) (rG : ∀ x ∈ Ω, ContDiffAt ℝ 2 G x)
    (B : OrthonormalBasis ι ℝ H) (l : ι → ℝ)
    (axes : ∀ x ∈ Ω, ∀ h i,
      fderiv ℝ (jac F) x h (B i) = (l i * B.repr h i) • jac F x (B i) ∧
      fderiv ℝ (jac G) x h (B i) = (-(l i) * B.repr h i) • jac G x (B i))
    (metric : ∀ a b, ⟪jac G p a,jac F p b⟫_ℝ = ⟪a,b⟫_ℝ)
    (A : H → ℝ) (dA : ∀ x ∈ Ω, HasFDerivAt A ((innerSL ℝ (G x-G p)).comp (jac F x)) x) :
    ∀ x ∈ Ω, A x = A p + ∑ i, primitive (l i) (B.repr (x-p) i) := by
  classical
  have AF (x : H) (hx : x ∈ Ω) (h : H) (i : ι) := (axes x hx h i).1
  have AG (x : H) (hx : x ∈ Ω) (h : H) (i : ι) := (axes x hx h i).2
  have gval := integrate_axes ho hc hp rG B.toBasis (-l) (by simpa using AG)
  let Q (y : H) := A p + ∑ i, primitive (l i) (B.repr (y-p) i)
  have dQ (x : H) (hx : x ∈ Ω) : HasFDerivAt Q ((innerSL ℝ (G x-G p)).comp (jac F x)) x := by
    have d (i : ι) := (primitive_deriv (l i) (B.toBasis.repr (x-p) i)).comp_hasFDerivAt x
      (coordinate_deriv B.toBasis i p x)
    have z := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ d i)).const_add (A p)
    convert z using 1
    · funext y; simp [Q]
    apply ContinuousLinearMap.coe_injective
    apply B.toBasis.ext
    intro i
    have fcol := axis_column ho hc hp rF B.toBasis l (by simpa using AF) hx i
    have col : jac F x (B i) = exp (l i * B.repr (x-p) i) • jac F p (B i) := by simpa using fcol
    change ⟪G x-G p,jac F x (B i)⟫_ℝ = _
    rw [gval x hx,add_sub_cancel_left,col,real_inner_smul_right,metric,real_inner_comm,
      ←B.repr_apply_apply,← B.coe_toBasis_repr_apply (axisMap B.toBasis (-l) (x-p)) i,axisMap_coord]
    simp [Module.Basis.coord_apply,smul_eq_mul,sExp_opposite]
  exact ho.eqOn_of_fderiv_eq hc
    (fun x hx ↦ (dA x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (dQ x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (dA x hx).fderiv.trans (dQ x hx).fderiv.symm) hp (by simp)

end FisherMidpoint
