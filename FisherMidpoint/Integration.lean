module

public import FisherMidpoint.Flat
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Integration of affine coordinates on the common axes

The integrating-factor proof follows JD Jones's companion work on complementary centroids. -/

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
namespace FisherMidpoint

@[simp] theorem sExp_zero (l : ℝ) : sExp l 0 = 0 := by simp [sExp]

theorem sExp_hasDerivAt (l t : ℝ) : HasDerivAt (sExp l) (Real.exp (l*t)) t := by
  by_cases hl : l = 0
  · subst l
    change HasDerivAt (fun y ↦ sExp 0 y) _ t
    simpa [sExp] using hasDerivAt_id' t
  · have hd := (((hasDerivAt_id' t).const_mul l).exp.sub_const 1).div_const l
    change HasDerivAt (fun y ↦ sExp l y) _ t
    simpa [sExp,hl] using hd

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
variable [Fintype ι] {Ω : Set H} {F : H → H} {p : H}

omit [Fintype ι] in
/-- Linear coordinate derivative, including the translation to the chosen base point. -/
theorem coordinate_deriv (B : Module.Basis ι ℝ H) (i : ι) (p x : H) :
    HasFDerivAt (fun y ↦ B.repr (y-p) i) (B.coord i).toContinuousLinearMap x := by
  have hd := (B.coord i).toContinuousLinearMap.hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const p)
  change HasFDerivAt ((B.coord i).toContinuousLinearMap ∘ fun y ↦ y-p) _ x
  simpa only [id_eq,ContinuousLinearMap.comp_id] using hd

omit [Fintype ι] in
theorem axis_column (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : ∀ x ∈ Ω, ContDiffAt ℝ 2 F x) (B : Module.Basis ι ℝ H) (l : ι → ℝ)
    (haxes : ∀ x ∈ Ω, ∀ h i, fderiv ℝ (jac F) x h (B i) = (l i * B.repr h i) • jac F x (B i))
    {x : H} (hx : x ∈ Ω) (i : ι) :
    jac F x (B i) = Real.exp (l i * B.repr (x-p) i) • jac F p (B i) := by
  let q (y : H) := Real.exp (-(l i * B.repr (y-p) i)) • jac F y (B i)
  have hzero (y : H) (hy : y ∈ Ω) : HasFDerivAt (𝕜 := ℝ) q 0 y := by
    have hz := (coordinate_deriv B i p y).const_smul (-(l i))
    have he := hz.exp
    have hj := (((rF y hy).fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).hasFDerivAt.clm_apply (hasFDerivAt_const (B i) y)
    have hd := he.smul hj
    have hval (h : H) : fderiv ℝ (jac F) y h (B i) =
        (l i * B.repr h i) • jac F y (B i) := haxes y hy h i
    convert hd using 1
    · funext z
      simp [q, smul_eq_mul,neg_mul]
    · ext h
      simp [hval, ContinuousLinearMap.smulRight_apply, smul_smul,
        Module.Basis.coord_apply, smul_eq_mul]
      module
  have eqn := ho.is_const_of_fderiv_eq_zero hc
    (fun y hy ↦ (hzero y hy).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hzero y hy).fderiv) hx hp
  change q x = q p at eqn
  have e := congrArg (fun v : H ↦ Real.exp (l i * B.repr (x-p) i) • v) eqn
  simpa [q, smul_smul, ← Real.exp_add] using e

theorem integrate_axes (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : ∀ x ∈ Ω, ContDiffAt ℝ 2 F x) (B : Module.Basis ι ℝ H) (l : ι → ℝ)
    (haxes : ∀ x ∈ Ω, ∀ h i, fderiv ℝ (jac F) x h (B i) = (l i * B.repr h i) • jac F x (B i)) :
    ∀ x ∈ Ω, F x = F p + jac F p (axisMap B l (x-p)) := by
  classical
  let Q (y : H) := F p + jac F p (axisMap B l (y-p))
  have hQ (x : H) (hx : x ∈ Ω) : HasFDerivAt Q (jac F x) x := by
    have hi (i : ι) := ((sExp_hasDerivAt (l i) (B.repr (x-p) i)).comp_hasFDerivAt x
      (coordinate_deriv B i p x)).smul_const (B i)
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)
    have h := ((jac F p).hasFDerivAt.comp x hs).const_add (F p)
    convert h using 1
    · rfl
    apply ContinuousLinearMap.ext
    intro a
    simp only [ContinuousLinearMap.comp_apply,sum_apply,map_sum]
    conv_lhs => rw [← B.sum_repr a, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,axis_column ho hc hp rF B l haxes hx i]
    simp [ContinuousLinearMap.smulRight_apply,
      Module.Basis.coord_apply, smul_smul, mul_comm]
  have hF (x : H) (hx : x ∈ Ω) := ((rF x hx).differentiableAt (by decide)).hasFDerivAt
  have heq := ho.eqOn_of_fderiv_eq hc
    (fun x hx ↦ (hF x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hQ x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hQ x hx).fderiv.symm) hp (show F p = Q p by simp [Q,axisMap])
  exact fun x hx ↦ heq hx

end FisherMidpoint
