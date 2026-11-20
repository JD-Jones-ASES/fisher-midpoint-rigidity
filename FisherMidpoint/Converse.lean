module
public import FisherMidpoint.Potential
public import FisherMidpoint.Equidistance

/-! # Global midpoint formulas in a Gaussian and gamma product -/

@[expose] public section
noncomputable section
open Real Set Metric
open scoped InnerProductSpace
namespace FisherMidpoint

/-- Natural midpoint in the unit-speed Fisher coordinate. -/
def axisMidpoint (l x y : ℝ) : ℝ :=
  if l = 0 then (x+y)/2 else log ((exp (l*x)+exp (l*y))/2)/l

theorem axis_midpoint_average (l x y : ℝ) :
    sExp l (axisMidpoint l x y) + sExp l (axisMidpoint l x y) = sExp l x + sExp l y := by
  by_cases h : l = 0
  · simp [sExp,axisMidpoint,h]
  · simp only [sExp,axisMidpoint,ite_eq_right h]
    rw [show l*(log ((exp (l*x)+exp (l*y))/2)/l) = log ((exp (l*x)+exp (l*y))/2) by field_simp,
      exp_log (by positivity)]; ring

theorem sExp_injective (l : ℝ) : Function.Injective (sExp l) := by
  intro x y e
  by_cases h : l = 0
  · simpa [sExp,h] using e
  · simp [sExp,h] at e
    exact e

theorem opposite_midpoints (l x y : ℝ) : axisMidpoint l x y + axisMidpoint (-l) x y = x+y := by
  by_cases h : l = 0
  · simp [h,axisMidpoint]
  · let a := exp (l*x)
    let b := exp (l*y)
    have ha : 0 < a := exp_pos _
    have hb : 0 < b := exp_pos _
    have ratio : (a+b)/2 / ((a⁻¹+b⁻¹)/2) = a*b := by
      field_simp [ha.ne',hb.ne',(add_pos ha hb).ne']; ring
    simp only [axisMidpoint,ite_eq_right h,ite_eq_right (neg_ne_zero.mpr h),neg_mul,exp_neg]
    change log ((a+b)/2)/l + log ((a⁻¹+b⁻¹)/2)/(-l) = x+y
    rw [div_neg,←sub_eq_add_neg,←sub_div,←log_div (by positivity) (by positivity),ratio, log_mul ha.ne' hb.ne']
    simp [a,b]; field_simp

/-- The two affine midpoints exist uniquely and preserve the Euclidean Fisher midpoint globally. -/
theorem product_midpoints {ι : Type*} (l : ι → ℝ) (x y : ι → ℝ) :
    ∃ a b : ι → ℝ,
      (∀ i, sExp (l i) (a i) + sExp (l i) (a i) = sExp (l i) (x i)+sExp (l i) (y i)) ∧
      (∀ i, sExp (-(l i)) (b i) + sExp (-(l i)) (b i) = sExp (-(l i)) (x i)+sExp (-(l i)) (y i)) ∧
      a+b=x+y ∧ ∀ A B : ι → ℝ,
        (∀ i, sExp (l i) (A i)+sExp (l i) (A i)=sExp (l i) (x i)+sExp (l i) (y i)) →
        (∀ i, sExp (-(l i)) (B i)+sExp (-(l i)) (B i)=sExp (-(l i)) (x i)+sExp (-(l i)) (y i)) →
        A=a ∧ B=b := by
  let a (i : ι) := axisMidpoint (l i) (x i) (y i)
  let b (i : ι) := axisMidpoint (-(l i)) (x i) (y i)
  have unique (k z X Y : ℝ) (eqn : sExp k z + sExp k z = sExp k X + sExp k Y) :
      z = axisMidpoint k X Y := sExp_injective k (by linarith [axis_midpoint_average k X Y])
  refine ⟨a,b,fun i ↦ axis_midpoint_average _ _ _,fun i ↦ axis_midpoint_average _ _ _,
    funext (fun i ↦ opposite_midpoints _ _ _),?_⟩
  intro u v hu hv
  exact ⟨funext fun i ↦ unique _ _ _ _ (hu i),funext fun i ↦ unique _ _ _ _ (hv i)⟩

/-- The first derivative of the standardized log-partition is the expectation coordinate. -/
def axisMean (l u : ℝ) : ℝ := u / (1+l*u)

theorem axis_cumulant_deriv {l u : ℝ} (hu : 0 < 1+l*u) :
    HasDerivAt (axisCGF l) (axisMean l u) u := by
  have h := ((hasDerivAt_id' u).const_mul l).const_add 1
  by_cases hl : l = 0
  · subst l
    convert ((hasDerivAt_id' u).pow 2).div_const 2 using 1
    · funext; simp [axisCGF]
    · simp [axisMean]
  · convert ((hasDerivAt_id' u).div_const l).sub ((h.log hu.ne').div_const (l^2)) using 1
    · funext; simp [axisCGF,hl]
    · simp [axisMean]
      field_simp [hu.ne',hl,show 1+u*l ≠ 0 by nlinarith]
      ring_nf

theorem axis_chart_metric (l x : ℝ) :
    0 < 1+l*sExp l x ∧ axisMean l (sExp l x) = sExp (-l) x ∧
    exp (l*x) * exp ((-l)*x) = 1 := by
  have val : 1+l*sExp l x = exp (l*x) := by
    by_cases hl : l=0
    · simp [hl]
    · simp [sExp,hl]; field_simp; ring
  refine ⟨val ▸ exp_pos _,?_,by rw [←exp_add]; ring_nf; exact exp_zero⟩
  rw [axisMean,val,← sExp_opposite l x]
  field_simp

end FisherMidpoint
