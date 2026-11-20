module
public import FisherMidpoint.Axes

/-! # What the longitudinal fourth-order equation implies at one point -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace FisherMidpoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
abbrev Jet (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] := H →L[ℝ] ProductTensor H
def form (J : Jet H) (a b c d : H) : ℝ := ⟪J a b c,d⟫_ℝ

/-- The three adjacent transpositions of the lowered covariant derivative. -/
structure SymmetricJet (J : Jet H) : Prop where
  first : ∀ a b c d, form J a b c d = form J b a c d
  middle : ∀ a b c d, form J a b c d = form J a c b d
  last : ∀ a b c d, form J a b c d = form J a b d c

private theorem coefficients (a b c d e f : ℝ)
    (h : ∀ t : ℝ, a+t*b+t^2*c+t^3*d+t^4*e+t^5*f=0) :
    f=0 ∧ e=0 ∧ d=0 ∧ c=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination -(h (-2))/120 + (h (-1))/24 - (h 0)/12 + (h 1)/12 - (h 2)/24 + (h 3)/120
  · linear_combination (h (-2))/24 - (h (-1))/6 + (h 0)/4 - (h 1)/6 + (h 2)/24
  · linear_combination -(h (-2))/24 - (h (-1))/24 + 5*(h 0)/12 - 7*(h 1)/12 + 7*(h 2)/24 - (h 3)/24
  · linear_combination -(h (-2))/24 + 2*(h (-1))/3 - 5*(h 0)/4 + 2*(h 1)/3 - (h 2)/24

private theorem expand3 (J : Jet H) (S : SymmetricJet J) (x e z : H) (t : ℝ) :
    form J (x+t•e) (x+t•e) (x+t•e) z = form J x x x z +
    3*t*form J x x e z + 3*t^2*form J x e e z + t^3*form J e e e z := by
  have A := S.middle x e x z
  have B := S.first e x x z
  have C := S.first e x e z
  have D := S.middle e e x z
  simp only [form, map_add, map_smul, add_apply,
    smul_apply, inner_add_left,real_inner_smul_left] at *
  simp only [B, A, D, C]
  ring

/-- The scalar equation annihilates an active eigenaxis in every slot. -/
theorem active_axis (K : ProductTensor H) (J : Jet H) (hs : SymmetricProduct K)
    (S : SymmetricJet J) (hp : ∀ h, form J h h h (K h h) = 0)
    (e : H) (χ : H → ℝ) (he : ∀ x, K x e = χ x • e) (hl : χ e ≠ 0) :
    ∀ a b c, form J a b c e = 0 := by
  let F := form J
  have rows (x : H) : χ e * F e e e e = 0 ∧
      2*χ x*F e e e e + 3*χ e*F x e e e = 0 ∧
      F e e e (K x x) + 6*χ x*F x e e e + 3*χ e*F x x e e = 0 ∧
      3*F x e e (K x x) + 6*χ x*F x x e e + χ e*F x x x e = 0 := by
    let k := K x x
    let l := χ e
    let r := χ x
    have row (t : ℝ) :
        F x x x k + t*(3*F x x e k+2*r*F x x x e) +
        t^2*(3*F x e e k+6*r*F x x e e+l*F x x x e) +
        t^3*(F e e e k+6*r*F x e e e+3*l*F x x e e) +
        t^4*(2*r*F e e e e+3*l*F x e e e) + t^5*(l*F e e e e) = 0 := by
      have prod : K (x+t•e) (x+t•e) = k + (2*r*t+l*t^2) • e := by
        dsimp [k,r,l]
        simp only [map_add, map_smul, add_apply,
          smul_apply, hs.1 e x, he, smul_smul]
        module
      have equation := hp (x+t•e)
      rw [prod] at equation
      have addLast (u v z : H) (s : ℝ) :
          form J u u u (v+s•z) = form J u u u v + s*form J u u u z := by
        simp [form,inner_add_right,real_inner_smul_right]
      rw [addLast, expand3 J S x e k, expand3 J S x e e] at equation
      dsimp only [F]
      linear_combination equation
    exact coefficients _ _ _ _ _ _ row
  have h0 : F e e e e = 0 := (mul_eq_zero.mp (rows e).1).resolve_left hl
  have h1 (x : H) : F x e e e = 0 := by
    have H1 := (rows x).2.1
    change 2*χ x*F e e e e + 3*χ e*F x e e e = 0 at H1
    rw [h0] at H1
    exact (mul_eq_zero.mp (show χ e * F x e e e = 0 by linarith)).resolve_left hl
  have h2 (x : H) : F x x e e = 0 := by
    have H2 := (rows x).2.2.1
    change F e e e (K x x) + 6*χ x*F x e e e + 3*χ e*F x x e e = 0 at H2
    have eq1 : F e e e (K x x) = F (K x x) e e e := by
      dsimp [F]; rw [S.last e e e _,S.middle e e _ e,S.first e _ e e]
    rw [eq1,h1,h1] at H2
    exact (mul_eq_zero.mp (show χ e * F x x e e = 0 by linarith)).resolve_left hl
  have h2mixed (x y : H) : F x y e e = 0 := by
    have h := h2 (x+y)
    have hxy := S.first y x e e
    have hx := h2 x
    have hy := h2 y
    simp only [F,form,map_add,add_apply,inner_add_left] at *
    linarith
  have h3 (x : H) : F x x x e = 0 := by
    have H3 := (rows x).2.2.2
    change 3*F x e e (K x x) + 6*χ x*F x x e e + χ e*F x x x e = 0 at H3
    have eq2 : F x e e (K x x) = F x (K x x) e e := by
      dsimp [F]; rw [S.last x e e _,S.middle x e _ e]
    rw [eq2,h2mixed,h2] at H3
    exact (mul_eq_zero.mp (show χ e * F x x x e = 0 by linarith)).resolve_left hl
  intro a b c
  have polar : F (a+b+c) (a+b+c) (a+b+c) e - F (a+b) (a+b) (a+b) e -
      F (b+c) (b+c) (b+c) e - F (a+c) (a+c) (a+c) e +
      F a a a e + F b b b e + F c c c e = 6 * F a b c e := by
    have p1 := S.first b a c e
    have p2 := S.middle a c b e
    have p3 := S.first c a b e
    have p4 := S.middle b c a e
    have p5 := S.middle c b a e
    simp only [F,form,map_add,add_apply,inner_add_left] at *
    linarith
  rw [h3,h3,h3,h3,h3,h3,h3] at polar
  linarith

end FisherMidpoint
