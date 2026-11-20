module
public import FisherMidpoint.Midpoints

/-! # Midpoint preservation and equidistance in a Fisher isometry chart -/

@[expose] public section
noncomputable section
open Set Metric
open scoped InnerProductSpace
namespace FisherMidpoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Natural and expectation midpoints of a nearby pair have the same Fisher midpoint
as the original endpoints. Sums express twice the Fisher midpoint in this chart. -/
def PreservesAt (F G : H → H) (p : H) : Prop :=
  ∃ r > (0:ℝ), ∀ P ∈ ball p r, ∀ Q ∈ ball p r, ∀ a ∈ ball p r, ∀ b ∈ ball p r,
    F a+F a=F P+F Q → G b+G b=G P+G Q → a+b=P+Q

/-- The updated Fisher midpoint is equidistant from the two original endpoints. -/
def EquidistantAt (F G : H → H) (p : H) : Prop :=
  ∃ r > (0:ℝ), ∀ P ∈ ball p r, ∀ Q ∈ ball p r, ∀ a ∈ ball p r, ∀ b ∈ ball p r,
    F a+F a=F P+F Q → G b+G b=G P+G Q → ‖a+b-(2:ℝ)•P‖=‖a+b-(2:ℝ)•Q‖

theorem equidistant_of_preserves {F G : H → H} {p : H} (h : PreservesAt F G p) :
    EquidistantAt F G p := by
  obtain ⟨r,hr,Hr⟩ := h
  refine ⟨r,hr,fun P hP Q hQ a ha b hb fa gb ↦ ?_⟩
  rw [Hr P hP Q hQ a ha b hb fa gb,show P+Q-(2:ℝ)•P=Q-P by module,
    show P+Q-(2:ℝ)•Q=P-Q by module,norm_sub_rev]

theorem longitudinal_of_equidistant {F G : H → H} {p : H} (h : EquidistantAt F G p) :
    LongitudinalAt F G p := by
  obtain ⟨r,hr,Hr⟩ := h
  intro v κ hκ
  refine ⟨r,hr,r/(‖v‖+1),by positivity,?_⟩
  intro t ht ht' a ha b hb fa gb
  have hr' := (lt_div_iff₀ (show 0 < ‖v‖+1 by positivity)).mp ht'
  have small : ‖(t/2)•v‖ < r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg v]
  have hP : p-(t/2)•v ∈ ball p r := by
    rw [mem_ball,dist_eq_norm,show p-(t/2)•v-p = -((t/2)•v) by module,norm_neg]; exact small
  have hQ : p+(t/2)•v ∈ ball p r := by rw [mem_ball,dist_eq_norm,add_sub_cancel_left]; exact small
  have e := Hr _ hP _ hQ a ha b hb fa gb
  let S := (a-p)+(b-p)
  have eqn := congrArg (fun x : ℝ ↦ x^2) e
  change ‖a+b-(2:ℝ)•(p-(t/2)•v)‖^2 = ‖a+b-(2:ℝ)•(p+(t/2)•v)‖^2 at eqn
  rw [show a+b-(2:ℝ)•(p-(t/2)•v) = S+t•v by dsimp [S]; module,
      show a+b-(2:ℝ)•(p+(t/2)•v) = S-t•v by dsimp [S]; module,
      norm_add_sq_real,norm_sub_sq_real,real_inner_smul_right] at eqn
  have hz := (mul_eq_zero.mp (show t*⟪S,v⟫_ℝ=0 by linarith)).resolve_left ht.ne'
  change |⟪v,S⟫_ℝ| ≤ _
  rw [real_inner_comm,hz,abs_zero]; positivity

end FisherMidpoint
