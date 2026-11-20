module
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-! # Orthogonal axes for a symmetric associative metric product -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace BigOperators
namespace FisherMidpoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
abbrev ProductTensor (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H →L[ℝ] H

/-- Tensor symmetries of a lowered Fisher connection coefficient. -/
def SymmetricProduct (K : ProductTensor H) : Prop :=
  (∀ u v, K u v = K v u) ∧ ∀ u v w, ⟪K u v,w⟫_ℝ = ⟪v,K u w⟫_ℝ

/-- Commutation of left multiplications in a Fisher-flat Hessian chart. -/
def Commutes (K : ProductTensor H) : Prop := ∀ u v w, K u (K v w) = K v (K u w)

/-- A single orthonormal basis diagonalizes every multiplication map. -/
theorem orthogonal_axes [FiniteDimensional ℝ H] (K : ProductTensor H)
    (hs : SymmetricProduct K) (hc : Commutes K) :
    ∃ (B : OrthonormalBasis (Fin (Module.finrank ℝ H)) ℝ H) (l : Fin (Module.finrank ℝ H) → ℝ),
      ∀ x i, K x (B i) = (l i * B.repr x i) • B i := by
  classical
  let T (x : H) := (K x).toLinearMap
  have sym (x : H) : (T x).IsSymmetric := hs.2 x
  have com (x y : H) : Commute (T x) (T y) := LinearMap.ext (hc x y)
  let V (χ : H → ℝ) := ⨅ x, Module.End.eigenspace (T x) (χ x)
  let original : DirectSum.IsInternal V := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute sym
    (fun x y _ ↦ com x y)
  let : Fintype {χ // V χ ≠ ⊥} := original.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  let internal := DirectSum.isInternal_ne_bot_iff.mpr original
  let orth := (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces sym).comp
    (Subtype.coe_injective (p := fun χ ↦ V χ ≠ ⊥))
  let B := internal.subordinateOrthonormalBasis rfl orth
  let χ (i : Fin (Module.finrank ℝ H)) := internal.subordinateOrthonormalBasisIndex rfl i orth
  have eig (i) (x : H) : K x (B i) = (χ i).val x • B i :=
    Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp
      (internal.subordinateOrthonormalBasis_subordinate rfl i orth) x)
  refine ⟨B, fun i ↦ (χ i).val (B i), fun x i ↦ ?_⟩
  have eqn := congrArg (fun v : H ↦ ⟪B i,v⟫_ℝ) (hs.1 x (B i))
  rw [eig] at eqn
  have eii := eig i (B i)
  have eqr : ⟪B i, K (B i) x⟫_ℝ = ⟪K (B i) (B i),x⟫_ℝ := (hs.2 _ _ _).symm
  rw [eqr,eii] at eqn
  have hunit : ⟪B i,B i⟫_ℝ = 1 := by simp [B.orthonormal.1 i]
  simp only [real_inner_smul_right, real_inner_smul_left, hunit, mul_one] at eqn
  calc
    K x (B i) = (χ i).val x • B i := eig i x
    _ = ((χ i).val (B i) * B.repr x i) • B i := by rw [B.repr_apply_apply]; exact congrArg (· • B i) eqn
end FisherMidpoint
