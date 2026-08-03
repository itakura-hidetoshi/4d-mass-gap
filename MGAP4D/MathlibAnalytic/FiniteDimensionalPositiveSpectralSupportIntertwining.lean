import MGAP4D.MathlibAnalytic.FiniteDimensionalPositiveSpectralSupportHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Extend positive-support coordinates by zero to all transfer eigenmodes. -/
noncomputable def positiveSpectralExtension :
    D.PositiveSpectralSpace →ₗ[ℝ]
      EuclideanSpace ℝ (Fin D.dimension) where
  toFun := fun x j =>
    if h : 0 < D.eigenvalue j then x ⟨j, h⟩ else 0
  map_add' := by
    intro x y
    ext j
    by_cases h : 0 < D.eigenvalue j
    · simp [h]
    · simp [h]
  map_smul' := by
    intro c x
    ext j
    by_cases h : 0 < D.eigenvalue j
    · simp [h]
    · simp [h]

@[simp] theorem positiveSpectralExtension_apply_pos
    (x : D.PositiveSpectralSpace)
    (i : D.PositiveSpectralIndex) :
    D.positiveSpectralExtension x i.1 = x i := by
  simp [positiveSpectralExtension, i.2]

/-- Synthesize a positive-support coordinate vector in the original Hilbert
space using Mathlib's canonical orthonormal transfer eigenbasis. -/
noncomputable def positiveSpectralSynthesis :
    D.PositiveSpectralSpace →ₗ[ℝ] E :=
  D.eigenbasis.repr.symm.toLinearMap.comp D.positiveSpectralExtension

/-- Coordinates of the synthesized vector are exactly the zero extension of
the support coordinates. -/
theorem eigenbasis_repr_positiveSpectralSynthesis
    (x : D.PositiveSpectralSpace)
    (j : Fin D.dimension) :
    D.eigenbasis.repr (D.positiveSpectralSynthesis x) j =
      D.positiveSpectralExtension x j := by
  simp [positiveSpectralSynthesis]

/-- Positive-support synthesis is injective. -/
theorem positiveSpectralSynthesis_injective :
    Function.Injective D.positiveSpectralSynthesis := by
  intro x y hxy
  ext i
  have hcoord := congrArg
    (fun z : E => D.eigenbasis.repr z i.1) hxy
  simpa [D.eigenbasis_repr_positiveSpectralSynthesis, i.2] using hcoord

/-- The original transfer intertwines exactly with the positive-support
diagonal transfer under spectral synthesis.  Zero modes vanish because
positivity forces every non-positive eigenvalue to equal zero. -/
theorem operator_positiveSpectralSynthesis_intertwining
    (x : D.PositiveSpectralSpace) :
    D.operator (D.positiveSpectralSynthesis x) =
      D.positiveSpectralSynthesis (D.positiveSpectralTransfer x) := by
  apply D.eigenbasis.repr.injective
  ext j
  rw [D.symmetric.eigenvectorBasis_apply_self_apply (by rfl)]
  by_cases h : 0 < D.eigenvalue j
  · simp [D.eigenbasis_repr_positiveSpectralSynthesis,
      positiveSpectralExtension, h]
  · have hz : D.eigenvalue j = 0 :=
      le_antisymm (le_of_not_gt h) (D.eigenvalue_nonneg j)
    simp [D.eigenbasis_repr_positiveSpectralSynthesis,
      positiveSpectralExtension, h, hz]

/-- All natural powers of the original transfer intertwine with the exact
diagonal support semigroup. -/
theorem operator_pow_positiveSpectralSynthesis_intertwining
    (n : ℕ)
    (x : D.PositiveSpectralSpace) :
    (D.operator ^ n) (D.positiveSpectralSynthesis x) =
      D.positiveSpectralSynthesis (D.positiveSpectralSemigroup n x) := by
  induction n with
  | zero =>
      simp [D.positiveSpectralSemigroup_zero]
  | succ n ih =>
      rw [pow_succ']
      change
        D.operator
            ((D.operator ^ n) (D.positiveSpectralSynthesis x)) =
          D.positiveSpectralSynthesis
            (D.positiveSpectralSemigroup (Nat.succ n) x)
      rw [ih, D.operator_positiveSpectralSynthesis_intertwining]
      congr 1
      ext i
      simp [positiveSpectralSemigroup_apply, positiveSpectralTransfer_apply,
        pow_succ, mul_assoc]

/-- The support semigroup embedded in the original Hilbert space has exact
Hamiltonian spectral weights at every natural time. -/
theorem operator_pow_positiveSpectralSynthesis_hamiltonian_weight
    (n : ℕ)
    (x : D.PositiveSpectralSpace)
    (i : D.PositiveSpectralIndex) :
    D.eigenbasis.repr
        ((D.operator ^ n) (D.positiveSpectralSynthesis x)) i.1 =
      (Real.exp (-D.positiveSpectralEnergy i)) ^ n * x i := by
  rw [D.operator_pow_positiveSpectralSynthesis_intertwining]
  simp [D.eigenbasis_repr_positiveSpectralSynthesis,
    D.positiveSpectralSemigroup_eq_exp_neg_energy_pow_apply, i.2]

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
