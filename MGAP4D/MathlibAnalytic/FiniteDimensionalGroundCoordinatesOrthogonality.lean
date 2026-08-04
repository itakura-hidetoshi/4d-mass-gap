import MGAP4D.MathlibAnalytic.FiniteDimensionalFullGroundExcitationNullDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Vanishing canonical ground coordinates make a vector orthogonal to every
fixed vector of the symmetric positive contraction. -/
theorem inner_fixed_eq_zero_of_groundCoordinates_eq_zero
    (x p : E)
    (hx : D.groundCoordinates x = 0)
    (hp : D.operator p = p) :
    inner ℝ x p = 0 := by
  have hpGround :
      p = D.groundSpectralSynthesis (D.groundCoordinates p) :=
    (D.operator_eq_self_iff_eq_groundSynthesis p).mp hp
  rw [hpGround]
  calc
    inner ℝ x
        (D.groundSpectralSynthesis (D.groundCoordinates p)) =
      inner ℝ (D.eigenbasis.repr x)
        (D.eigenbasis.repr
          (D.groundSpectralSynthesis (D.groundCoordinates p))) := by
        exact
          (D.eigenbasis.repr.inner_map_map x
            (D.groundSpectralSynthesis (D.groundCoordinates p))).symm
    _ = 0 := by
      rw [PiLp.inner_apply]
      apply Finset.sum_eq_zero
      intro i _hi
      by_cases hg : D.eigenvalue i = 1
      · let j : D.GroundSpectralIndex := ⟨i, hg⟩
        have hcoord := congrArg
          (fun z : D.GroundSpectralSpace => z j) hx
        have hxi : D.eigenbasis.repr x i = 0 := by
          simpa [groundCoordinates, fullGroundCoordinates, j] using hcoord
        simp [groundSpectralSynthesis, groundSpectralExtension, hg, hxi]
      · simp [groundSpectralSynthesis, groundSpectralExtension, hg]

/-- Equivalently, zero ground coordinates imply orthogonality to every chosen
Perron fixed representative, independently of its normalization. -/
theorem inner_eq_zero_fixed_of_groundCoordinates_eq_zero
    (x p : E)
    (hx : D.groundCoordinates x = 0)
    (hp : D.operator p = p) :
    inner ℝ p x = 0 := by
  rw [real_inner_comm]
  exact D.inner_fixed_eq_zero_of_groundCoordinates_eq_zero x p hx hp

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
