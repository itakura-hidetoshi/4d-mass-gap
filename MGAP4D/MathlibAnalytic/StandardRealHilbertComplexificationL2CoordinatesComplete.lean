import MGAP4D.MathlibAnalytic.StandardRealHilbertComplexificationNormedTransport
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The standard complexification is the real-linear `L²` product of its two real coordinates. -/
noncomputable def coordinatesL2 :
    StandardRealHilbertComplexification H ≃ₗᵢ[ℝ] WithLp 2 (H × H) where
  __ := (WithLp.linearEquiv 2 ℝ (H × H)).symm
  norm_map' z := by
    rw [WithLp.prod_norm_eq_of_L2, norm_eq_standardNorm, standardNorm_eq]

@[simp]
theorem coordinatesL2_apply
    (z : StandardRealHilbertComplexification H) :
    coordinatesL2 z = WithLp.toLp 2 (z.1, z.2) :=
  rfl

@[simp]
theorem coordinatesL2_symm_apply
    (z : WithLp 2 (H × H)) :
    (coordinatesL2 (H := H)).symm z = (z.fst, z.snd) :=
  rfl

/-- Continuous real-linear coordinate equivalence with the `L²` product model. -/
noncomputable def coordinatesL2ContinuousLinearEquiv :
    StandardRealHilbertComplexification H ≃L[ℝ] WithLp 2 (H × H) :=
  (coordinatesL2 (H := H)).toContinuousLinearEquiv

@[simp]
theorem coordinatesL2ContinuousLinearEquiv_apply
    (z : StandardRealHilbertComplexification H) :
    coordinatesL2ContinuousLinearEquiv z = WithLp.toLp 2 (z.1, z.2) :=
  rfl

@[simp]
theorem coordinatesL2ContinuousLinearEquiv_symm_apply
    (z : WithLp 2 (H × H)) :
    (coordinatesL2ContinuousLinearEquiv (H := H)).symm z = (z.fst, z.snd) :=
  rfl

/-- Completeness transports from the real Hilbert space to its standard complexification. -/
noncomputable instance instCompleteSpace [CompleteSpace H] :
    CompleteSpace (StandardRealHilbertComplexification H) :=
  (coordinatesL2 (H := H)).toIsometryEquiv.completeSpace

end StandardRealHilbertComplexification

end

end MathlibAnalytic
end MGAP4D
