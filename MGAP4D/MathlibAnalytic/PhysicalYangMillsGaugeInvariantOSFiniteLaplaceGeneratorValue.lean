import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteLaplaceSemigroupAction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section
open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Every finite Laplace integral has the expected right-generator value. -/
theorem hasRightGeneratorValue_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.HasRightGeneratorValue
      (T.finiteLaplaceIntegral lambda h psi)
      (lambda • T.finiteLaplaceIntegral lambda h psi +
        Real.exp ((-lambda) * (h : ℝ)) •
          T.toPhysicalSemigroup.operator h psi - psi) := by
  unfold HasRightGeneratorValue
  have hreal :=
    (T.shiftedExponentialTimePrimitive_hasDerivAt_zero_explicit
      lambda h psi).tendsto_slope_zero_right
  have hcomp := hreal.comp nnreal_coe_tendsto_zero_right
  simpa only [T.rightDifferenceQuotient_finiteLaplaceIntegral,
    zero_add] using hcomp

/-- Every finite Laplace integral belongs to the canonical generator domain. -/
theorem finiteLaplaceIntegral_mem_rightGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.finiteLaplaceIntegral lambda h psi ∈ T.rightGeneratorDomain :=
  ⟨lambda • T.finiteLaplaceIntegral lambda h psi +
      Real.exp ((-lambda) * (h : ℝ)) •
        T.toPhysicalSemigroup.operator h psi - psi,
    T.hasRightGeneratorValue_finiteLaplaceIntegral lambda h psi⟩

/-- The finite Laplace integral bundled in the canonical generator domain. -/
def finiteLaplaceIntegralGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightGeneratorDomain :=
  ⟨T.finiteLaplaceIntegral lambda h psi,
    T.finiteLaplaceIntegral_mem_rightGeneratorDomain lambda h psi⟩

@[simp] theorem finiteLaplaceIntegralGeneratorDomain_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    (T.finiteLaplaceIntegralGeneratorDomain lambda h psi :
      P.PhysicalHilbert) = T.finiteLaplaceIntegral lambda h psi :=
  rfl

/-- The canonical generator evaluates by the finite-time resolvent formula. -/
theorem rightGenerator_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightGenerator
        (T.finiteLaplaceIntegralGeneratorDomain lambda h psi) =
      lambda • T.finiteLaplaceIntegral lambda h psi +
        Real.exp ((-lambda) * (h : ℝ)) •
          T.toPhysicalSemigroup.operator h psi - psi := by
  apply T.hasRightGeneratorValue_unique
    (T.rightGenerator_hasRightGeneratorValue
      (T.finiteLaplaceIntegralGeneratorDomain lambda h psi))
  exact T.hasRightGeneratorValue_finiteLaplaceIntegral lambda h psi

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end
end MathlibAnalytic
end MGAP4D
