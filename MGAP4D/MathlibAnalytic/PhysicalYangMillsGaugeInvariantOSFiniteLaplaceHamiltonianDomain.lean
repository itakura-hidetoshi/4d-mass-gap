import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteLaplaceGeneratorValue
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianResolventLowerBound
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

/-- The canonical Hamiltonian shift maps a finite Laplace integral to the
initial vector minus its exponentially decaying terminal orbit. -/
theorem rightHamiltonianShift_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightHamiltonianShift lambda
        (T.finiteLaplaceIntegralGeneratorDomain lambda h psi) =
      psi - Real.exp ((-lambda) * (h : ℝ)) •
        T.toPhysicalSemigroup.operator h psi := by
  rw [T.rightHamiltonianShift_apply,
    T.finiteLaplaceIntegralGeneratorDomain_coe,
    T.rightHamiltonian_apply,
    T.rightGenerator_finiteLaplaceIntegral]
  module

/-- The finite Laplace vector bundled in the closed Hamiltonian domain. -/
def finiteLaplaceIntegralClosedDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonian.domain :=
  ⟨T.finiteLaplaceIntegral lambda h psi,
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1
      (T.finiteLaplaceIntegral_mem_rightGeneratorDomain lambda h psi)⟩

@[simp] theorem finiteLaplaceIntegralClosedDomain_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    (T.finiteLaplaceIntegralClosedDomain lambda h psi :
      P.PhysicalHilbert) = T.finiteLaplaceIntegral lambda h psi :=
  rfl

/-- The closed Hamiltonian agrees with the canonical Hamiltonian on finite
Laplace integrals. -/
theorem closedRightHamiltonian_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonian
        (T.finiteLaplaceIntegralClosedDomain lambda h psi) =
      T.rightHamiltonian
        (T.finiteLaplaceIntegralGeneratorDomain lambda h psi) := by
  exact (T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.2
    (x := T.finiteLaplaceIntegralGeneratorDomain lambda h psi)
    (y := T.finiteLaplaceIntegralClosedDomain lambda h psi) rfl).symm

/-- The positive shift of the closed Hamiltonian obeys the finite-time Laplace
resolvent identity. -/
theorem closedRightHamiltonianShift_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonianShift lambda
        (T.finiteLaplaceIntegralClosedDomain lambda h psi) =
      psi - Real.exp ((-lambda) * (h : ℝ)) •
        T.toPhysicalSemigroup.operator h psi := by
  simpa only [T.closedRightHamiltonianShift_apply,
    T.closedRightHamiltonian_finiteLaplaceIntegral,
    T.rightHamiltonianShift_apply,
    T.finiteLaplaceIntegralGeneratorDomain_coe] using
      T.rightHamiltonianShift_finiteLaplaceIntegral lambda h psi

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end
end MathlibAnalytic
end MGAP4D
