import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumHalfQuadraticGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumUniqueness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedMassGapPointSpectrum
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup
namespace HalfQuadraticGapCertificate

variable {T : P.PositiveTimeObservableContractionSemigroup}

/-- Reflection/time exchange in a continuum half-quadratic gap certificate makes
the graph-closed reconstructed OS Hamiltonian self-adjoint. -/
theorem closedRightHamiltonian_isSelfAdjoint
    (Q : T.HalfQuadraticGapCertificate)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian := by
  exact T.closedRightHamiltonian_isSelfAdjoint_of_reflectionTimeTranslationExchange
    Q.exchange hContinuous

/-- The positive half-quadratic gap passes from the dense centered observable
core to the full graph-closed Hamiltonian domain. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (Q : T.HalfQuadraticGapCertificate)
    (hP : P.IsNormalized)
    (hContinuous : T.StrongContinuityOnObservableStates)
    (psi :
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ
        ((StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
          T hContinuous).closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  let Ts :=
    StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
      T hContinuous
  let G : Ts.VacuumSemigroupGapSlope :=
    Q.toVacuumSemigroupGapSlope hP hContinuous
  exact G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    Ts hP psi hpsi

/-- The zero-energy eigenspace of the graph-closed reconstructed Hamiltonian is
exactly the normalized vacuum line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (Q : T.HalfQuadraticGapCertificate)
    (hP : P.IsNormalized)
    (hContinuous : T.StrongContinuityOnObservableStates)
    (psi :
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian.domain) :
    (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  let Ts :=
    StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
      T hContinuous
  let G : Ts.VacuumSemigroupGapSlope :=
    Q.toVacuumSemigroupGapSlope hP hContinuous
  exact G.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    Ts hP psi

/-- No nonzero closed-Hamiltonian eigenvector can have energy strictly between
zero and the mass supplied by the half-quadratic gap certificate. -/
theorem closedRightHamiltonian_no_eigenvector_in_open_mass_gap
    (Q : T.HalfQuadraticGapCertificate)
    (hP : P.IsNormalized)
    (hContinuous : T.StrongContinuityOnObservableStates)
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_mass : lambda < Q.mass)
    (psi :
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian.domain)
    (hEigen :
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
          T hContinuous).closedRightHamiltonian psi =
        lambda • (psi : P.PhysicalHilbert)) :
    (psi : P.PhysicalHilbert) = 0 := by
  let Ts :=
    StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
      T hContinuous
  let G : Ts.VacuumSemigroupGapSlope :=
    Q.toVacuumSemigroupGapSlope hP hContinuous
  have hSelf : IsSelfAdjoint Ts.closedRightHamiltonian :=
    Q.closedRightHamiltonian_isSelfAdjoint hContinuous
  exact G.closedRightHamiltonian_no_eigenvector_in_open_mass_gap_of_selfAdjoint
    Ts hP hSelf hlambda_pos hlambda_mass psi hEigen

end HalfQuadraticGapCertificate
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
