import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryMomentGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingCenteredQuadraticLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumHalfQuadraticGapClosure

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- Boundary Gram-moment decay generates the continuum half-time OS quadratic
certificate through exact boundary factorization, finite reflected-integral
transport, and weak-star convergence of centered quadratic values. -/
noncomputable def toContinuumHalfQuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.HalfQuadraticGapCertificate
      C.toContinuumPositiveTimeObservableContractionSemigroup :=
  Q.toApproximatingFiniteIntegralGapCertificate
    |>.toApproximatingHalfQuadraticGapCertificate
    |>.toContinuumHalfQuadraticGapCertificate

/-- The local boundary-moment gap and continuum observable-state continuity
produce a self-adjoint graph-closed OS Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (hContinuous :
      (C.toContinuumPositiveTimeObservableContractionSemigroup).StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        C.toContinuumPositiveTimeObservableContractionSemigroup
        hContinuous).closedRightHamiltonian := by
  exact Q.toContinuumHalfQuadraticGapCertificate
    |>.closedRightHamiltonian_isSelfAdjoint hContinuous

/-- The boundary-moment estimate gives the positive mass Rayleigh lower bound on
the full graph-closed continuum Hamiltonian domain. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (hContinuous :
      (C.toContinuumPositiveTimeObservableContractionSemigroup).StrongContinuityOnObservableStates)
    (psi :
      (PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        C.toContinuumPositiveTimeObservableContractionSemigroup
        hContinuous).closedRightHamiltonian.domain)
    (hpsi : inner ℝ
      (psi :
        (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant).PhysicalHilbert)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant).vacuum = 0) :
    Q.mass * ‖(psi :
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant).PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ
        ((PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
          C.toContinuumPositiveTimeObservableContractionSemigroup
          hContinuous).closedRightHamiltonian psi)
        (psi :
          (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant).PhysicalHilbert) := by
  exact Q.toContinuumHalfQuadraticGapCertificate
    |>.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta B hInvariant)
      hContinuous psi hpsi

/-- The zero-energy eigenspace obtained from the local boundary-moment gap is
exactly the normalized continuum vacuum line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (hContinuous :
      (C.toContinuumPositiveTimeObservableContractionSemigroup).StrongContinuityOnObservableStates)
    (psi :
      (PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        C.toContinuumPositiveTimeObservableContractionSemigroup
        hContinuous).closedRightHamiltonian.domain) :
    (PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        C.toContinuumPositiveTimeObservableContractionSemigroup
        hContinuous).closedRightHamiltonian psi = 0 ↔
      (psi :
        (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant).PhysicalHilbert) =
        (inner ℝ
          (psi :
            (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant).PhysicalHilbert)
          (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant).vacuum) •
          (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant).vacuum := by
  exact Q.toContinuumHalfQuadraticGapCertificate
    |>.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta B hInvariant)
      hContinuous psi

/-- The boundary-moment gap excludes nonzero closed-Hamiltonian eigenvectors
with energy strictly between zero and the transferred mass. -/
theorem closedRightHamiltonian_no_eigenvector_in_open_mass_gap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (hContinuous :
      (C.toContinuumPositiveTimeObservableContractionSemigroup).StrongContinuityOnObservableStates)
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_mass : lambda < Q.mass)
    (psi :
      (PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        C.toContinuumPositiveTimeObservableContractionSemigroup
        hContinuous).closedRightHamiltonian.domain)
    (hEigen :
      (PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
          C.toContinuumPositiveTimeObservableContractionSemigroup
          hContinuous).closedRightHamiltonian psi =
        lambda •
          (psi :
            (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant).PhysicalHilbert)) :
    (psi :
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant).PhysicalHilbert) = 0 := by
  exact Q.toContinuumHalfQuadraticGapCertificate
    |>.closedRightHamiltonian_no_eigenvector_in_open_mass_gap
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta B hInvariant)
      hContinuous hlambda_pos hlambda_mass psi hEigen

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate

end MathlibAnalytic
end MGAP4D

end
