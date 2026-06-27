import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentGapClosure

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate

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

/-- The exponential shared-boundary Poincaré estimate generates the integrated
boundary Gram-moment gap certificate. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingMeasurableBoundaryL2PoincareGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- The exponential finite Wilson boundary estimate generates the continuum
half-time OS quadratic mass-gap certificate with exact mass `Q.mass`. -/
noncomputable def toContinuumHalfQuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.HalfQuadraticGapCertificate
      C.toContinuumPositiveTimeObservableContractionSemigroup :=
  Q.toApproximatingBoundaryMomentGapCertificate
    |>.toContinuumHalfQuadraticGapCertificate

/-- Exponential finite Wilson boundary decay and continuum observable-state
continuity produce a self-adjoint graph-closed continuum OS Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (hContinuous :
      (C.toContinuumPositiveTimeObservableContractionSemigroup).StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        C.toContinuumPositiveTimeObservableContractionSemigroup
        hContinuous).closedRightHamiltonian := by
  exact Q.toApproximatingBoundaryMomentGapCertificate
    |>.closedRightHamiltonian_isSelfAdjoint hContinuous

/-- The exponential boundary Poincaré estimate gives the exact positive-mass
Rayleigh lower bound on the full graph-closed continuum Hamiltonian domain. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
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
  exact Q.toApproximatingBoundaryMomentGapCertificate
    |>.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      hContinuous psi hpsi

/-- The exponential finite Wilson boundary estimate identifies the zero-energy
space of the graph-closed continuum Hamiltonian with the normalized vacuum
line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
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
  exact Q.toApproximatingBoundaryMomentGapCertificate
    |>.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
      hContinuous psi

/-- The exponential boundary Poincaré estimate excludes nonzero continuum
closed-Hamiltonian eigenvectors with energy strictly between zero and
`Q.mass`. -/
theorem closedRightHamiltonian_no_eigenvector_in_open_mass_gap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
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
  exact Q.toApproximatingBoundaryMomentGapCertificate
    |>.closedRightHamiltonian_no_eigenvector_in_open_mass_gap
      hContinuous hlambda_pos hlambda_mass psi hEigen

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate

end MathlibAnalytic
end MGAP4D

end