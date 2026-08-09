import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentGapClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSUniformVarianceContinuumExcitation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

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
    {F : D.positiveTimeSubalgebra}

/-- Actual finite Wilson boundary decay and a scale-uniform nonzero centered
observable together give a lower bound on the mass variationally derived from
the reconstructed continuum OS Hamiltonian.

The boundary certificate contributes the Hamiltonian Rayleigh lower bound.  The
uniform centered-variance certificate contributes an actual nonzero continuum
excitation, and hence a genuine nonempty excitation Rayleigh set.  No numerical
mass value is prescribed by this theorem. -/
theorem mass_le_physicalYangMillsMass_of_uniformCenteredVariance
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta B hInvariant F)
    (hContinuous :
      (C.toContinuumPositiveTimeObservableContractionSemigroup).
        StrongContinuityOnObservableStates) :
    let Tinf :=
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.
        PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.
          toStronglyContinuousPhysicalSemigroup
            C.toContinuumPositiveTimeObservableContractionSemigroup hContinuous
    Q.mass ≤ Tinf.physicalYangMillsMass := by
  let Pinf :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
  let Tobs := C.toContinuumPositiveTimeObservableContractionSemigroup
  let Tinf :=
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.
      PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.
        toStronglyContinuousPhysicalSemigroup Tobs hContinuous
  let hP : Pinf.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta B hInvariant
  have hSelf : IsSelfAdjoint Tinf.closedRightHamiltonian := by
    simpa only [Tinf, Tobs] using
      Q.closedRightHamiltonian_isSelfAdjoint hContinuous
  let phi : Pinf.VacuumOrthogonalHilbert := V.continuumExcitation
  have hphi : phi ≠ 0 := by
    simpa only [phi] using V.continuumExcitation_ne_zero
  let W : Tinf.PhysicalYangMillsExcitationDomainWitness :=
    Tinf.physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation
      hP hSelf phi hphi
  apply Tinf.uniformRayleighLowerBound_le_physicalYangMillsMass W
  intro psi _hpsi horthogonal
  simpa only [Tinf, Tobs, Pinf] using
    Q.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      hContinuous psi horthogonal

/-- Therefore the mass defined from the actual continuum Yang--Mills
Hamiltonian is strictly positive whenever the finite Wilson model supplies
both a positive boundary-moment gap and one scale-uniform nonzero centered
observable. -/
theorem physicalYangMillsMass_pos_of_uniformCenteredVariance
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta B hInvariant F)
    (hContinuous :
      (C.toContinuumPositiveTimeObservableContractionSemigroup).
        StrongContinuityOnObservableStates) :
    let Tinf :=
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.
        PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.
          toStronglyContinuousPhysicalSemigroup
            C.toContinuumPositiveTimeObservableContractionSemigroup hContinuous
    0 < Tinf.physicalYangMillsMass := by
  let Tinf :=
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.
      PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.
        toStronglyContinuousPhysicalSemigroup
          C.toContinuumPositiveTimeObservableContractionSemigroup hContinuous
  have hLower : Q.mass ≤ Tinf.physicalYangMillsMass := by
    simpa only [Tinf] using
      Q.mass_le_physicalYangMillsMass_of_uniformCenteredVariance V hContinuous
  exact lt_of_lt_of_le Q.mass_pos hLower

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate

end

end MathlibAnalytic
end MGAP4D
