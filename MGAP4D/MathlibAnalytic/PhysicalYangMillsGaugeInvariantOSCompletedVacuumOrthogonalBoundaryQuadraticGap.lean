import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedVacuumOrthogonalBoundaryTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2QuadraticGap

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance completedVacuumOrthogonalBoundaryQuadraticGapSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedVacuumOrthogonalBoundaryQuadraticGapSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedVacuumOrthogonalBoundaryQuadraticGapSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedVacuumOrthogonalBoundaryQuadraticGapSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedVacuumOrthogonalBoundaryQuadraticGapSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedVacuumOrthogonalBoundaryQuadraticGapSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant}

/-- The completed finite OS quadratic-gap certificate canonically generates an
*actual* boundary-Haar `L²` quadratic-gap certificate.

The boundary transfer is not an abstract supplied operator: it is the centered
completed realization

`Ĵ_n ∘ T_n(t/2) ∘ P_{Ω_n^⊥} ∘ Ĵ_n⁻¹ ∘ P_{ran Ĵ_n}`

constructed from the actual Wilson boundary-moment isometry.  Gram
integrability and boundary `L²` membership are theorem-generated, and the
intertwining is inherited from the exact centered completion theorem.

Thus, after #1476, no actual-adjoint/open-half factorization hypothesis is
needed to enter the legacy boundary-`L²` gap pipeline. -/
noncomputable def toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C where
  mass := R.mass
  mass_pos := R.mass_pos
  quadraticDecayFactor := R.quadraticDecayFactor
  quadraticDecayFactor_nonneg := R.quadraticDecayFactor_nonneg
  slope_tendsto := R.slope_tendsto
  exchange := R.exchange
  gram_integrable := by
    intro n F b
    exact
      PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate.gram_integrable
        (S := S) (D := D) (halfExtent := halfExtent) (N := N)
        (hN := hN) (beta := beta) (hbeta := hbeta)
        (B := Q.toWeakStarBridge) (hInvariant := hInvariant) n F b
  boundaryMoment_memLp :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant
  boundaryTransfer :=
    Q.completedVacuumOrthogonalBoundaryTransfer hInvariant C
  boundaryMoment_intertwining := by
    intro n t
    dsimp only
    intro F
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    have hcentered :=
      Q.completedVacuumOrthogonalBoundaryTransfer_vacuumCentered_intertwining
        hInvariant C n t F
    simpa [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2]
      using hcentered
  boundaryTransfer_quadratic_bound := by
    intro n t v
    exact
      Q.completedVacuumOrthogonalBoundaryTransfer_quadratic_bound
        hInvariant C R n t v

/-- The direct actual-boundary realization therefore also generates the older
operator-norm boundary-transfer certificate. -/
noncomputable def toCompletedVacuumOrthogonalBoundaryL2TransferGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    |>.toApproximatingBoundaryL2TransferGapCertificate

/-- Likewise, the actual centered boundary realization enters the integrated
boundary-moment gap route without any additional model input. -/
noncomputable def toCompletedVacuumOrthogonalBoundaryMomentGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- And hence it generates the completed finite Wilson OS vacuum-sector gap
certificate consumed by the continuum strong-limit Hamiltonian route. -/
noncomputable def toCompletedVacuumOrthogonalApproximatingVacuumGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate

end MathlibAnalytic
end MGAP4D

end
