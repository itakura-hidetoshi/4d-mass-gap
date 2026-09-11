import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentAutomaticL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2QuadraticGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance automaticAnalyticBoundaryL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance automaticAnalyticBoundaryL2SpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance automaticAnalyticBoundaryL2SpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance automaticAnalyticBoundaryL2SpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance automaticAnalyticBoundaryL2SpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

section ActualWilsonCarrier

variable
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- The canonical shared-boundary `L²` representative of an actual finite
Wilson OS carrier vector.  Its `MemLp` receipt is generated internally by the
finite Wilson measure theory rather than supplied by a certificate. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2Automatic
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
    S D halfExtent N hN beta hbeta B hInvariant n F
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp
      S D halfExtent N hN beta hbeta B hInvariant n F)

end ActualWilsonCarrier

section AutomaticAnalyticCertificate

variable
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)

/-- The finite Wilson boundary-`L²` quadratic-gap interface after all purely
analytic membership and boundedness receipts have been discharged internally.

Compared with the older bounded certificate, this structure no longer asks for
open-half finite measure, Gram-feature measurability, a Gram majorant, or
boundary-moment `MemLp`.  Those facts are theorems of the finite Wilson model.
The remaining data are exactly the spectral rate and the model-specific
boundary transfer realization, intertwining, and quadratic contraction. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingAutomaticAnalyticBoundaryL2QuadraticGapCertificate where
  mass : ℝ
  mass_pos : 0 < mass
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg : ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  boundaryTransfer :
    (n : ℕ) → NNReal →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        boundaryTransfer n t
            (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2Automatic
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F)) =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2Automatic
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
  boundaryTransfer_quadratic_bound :
    ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
        (halfExtent n) N),
      ‖boundaryTransfer n t v‖ ^ 2 ≤
        quadraticDecayFactor t * ‖v‖ ^ 2

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingAutomaticAnalyticBoundaryL2QuadraticGapCertificate

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

/-- Generate the full quadratic boundary-`L²` certificate.  Gram integrability
comes from bounded-continuous Wilson reflection positivity, while boundary
`MemLp` comes from the automatic finite-Haar theorem. -/
noncomputable def toApproximatingBoundaryL2QuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingAutomaticAnalyticBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  gram_integrable := by
    intro n F b
    change Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent N hN beta hbeta B hInvariant n F)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)
    exact
      periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent N hN beta hbeta B hInvariant n F)
        b
  boundaryMoment_memLp := by
    intro n F
    exact
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp
        S D halfExtent N hN beta hbeta B hInvariant n F
  boundaryTransfer := Q.boundaryTransfer
  boundaryMoment_intertwining := by
    intro n t
    dsimp
    intro F
    simpa [physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2Automatic] using
      Q.boundaryMoment_intertwining n t F
  boundaryTransfer_quadratic_bound := Q.boundaryTransfer_quadratic_bound

/-- The automatic-analytic interface therefore generates the boundary-transfer
operator-norm gap package. -/
noncomputable def toApproximatingBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingAutomaticAnalyticBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2QuadraticGapCertificate
    |>.toApproximatingBoundaryL2TransferGapCertificate

/-- The same model-specific boundary-transfer data generate the integrated
boundary-moment gap package. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingAutomaticAnalyticBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2QuadraticGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- And the same data generate completed finite Wilson OS vacuum-sector
norm decay. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingAutomaticAnalyticBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2QuadraticGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingAutomaticAnalyticBoundaryL2QuadraticGapCertificate

end AutomaticAnalyticCertificate

end MathlibAnalytic
end MGAP4D

end
