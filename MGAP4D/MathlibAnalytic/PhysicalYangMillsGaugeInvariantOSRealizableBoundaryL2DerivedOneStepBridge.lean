import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableBoundaryL2DerivedTransferRate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepDerivedRateGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableBoundaryDerivedOneStepSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableBoundaryDerivedOneStepSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableBoundaryDerivedOneStepSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableBoundaryDerivedOneStepSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableBoundaryDerivedOneStepSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableBoundaryDerivedOneStepSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The Gram feature belonging to every actual finite Wilson OS carrier is
integrable automatically from bounded continuity and compact-Haar finiteness.

This lemma is deliberately restated in the mass-free derived-transfer layer so
that the physical bridge has no dependency on any exact-value module. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_derivedTransfer_boundaryMoment_gram_integrable
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) :
    Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) := by
  exact
    periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
      (halfExtent n) N hN (beta n) (hbeta n)
      (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F)
      b

/-- The full reflected finite Wilson Gibbs integral is exactly the squared
shared-boundary Gram-moment integral, with all integrability obligations
generated from the actual bounded-continuous Wilson observable.

No mass value occurs in this identity. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_derivedTransfer_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  exact
    physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n F
      (fun b =>
        physical_yang_mills_evenPeriodicWilsonOS_derivedTransfer_boundaryMoment_gram_integrable
          S D halfExtent N hN beta hbeta B hInvariant n F b)

/-- The OS carrier norm square of every actual finite Wilson observable is the
literal compact-Haar shared-boundary Gram-moment integral.

This mass-free theorem is the structural identity previously buried in an
exact-value file. It depends only on the actual finite reflected Gibbs integral
and the already-proved boundary Gram factorization. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖F‖ ^ 2 =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  calc
    ‖F‖ ^ 2 = Pn.osQuadraticValue F :=
      (Pn.osQuadraticValue_eq_norm_sq F).symm
    _ = physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F :=
      physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F
    _ = ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) :=
      physical_yang_mills_evenPeriodicWilsonOS_derivedTransfer_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
        S D halfExtent N hN beta hbeta B hInvariant n F

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily

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
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The boundary `L²` transfer estimate generated by `Kₙ` is exactly the
one-step centered OS carrier estimate required by the realizable discrete gap
spine. The factor is the actual operator norm `‖Kₙ‖`; no numerical mass enters. -/
theorem oneStep_centered_carrier_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ‖R.realizableCarrierTranslation hInvariant n 1
        (Pn.vacuumCenteredCarrier F)‖ ≤
      A.transferFactor n * ‖Pn.vacuumCenteredCarrier F‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let F0 : Pn.Carrier := Pn.vacuumCenteredCarrier F
  let F1 : Pn.Carrier :=
    R.realizableCarrierTranslation hInvariant n 1 F0
  have hboundary := A.oneStep_centered_boundaryMoment_le n F
  dsimp only at hboundary
  have hnorm0 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
  have hnorm1 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
  change ‖F1‖ ≤ A.transferFactor n * ‖F0‖
  rw [← hnorm1, ← hnorm0] at hboundary
  have hright : 0 ≤ A.transferFactor n * ‖F0‖ :=
    mul_nonneg (A.transferFactor_nonneg n) (norm_nonneg F0)
  nlinarith [norm_nonneg F1, norm_nonneg F0]

/-- Hence every actual boundary transfer family canonically supplies the finite
one-step certificate used by the discrete/floor weak-star continuum spine of
#1503, with `rₙ` definitionally equal to `‖Kₙ‖`. -/
noncomputable def toRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant A.transferFactor where
  transferFactor_nonneg := A.transferFactor_nonneg
  oneStep_centered_norm_le := A.oneStep_centered_carrier_norm_le

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate

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
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- A positive logarithmic rate certificate for the actual boundary operators
therefore supplies both ingredients consumed by the corrected continuum route:
the generic positive discrete rate limit and the actual one-step Wilson gap
certificate with factor `rₙ = ‖Kₙ‖`. -/
noncomputable def toRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant
        A.transfer.transferFactor :=
  A.transfer.toRealizableOneStepGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end
