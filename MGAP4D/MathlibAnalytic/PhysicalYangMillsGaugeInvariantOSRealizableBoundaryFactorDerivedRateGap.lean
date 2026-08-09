import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepDerivedRateGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableBoundaryFactorDerivedRateSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableBoundaryFactorDerivedRateSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableBoundaryFactorDerivedRateSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableBoundaryFactorDerivedRateSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableBoundaryFactorDerivedRateSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableBoundaryFactorDerivedRateSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The boundary Gram feature of every actual finite Wilson OS carrier is
integrable.  This is a model theorem coming only from bounded continuity and
compact-Haar finiteness; it contains no mass parameter. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_derivedRate_boundaryMoment_gram_integrable
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

/-- The actual finite reflected Wilson Gibbs integral is exactly the squared
shared-boundary Gram-moment norm.  Again this identity is independent of any
proposed gap value. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_derivedRate_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
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
        physical_yang_mills_evenPeriodicWilsonOS_derivedRate_boundaryMoment_gram_integrable
          S D halfExtent N hN beta hbeta B hInvariant n F b)

/-- Actual one-step Wilson boundary transfer factored through a real normed
feature space, with a scale-dependent factor `r_n`.

The factor is not a mass.  It is a theorem-facing finite operator bound.  Its
logarithmic continuum rate is derived later by `PositiveDiscreteTransferRateLimit`.
No exact numerical value occurs in this package. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (transferFactor : ℕ → ℝ) where
  transferFactor_nonneg : ∀ n, 0 ≤ transferFactor n
  boundaryMoment_memLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      MemLp
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  FeatureState : ℕ → Type
  [featureNormedAddCommGroup : ∀ n, NormedAddCommGroup (FeatureState n)]
  [featureNormedSpace : ∀ n, NormedSpace ℝ (FeatureState n)]
  analysis :
    (n : ℕ) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        FeatureState n
  synthesis :
    (n : ℕ) → FeatureState n →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_factorized_intertwining :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (synthesis n).comp (analysis n)
          (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (Pn.vacuumCenteredCarrier F)
            (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1
            (Pn.vacuumCenteredCarrier F))
          (boundaryMoment_memLp n
            (R.realizableCarrierTranslation hInvariant n 1
              (Pn.vacuumCenteredCarrier F)))
  factor_opNorm_mul_le :
    ∀ n : ℕ,
      ‖synthesis n‖ * ‖analysis n‖ ≤ transferFactor n

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate.featureNormedAddCommGroup
  PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate.featureNormedSpace

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate

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
    {transferFactor : ℕ → ℝ}

/-- The theorem-generated shared-boundary transfer is the factor composition. -/
noncomputable def boundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  (A.synthesis n).comp (A.analysis n)

/-- Mathlib operator-norm submultiplicativity turns the factor estimate into the
actual one-step shared-boundary transfer estimate. -/
theorem boundaryTransfer_opNorm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor)
    (n : ℕ) :
    ‖A.boundaryTransfer n‖ ≤ transferFactor n := by
  exact ((A.synthesis n).opNorm_comp_le (A.analysis n)).trans
    (A.factor_opNorm_mul_le n)

/-- The factorized boundary operator estimate generates the literal integrated
shared-boundary Gram-moment one-step decay. -/
theorem oneStep_centered_boundaryMoment_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    (∫ b,
      ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)) b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
    (transferFactor n) ^ 2 *
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (Pn.vacuumCenteredCarrier F) b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let F0 : Pn.Carrier := Pn.vacuumCenteredCarrier F
  let F1 : Pn.Carrier :=
    R.realizableCarrierTranslation hInvariant n 1 F0
  let v0 :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
      (A.boundaryMoment_memLp n F0)
  let v1 :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
      (A.boundaryMoment_memLp n F1)
  let K := A.boundaryTransfer n
  have hintertwining : K v0 = v1 := by
    simpa [Pn, F0, F1, v0, v1, K, boundaryTransfer] using
      A.boundaryMoment_factorized_intertwining n F
  have hnorm : ‖v1‖ ≤ transferFactor n * ‖v0‖ := by
    calc
      ‖v1‖ = ‖K v0‖ := by rw [← hintertwining]
      _ ≤ ‖K‖ * ‖v0‖ := K.le_opNorm v0
      _ ≤ transferFactor n * ‖v0‖ :=
        mul_le_mul_of_nonneg_right
          (A.boundaryTransfer_opNorm_le n) (norm_nonneg v0)
  have hsq :
      ‖v1‖ ^ 2 ≤ (transferFactor n) ^ 2 * ‖v0‖ ^ 2 := by
    nlinarith [norm_nonneg v1, norm_nonneg v0, A.transferFactor_nonneg n]
  rw [← physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
    (A.boundaryMoment_memLp n F1)]
  rw [← physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
    (A.boundaryMoment_memLp n F0)]
  exact hsq

/-- The boundary factorization reconstructs the actual centered one-step Wilson
OS norm estimate with the same finite factor `r_n`. -/
noncomputable def toOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor where
  transferFactor_nonneg := A.transferFactor_nonneg
  oneStep_centered_norm_le := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    have hboundary := A.oneStep_centered_boundaryMoment_le n F
    dsimp only at hboundary
    have hreflected :
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (R.realizableCarrierTranslation hInvariant n 1
              (Pn.vacuumCenteredCarrier F)) ≤
          (transferFactor n) ^ 2 *
            physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
              (Pn.vacuumCenteredCarrier F) := by
      rw [physical_yang_mills_evenPeriodicWilsonOS_derivedRate_finiteReflectedIntegral_eq_boundaryMoment_norm_sq,
        physical_yang_mills_evenPeriodicWilsonOS_derivedRate_finiteReflectedIntegral_eq_boundaryMoment_norm_sq]
      exact hboundary
    rw [← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral,
      ← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral] at hreflected
    rw [Pn.osQuadraticValue_eq_norm_sq, Pn.osQuadraticValue_eq_norm_sq] at hreflected
    have hx :
        0 ≤ ‖R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)‖ := norm_nonneg _
    have hy : 0 ≤ ‖Pn.vacuumCenteredCarrier F‖ := norm_nonneg _
    have hr : 0 ≤ transferFactor n := A.transferFactor_nonneg n
    nlinarith [mul_nonneg hr hy]

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryFactorDerivedRateGapCertificate

end MathlibAnalytic
end MGAP4D

end
