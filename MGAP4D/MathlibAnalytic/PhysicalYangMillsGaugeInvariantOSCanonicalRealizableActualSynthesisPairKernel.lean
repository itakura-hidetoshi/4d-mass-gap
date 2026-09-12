import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfL2TemporalStep
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryTransferSpatialSlicePair
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualAdjointSynthesisBoundaryTransferGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance canonicalRealizableSynthesisPairKernelSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalRealizableSynthesisPairKernelTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalRealizableSynthesisPairKernelCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalRealizableSynthesisPairKernelSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalRealizableSynthesisPairKernelMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalRealizableSynthesisPairKernelBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance canonicalRealizableSynthesisPairKernelSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalRealizableSynthesisPairKernelBoundaryHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance canonicalRealizableSynthesisPairKernelOpenHalfHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- In ordered spatial-endpoint coordinates, every matrix coefficient of the
actual Wilson adjoint synthesis operator is exactly the rectangular Wilson
Gram-kernel pairing.

This is only Hilbert adjunction plus the exact boundary/pair coordinate
isometries.  It performs no new integral manipulation: the rectangular kernel
pairing is the already-constructed Mathlib Hilbert--Schmidt pairing. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesis_pair_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N))
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          H N
          (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
            H N hN beta hbeta u)) z =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta)
        (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
          H N z)
        u := by
  let e := periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
  let eInv := periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
  let A := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta
  let S := periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
    H N hN beta hbeta
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H N hN beta hbeta
  have hz : e (eInv z) = z := by
    simpa [e, eInv] using
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePair_rightInverse H N z
  calc
    inner ℝ (e (S u)) z = inner ℝ (e (S u)) (e (eInv z)) := by
      rw [hz]
    _ = inner ℝ (S u) (eInv z) := by
      exact e.inner_map_map (S u) (eInv z)
    _ = inner ℝ u (A (eInv z)) := by
      simpa [A, S] using
        periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_inner
          H N hN beta hbeta u (eInv z)
    _ = inner ℝ (A (eInv z)) u := by
      exact real_inner_comm _ _
    _ = realL2HilbertSchmidtKernelPairing K (eInv z) u := by
      simpa [A, K] using
        periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
          H N hN beta hbeta (eInv z) u

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- Exact one-step finite-Wilson receipt for an arbitrary actual OS carrier and
arbitrary endpoint-pair test vector.

The first component rewrites the actual adjoint-synthesis coefficient as the
literal Wilson boundary/open-half Hilbert--Schmidt kernel pairing.  The second
component identifies the open-half `L²` input a.e. with the original canonical
positive-half pullback evaluated on one literal integer temporal section step.

Together these remove the abstract common-semigroup layer from the scalar
coefficient.  No completion, limit, eigen-equation, or Hamiltonian input is
used. -/
theorem canonicalRealizableOneStepActualSynthesis_pairKernelReceipt
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback E)
    (hInvariant : ∀ n,
      R₀.reflectionData.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).Carrier)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N) :
    let u :=
      R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfL2LinearMap
        hInvariant n (R.realizableCarrierTranslation hInvariant n 1 F)
    inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
            halfExtent N hN beta hbeta n u)) z =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          (halfExtent n) N hN (beta n) (hbeta n))
        (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
          (halfExtent n) N z)
        u ∧
    (fun x => u x) =ᵐ[
      periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N]
      (fun x =>
        R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S R₀.reflectionData halfExtent N hN beta hbeta
              R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).toPositiveTime F)
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
            (halfExtent n) N 1 x)) := by
  dsimp only
  constructor
  · simpa [physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator] using
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesis_pair_inner
        (halfExtent n) N hN (beta n) (hbeta n)
        (R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfL2LinearMap
          hInvariant n (R.realizableCarrierTranslation hInvariant n 1 F)) z
  · exact R₀.canonicalPositiveHalfL2_realizableCarrierTranslation_one_coeFn
      R hInvariant n F

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end
end MathlibAnalytic
end MGAP4D
