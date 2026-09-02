import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisPairKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureTransferKernelBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance canonicalRealizableRawPathGramSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩

local instance canonicalRealizableRawPathGramTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalRealizableRawPathGramCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalRealizableRawPathGramSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalRealizableRawPathGramMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalRealizableRawPathGramBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance canonicalRealizableRawPathGramSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalRealizableRawPathGramBoundaryHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance canonicalRealizableRawPathGramOpenHalfHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- Literal normalized unfixed Wilson path kernel on the same boundary ×
open-half carrier used by the canonical rectangular Gram `L²` kernel. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryGramRawPathRectangularKernel
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (p : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) : ℝ :=
  periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
      H N hN beta hbeta *
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
      H N beta
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N p).1
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N p).2

/-- The canonical rectangular boundary/open-half Gram `L²` kernel has the
literal normalized unfixed `H+1`-slab Wilson path kernel as an almost-everywhere
representative.  This bypasses any auxiliary scalar-analysis-section layer. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn_eq_rawPath
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun p =>
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN beta hbeta p) =ᵐ[
      (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)]
      periodicHypercubicEvenWilsonBoundaryGramRawPathRectangularKernel
        H N hN beta hbeta := by
  let hmem :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
      H N hN beta hbeta
  have hKernel :
      (fun p =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta p) =ᵐ[
        (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)]
        (fun p =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta p.1 p.2) := by
    simpa [periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2,
      periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using hmem.coeFn_toLp
  filter_upwards [hKernel] with p hp
  rw [hp]
  simpa [periodicHypercubicEvenWilsonBoundaryGramRawPathRectangularKernel] using
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedUnfixedPathKernel
      H N hN beta hbeta p.1 p.2)

/-- Pair-coordinate diagonal Gram identity.

After transporting the shared boundary to the actual ordered spatial-endpoint
pair carrier, synthesis of the analysis vector has quadratic coefficient equal
to the exact analysis norm square.  This is the concrete pair-coordinate form
of `A† A` and introduces no duplicate Gram operator. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesis_analysis_pair_inner_eq_norm_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    let f :=
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N z
    let a :=
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta f
    inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          H N
          (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
            H N hN beta hbeta a)) z =
      ‖a‖ ^ 2 := by
  dsimp only
  let f :=
    periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N z
  let a :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      H N hN beta hbeta f
  calc
    inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          H N
          (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
            H N hN beta hbeta a)) z =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta) f a := by
        simpa [f, a] using
          periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesis_pair_inner
            H N hN beta hbeta a z
    _ = inner ℝ a a := by
      symm
      simpa [f, a] using
        periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
          H N hN beta hbeta f a
    _ = ‖a‖ ^ 2 := by
      exact real_inner_self_eq_norm_sq a

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

/-- Raw-path Gram receipt for one actual realizable lattice step.

For an arbitrary OS carrier and endpoint-pair test vector, the actual synthesis
coefficient remains exactly the canonical rectangular Gram pairing, while the
rectangular Gram kernel and the translated open-half input are now both exposed
by literal finite Wilson representatives.  The next theorem is therefore only
the finite Haar/Markov/Fubini decomposition extracting the adjacent one-slab
kernel. -/
theorem canonicalRealizableOneStepActualSynthesis_rawPathGramReceipt
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
    let fz :=
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent n) N z
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
          (halfExtent n) N hN (beta n) (hbeta n)) fz u ∧
    (fun p =>
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        (halfExtent n) N hN (beta n) (hbeta n) p) =ᵐ[
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)]
      periodicHypercubicEvenWilsonBoundaryGramRawPathRectangularKernel
        (halfExtent n) N hN (beta n) (hbeta n) ∧
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
  let fz :=
    periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent n) N z
  let u :=
    R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfL2LinearMap
      hInvariant n (R.realizableCarrierTranslation hInvariant n 1 F)
  have hPair :=
    R₀.canonicalRealizableOneStepActualSynthesis_pairKernelReceipt
      R hInvariant n F z
  constructor
  · simpa [fz, u] using hPair.1
  · constructor
    · exact
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn_eq_rawPath
          (halfExtent n) N hN (beta n) (hbeta n)
    · simpa [u] using hPair.2

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end
end MathlibAnalytic
end MGAP4D
