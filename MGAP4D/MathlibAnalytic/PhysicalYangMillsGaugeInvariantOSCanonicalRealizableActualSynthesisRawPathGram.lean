import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisPairKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureTransferKernelBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryHilbertSchmidtOperatorFactorization
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

/-- Literal raw Wilson path form of the boundary Gram analysis section.

The completed positive Gram feature is rewritten pointwise through the existing
positive-closure transfer coordinates.  Thus the only kernel visible here is
the partition-normalized unfixed `H+1`-slab Wilson path kernel; no abstract
operator or semigroup occurs in the definition. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryGramRawPathAnalysisSection
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) : ℝ :=
  ∫ b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N,
    (periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N (b, x)).1
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N (b, x)).2) * f b
    ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)

/-- The canonical Gram analysis section is exactly its literal normalized
unfixed Wilson path-kernel form, pointwise on the open-half configuration
space. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_eq_rawPath
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
        H N hN beta hbeta f x =
      periodicHypercubicEvenWilsonBoundaryGramRawPathAnalysisSection
        H N hN beta hbeta f x := by
  unfold periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
  unfold periodicHypercubicEvenWilsonBoundaryGramRawPathAnalysisSection
  apply integral_congr_ae
  filter_upwards with b
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedUnfixedPathKernel]

/-- The bounded Fréchet--Riesz Gram analysis operator itself therefore has the
literal normalized unfixed Wilson path-analysis representative almost
everywhere.  This is the exact bridge needed before applying temporal-gauge
reduction and one-step Markov/Fubini decomposition. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_coeFn_eq_rawPath
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    (fun x => periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      H N hN beta hbeta f x) =ᵐ[
        periodicHypercubicEvenOpenHalfHaarMeasure H N]
      periodicHypercubicEvenWilsonBoundaryGramRawPathAnalysisSection
        H N hN beta hbeta f := by
  have hSection :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_coeFn
      H N hN beta hbeta f
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_eq_analysisOperator]
    at hSection
  filter_upwards [hSection] with x hx
  rw [hx]
  exact periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_eq_rawPath
    H N hN beta hbeta f x

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

For an arbitrary OS carrier and arbitrary endpoint-pair test vector, the actual
synthesis coefficient is now an inner product of two open-half `L²` vectors
whose representatives are both explicit:

* the left vector is the normalized unfixed Wilson path analysis of the pair
  test kernel;
* the right vector is the original positive-half observable evaluated after one
  literal integer temporal-section step.

This removes the rectangular Hilbert--Schmidt wrapper from the remaining
finite-model calculation.  The next equality is therefore purely the finite
Haar/Markov/Fubini reduction extracting the adjacent temporal-gauge one-slab
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
    let a :=
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        (halfExtent n) N hN (beta n) (hbeta n) fz
    let u :=
      R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfL2LinearMap
        hInvariant n (R.realizableCarrierTranslation hInvariant n 1 F)
    inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
            halfExtent N hN beta hbeta n u)) z =
      inner ℝ a u ∧
    (fun x => a x) =ᵐ[
      periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N]
      periodicHypercubicEvenWilsonBoundaryGramRawPathAnalysisSection
        (halfExtent n) N hN (beta n) (hbeta n) fz ∧
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
  let a :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      (halfExtent n) N hN (beta n) (hbeta n) fz
  let u :=
    R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfL2LinearMap
      hInvariant n (R.realizableCarrierTranslation hInvariant n 1 F)
  have hPair :=
    R₀.canonicalRealizableOneStepActualSynthesis_pairKernelReceipt
      R hInvariant n F z
  constructor
  · calc
      inner ℝ
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
            (halfExtent n) N
            (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
              halfExtent N hN beta hbeta n u)) z =
        realL2HilbertSchmidtKernelPairing
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
            (halfExtent n) N hN (beta n) (hbeta n)) fz u := by
              simpa [fz, u] using hPair.1
      _ = inner ℝ a u := by
        symm
        simpa [fz, a] using
          periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
            (halfExtent n) N hN (beta n) (hbeta n) fz u
  · constructor
    · simpa [fz, a] using
        periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_coeFn_eq_rawPath
          (halfExtent n) N hN (beta n) (hbeta n) fz
    · simpa [u] using hPair.2

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end
end MathlibAnalytic
end MGAP4D
