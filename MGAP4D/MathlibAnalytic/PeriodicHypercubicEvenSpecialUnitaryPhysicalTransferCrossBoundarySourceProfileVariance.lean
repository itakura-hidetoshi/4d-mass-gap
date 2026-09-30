import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryConcreteTargetMean
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateKernelSectionExplicitMarkovKernel
import MGAP4D.MathlibAnalytic.ProbabilityMeasurePairwiseVarianceCancellation
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-!
# Cross-boundary source-profile variance

PR #4955 gives a pointwise pairwise estimate for the concrete opposite-boundary
target mean as the source value is varied.  This file packages the target
one-link law as an explicit measurable Markov kernel in that source value and
then applies the exact independent-pair cancellation from #4952.

The resulting one-copy estimate keeps the same coefficient

  c_cross(beta)^2

with no extra factor two, link-count factor, or volume factor.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance crossBoundarySourceProfileVarianceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundarySourceProfileVarianceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundarySourceProfileVarianceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundarySourceProfileVarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundarySourceProfileVarianceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundarySourceProfileVarianceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The ENNReal target-fiber weight, viewed as a jointly measurable family in
the opposite-boundary source value and the resampled target value. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberENNRealWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkENNRealWeight
    H N hN beta hbeta (Function.update B source k) A target g

/-- Joint measurability of the source/target-fiber weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberENNRealWeight_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measurable
      (Function.uncurry
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberENNRealWeight
          H N hN beta hbeta source target B A)) := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let U := Matrix.specialUnitaryGroup (Fin N) ℂ
  let w : G × G → ℝ := fun p =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta p.1 p.2
  let updateRight : U → G := fun k => Function.update B source k
  let updateLeft : U → G := fun g => Function.update A target g
  let pairMap : U × U → G × G := fun p => (updateRight p.1, updateLeft p.2)
  have hw : Continuous w := by
    simpa [w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_joint_continuous
        H N hN beta hbeta
  have hUpdateRight : Continuous updateRight := by
    simpa [
      updateRight,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N B source)
  have hUpdateLeft : Continuous updateLeft := by
    simpa [
      updateLeft,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N A target)
  have hPairMap : Continuous pairMap := by
    exact
      (hUpdateRight.comp continuous_fst).prodMk
        (hUpdateLeft.comp continuous_snd)
  have hWeight : Continuous (fun p : U × U => w (pairMap p)) :=
    hw.comp hPairMap
  change Measurable (fun p : U × U => ENNReal.ofReal (w (pairMap p)))
  exact (ENNReal.continuous_ofReal.comp hWeight).measurable

/-- The exact normalizing mass of the target-fiber weight. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  doobWeightMass
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberENNRealWeight
      H N hN beta hbeta source target B A k)

/-- The target-fiber normalizing mass is measurable in the source value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMass_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMass
        H N hN beta hbeta source target B A) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMass
    doobWeightMass
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberENNRealWeight_measurable
      H N hN beta hbeta source target B A).lintegral_kernel_prod_right
      (κ :=
        Kernel.const
          (Matrix.specialUnitaryGroup (Fin N) ℂ)
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

/-- Normalized measurable density in the source parameter and target value. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberENNRealWeight
      H N hN beta hbeta source target B A k g /
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMass
      H N hN beta hbeta source target B A k

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberDensity_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measurable
      (Function.uncurry
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberDensity
          H N hN beta hbeta source target B A)) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberDensity
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberENNRealWeight_measurable
      H N hN beta hbeta source target B A).div
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMass_measurable
        H N hN beta hbeta source target B A).comp measurable_fst)

/-- Explicit Markov kernel in the source value whose fiber is the actual
source-updated target one-link kernel-section law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Kernel
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  Kernel.withDensity
    (Kernel.const
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberDensity
      H N hN beta hbeta source target B A)

/-- The explicit parameterized kernel has exactly the desired literal fiber
measure at every source value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel
        H N hN beta hbeta source target B A k =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A target := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberENNRealWeight
      H N hN beta hbeta source target B A k
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel
  rw [
    Kernel.withDensity_apply _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberDensity_measurable
        H N hN beta hbeta source target B A)]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberDensity
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMass
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
    doobWeightedMeasure
  rfl

/-- The parameterized target-fiber kernel is a genuine Markov kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel
        H N hN beta hbeta source target B A) := by
  constructor
  intro k
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_apply
      H N hN beta hbeta source target B A k]
  have hLaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentTarget_eq_kernelSection_sourceUpdate
      H N hN beta hbeta B target source target k A
  rw [← hLaw]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B target source target k (B target) A

/-- The source-invariant target mean is strongly measurable as a scalar
function of the source value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_stronglyMeasurable_of_sourceInvariant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (hInvariant :
      ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right))
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A) := by
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel
      H N hN beta hbeta source target B A
  let phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A
  have hphi :
      StronglyMeasurable phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_stronglyMeasurable
      H N target F hF B A
  have hInt :
      StronglyMeasurable (fun k => ∫ g, phi g ∂κ k) :=
    hphi.integral_kernel
  have hEq :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
          H N hN beta hbeta source target F B A =
        fun k => ∫ g, phi g ∂κ k := by
    funext k
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_frozen_of_sourceInvariant
        H N hN beta hbeta source target F hInvariant B A k,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_apply
        H N hN beta hbeta source target B A k]
  rw [hEq]
  exact hInt

/-- The one-link source law obtained by swapping the fixed and fluctuating
boundaries is a probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedSourceFiber_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta A B source) := by
  have hLaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentTarget_eq_kernelSection_sourceUpdate
      H N hN beta hbeta A source source source (A source) B
  change IsProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source)
  have hLaw' :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta A source source source (A source) (A source) B =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta A B source := by
    simpa using hLaw
  rw [← hLaw']
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta A source source source (A source) (A source) B

/-- Uniform boundedness of the target mean by the concrete bounded-core
observable bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant :
      ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right))
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A k‖ ≤ |bound| := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta (Function.update B source k) A target
  let phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A target)
    rw [←
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_apply
        H N hN beta hbeta source target B A k]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_isMarkovKernel
        H N hN beta hbeta source target B A).isProbabilityMeasure k
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_frozen_of_sourceInvariant
      H N hN beta hbeta source target F hInvariant B A k]
  have hBoundPhi : ∀ᵐ g ∂μ, ‖phi g‖ ≤ |bound| := by
    filter_upwards with g
    unfold phi
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
    exact (hbound (B, Function.update A target g)).trans (le_abs_self bound)
  simpa using
    (norm_integral_le_of_norm_le_const hBoundPhi)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_memLp_two_swappedSourceFiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant :
      ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right))
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta A B source) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedSourceFiber_isProbabilityMeasure
      H N hN beta hbeta source B A
  apply MemLp.of_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_stronglyMeasurable_of_sourceInvariant
      H N hN beta hbeta source target F hF hInvariant B A).aestronglyMeasurable
    |bound|
  exact Filter.Eventually.of_forall fun k =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_norm_le
      H N hN beta hbeta source target F hF bound hbound hInvariant B A k

/-- Target conditional variance profile indexed by the opposite-boundary
source value. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  variance
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta (Function.update B source k) A target)

/-- The target conditional variance profile is strongly measurable in the
source value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_stronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
        H N hN beta hbeta source target F B A) := by
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel
      H N hN beta hbeta source target B A
  let phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A
  letI : IsMarkovKernel κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_isMarkovKernel
      H N hN beta hbeta source target B A
  have hphi :
      StronglyMeasurable phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_stronglyMeasurable
      H N target F hF B A
  have hphiSq : StronglyMeasurable (fun g => (phi g) ^ 2) := hphi.pow 2
  have hFirst :
      StronglyMeasurable (fun k => ∫ g, phi g ∂κ k) :=
    hphi.integral_kernel
  have hSecond :
      StronglyMeasurable (fun k => ∫ g, (phi g) ^ 2 ∂κ k) :=
    hphiSq.integral_kernel
  have hEq :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
          H N hN beta hbeta source target F B A =
        fun k =>
          (∫ g, (phi g) ^ 2 ∂κ k) -
            (∫ g, phi g ∂κ k) ^ 2 := by
    funext k
    have hphiLp :
        MemLp phi 2 (κ k) := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_apply
          H N hN beta hbeta source target B A k]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
          H N hN beta hbeta source target F hF bound hbound B A k
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
    rw [
      ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_apply
        H N hN beta hbeta source target B A k]
    simpa only [Pi.pow_apply] using variance_eq_sub hphiLp
  rw [hEq]
  exact hSecond.sub (hFirst.pow 2)

/-- Pointwise target variance is bounded by the square of the bounded-core
observable bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_le_bound_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
        H N hN beta hbeta source target F B A k ≤ |bound| ^ 2 := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta (Function.update B source k) A target
  let phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A target)
    rw [←
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_apply
        H N hN beta hbeta source target B A k]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetFiberMarkovKernel_isMarkovKernel
        H N hN beta hbeta source target B A).isProbabilityMeasure k
  have hphiLp :
      MemLp phi 2 μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
      H N hN beta hbeta source target F hF bound hbound B A k
  have hVar :
      variance phi μ ≤ ∫ g, (phi g) ^ 2 ∂μ :=
    variance_le_expectation_sq hphiLp.aestronglyMeasurable
  have hSqInt : Integrable (fun g => (phi g) ^ 2) μ := hphiLp.integrable_sq
  have hConstInt : Integrable (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => |bound| ^ 2) μ := integrable_const _
  have hPoint : ∀ᵐ g ∂μ, (phi g) ^ 2 ≤ |bound| ^ 2 := by
    filter_upwards with g
    have hg :
        ‖phi g‖ ≤ |bound| := by
      unfold phi
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      exact (hbound (B, Function.update A target g)).trans (le_abs_self bound)
    have hnonneg : 0 ≤ |bound| := abs_nonneg _
    simpa [Real.norm_eq_abs] using
      (sq_le_sq₀ (abs_nonneg (phi g)) hnonneg).2 hg
  have hInt :
      (∫ g, (phi g) ^ 2 ∂μ) ≤ |bound| ^ 2 := by
    calc
      (∫ g, (phi g) ^ 2 ∂μ) ≤
          ∫ _ : Matrix.specialUnitaryGroup (Fin N) ℂ, |bound| ^ 2 ∂μ :=
        integral_mono_ae hSqInt hConstInt hPoint
      _ = |bound| ^ 2 := by simp
  exact hVar.trans hInt

/-- The target conditional variance profile is integrable under the swapped
source fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_integrable_swappedSourceFiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
        H N hN beta hbeta source target F B A)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta A B source) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
      H N hN beta hbeta source target F B A
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedSourceFiber_isProbabilityMeasure
      H N hN beta hbeta source B A
  have hVStrong :
      StronglyMeasurable V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_stronglyMeasurable
      H N hN beta hbeta source target F hF bound hbound B A
  have hVNonneg : ∀ k, 0 ≤ V k := fun k => variance_nonneg _ _
  have hVBound : ∀ k, V k ≤ |bound| ^ 2 := fun k =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_le_bound_sq
      H N hN beta hbeta source target F hF bound hbound B A k
  exact Integrable.mono'
    (integrable_const (μ := μ) (|bound| ^ 2))
    hVStrong.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hVNonneg k)]
      exact hVBound k)

/-- Exact one-copy source-profile variance estimate obtained by combining
#4955 with the independent-pair factor-two cancellation of #4952. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_variance_le_crossCoefficient_sq_mul_integral_targetVarianceProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant :
      ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right))
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    variance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
          H N hN beta hbeta source target F B A)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta A B source) ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta) ^ 2 *
        ∫ k,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
            H N hN beta hbeta source target F B A k
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta A B source := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
      H N hN beta hbeta source target F B A
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
      H N hN beta hbeta source target F B A
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
      beta
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedSourceFiber_isProbabilityMeasure
      H N hN beta hbeta source B A
  have hM :
      MemLp M 2 μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_memLp_two_swappedSourceFiber
      H N hN beta hbeta source target F hF bound hbound hInvariant B A
  have hV :
      Integrable V μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_integrable_swappedSourceFiber
      H N hN beta hbeta source target F hF bound hbound B A
  have hPair : ∀ k₁ k₂,
      (M k₁ - M k₂) ^ 2 ≤ c ^ 2 * (V k₁ + V k₂) := by
    intro k₁ k₂
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_pairwise_sq_le_varianceSum
        H N hN beta hbeta hBetaLt source target F hF bound hbound hInvariant B A k₁ k₂
  simpa [μ, M, V, c] using
    (realProbability_variance_le_coeff_sq_mul_integral_of_pairwise_sq_le
      μ M V hM hV c hPair)

end

end MathlibAnalytic
end MGAP4D
