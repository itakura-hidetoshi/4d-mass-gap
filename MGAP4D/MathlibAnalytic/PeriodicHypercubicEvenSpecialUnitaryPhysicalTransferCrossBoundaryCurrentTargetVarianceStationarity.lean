import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryCurrentTargetVarianceSection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkFubiniCompatibility
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFullKernelSectionLaw
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-!
# Cross-boundary current target variance: full-background measurability and stationarity

PR #4958 rewrites the cross-boundary target-variance profile as the source
section of one current target variance.  To outer-integrate that estimate we
must apply the actual fixed-right one-link heat-bath stationarity in the
opposite boundary variable.

The remaining technical premise is measurability in the complete opposite
boundary, not merely along one already-fixed source-coordinate section.  This
file builds the literal target fiber as an explicit Markov kernel parameterized
by the complete opposite boundary, proves the current target variance strongly
measurable, and then applies the existing exact one-link stationarity theorem.

No comparison coefficient, cutoff, factor two, link-count factor, or volume
factor is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance crossBoundaryCurrentTargetVarianceStationaritySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryCurrentTargetVarianceStationaritySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryCurrentTargetVarianceStationaritySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryCurrentTargetVarianceStationaritySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryCurrentTargetVarianceStationaritySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryCurrentTargetVarianceStationaritySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The target one-link ENNReal weight, parameterized by the complete current
opposite-boundary configuration. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberENNRealWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkENNRealWeight
    H N hN beta hbeta B A target g

/-- Joint measurability in the complete opposite boundary and target-fiber
value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberENNRealWeight_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measurable
      (Function.uncurry
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberENNRealWeight
          H N hN beta hbeta target A)) := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let U := Matrix.specialUnitaryGroup (Fin N) ℂ
  let w : G × G → ℝ := fun p =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta p.1 p.2
  let updateTarget : U → G := fun g => Function.update A target g
  let pairMap : G × U → G × G := fun p => (p.1, updateTarget p.2)
  have hw : Continuous w := by
    simpa [w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_joint_continuous
        H N hN beta hbeta
  have hUpdateTarget : Continuous updateTarget := by
    simpa [
      updateTarget,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N A target)
  have hPairMap : Continuous pairMap := by
    exact continuous_fst.prodMk (hUpdateTarget.comp continuous_snd)
  have hWeight : Continuous (fun p : G × U => w (pairMap p)) :=
    hw.comp hPairMap
  change Measurable (fun p : G × U => ENNReal.ofReal (w (pairMap p)))
  exact (ENNReal.continuous_ofReal.comp hWeight).measurable

/-- Exact normalizing mass of the current target fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ≥0∞ :=
  doobWeightMass
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberENNRealWeight
      H N hN beta hbeta target A B)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMass_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMass
        H N hN beta hbeta target A) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMass
    doobWeightMass
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberENNRealWeight_measurable
      H N hN beta hbeta target A).lintegral_kernel_prod_right
      (κ :=
        Kernel.const
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

/-- Normalized current target-fiber density, jointly measurable in the
complete opposite boundary and target value. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberENNRealWeight
      H N hN beta hbeta target A B g /
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMass
      H N hN beta hbeta target A B

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberDensity_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measurable
      (Function.uncurry
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberDensity
          H N hN beta hbeta target A)) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberDensity
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberENNRealWeight_measurable
      H N hN beta hbeta target A).div
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMass_measurable
        H N hN beta hbeta target A).comp measurable_fst)

/-- Explicit Markov kernel in the complete opposite boundary whose fiber is
the literal current target one-link kernel-section law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  Kernel.withDensity
    (Kernel.const
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberDensity
      H N hN beta hbeta target A)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel
        H N hN beta hbeta target A B =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta B A target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel
  rw [
    Kernel.withDensity_apply _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberDensity_measurable
        H N hN beta hbeta target A)]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberDensity
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMass
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
    doobWeightedMeasure
  rfl

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel
        H N hN beta hbeta target A) := by
  constructor
  intro B
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel_apply
      H N hN beta hbeta target A B]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedSourceFiber_isProbabilityMeasure
      H N hN beta hbeta target A B

/-- The current target conditional variance is strongly measurable in the
complete opposite-boundary configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_stronglyMeasurable_in_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (fun B =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
          H N hN beta hbeta target F B A) := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let U := Matrix.specialUnitaryGroup (Fin N) ℂ
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel
      H N hN beta hbeta target A
  let phi : G → U → ℝ := fun B g => F (B, Function.update A target g)
  letI : IsMarkovKernel κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel_isMarkovKernel
      H N hN beta hbeta target A
  have hPhi :
      StronglyMeasurable (Function.uncurry phi) := by
    exact hF.comp_measurable
      (measurable_fst.prodMk
        ((measurable_update A).comp measurable_snd))
  have hPhiSq :
      StronglyMeasurable (Function.uncurry (fun B g => (phi B g) ^ 2)) := by
    simpa only [Function.uncurry_apply_pair] using hPhi.pow 2
  have hFirst :
      StronglyMeasurable (fun B => ∫ g, phi B g ∂κ B) :=
    hPhi.integral_kernel_prod_right
  have hSecond :
      StronglyMeasurable (fun B => ∫ g, (phi B g) ^ 2 ∂κ B) :=
    hPhiSq.integral_kernel_prod_right
  have hMemLp : ∀ B : G, MemLp (phi B) 2 (κ B) := by
    intro B
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel_apply
        H N hN beta hbeta target A B]
    simpa [phi] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
        H N hN beta hbeta target target F hF bound hbound B A (B target)
  have hEq :
      (fun B =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
          H N hN beta hbeta target F B A) =
        fun B =>
          (∫ g, (phi B g) ^ 2 ∂κ B) -
            (∫ g, phi B g ∂κ B) ^ 2 := by
    funext B
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
    rw [
      ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetFiberMarkovKernel_apply
        H N hN beta hbeta target A B]
    simpa only [phi, Pi.pow_apply] using variance_eq_sub (hMemLp B)
  rw [hEq]
  exact hSecond.sub (hFirst.pow 2)

/-- Uniform pointwise bound for the current target variance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_le_bound_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
        H N hN beta hbeta target F B A ≤
      |bound| ^ 2 := by
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_currentValue_eq_currentTargetVariance
      H N hN beta hbeta target target F B A]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_le_bound_sq
      H N hN beta hbeta target target F hF bound hbound B A (B target)

/-- The ENNReal current target variance is measurable in the complete
opposite boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_ofReal_measurable_in_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measurable
      (fun B =>
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
            H N hN beta hbeta target F B A)) := by
  exact
    ENNReal.continuous_ofReal.measurable.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_stronglyMeasurable_in_left
        H N hN beta hbeta target F hF bound hbound A).measurable

/-- Exact one-link stationarity return for the current target variance.
The source update is averaged under the swapped/fixed-right source fiber and
returns to the same current target variance under the unswept section law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_sourceUpdate_lintegral_eq_current
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ B,
      (∫⁻ k,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
            H N hN beta hbeta target F
            (Function.update B source k) A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta A B source)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta A) =
      ∫⁻ B,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
            H N hN beta hbeta target F B A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta A := by
  let Phi :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun B =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
          H N hN beta hbeta target F B A)
  have hPhi : Measurable Phi := by
    simpa [Phi] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_ofReal_measurable_in_left
        H N hN beta hbeta target F hF bound hbound A
  have hStationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_lintegral_oneLinkFiber
      H N hN beta hbeta A source source source
      (A source) (A source) Phi hPhi
  simpa only [
    Phi,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure]
    using hStationary

end

end MathlibAnalytic
end MGAP4D
