import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFullResponseSumEnergy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepStageLocalProfileExactResidual
import Mathlib.Tactic

/-!
# Charge the actual full response sums to exact canonical stage residuals

PR #4849 realizes the target-law response sums as genuine source-specific L2
vectors. PR #4846 bounds the corresponding fixed-background amplitude energy
by the sum of canonical target fiber variances. PR #4853 preserves the exact
canonical prefix of every selected sweep-stage representative, and PR #4856
identifies the local profile at that link with the norm of the actual Hilbert
stage residual.

This file first exposes the missing arbitrary-family version of the full
response-energy estimate:

  integral_C sum_source ||sum_target Response(source,target)||^2
    <= rhoResp * sum_target CanonicalFiberVariance(target).

It then chooses the canonical-prefix family and replaces every target variance
by the squared norm of the exact stage residual at that preserved prefix.

Thus the response-energy side is now charged directly to genuine Hilbert
vectors of the ordered one-link sweep, not to an abstract profile majorant.

No response symmetry, target reordering, finite-cardinality factor, factor two,
or new cutoff is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fullResponseExactStageResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fullResponseExactStageResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fullResponseExactStageResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fullResponseExactStageResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fullResponseExactStageResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fullResponseExactStageResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual Hilbert residual at the preserved canonical prefix immediately
before one spatial link. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (pre :
      List
        (PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenSpatialSliceLinkColor H e)))
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
      H N hN beta hbeta
      (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta
      (periodicHypercubicEvenSpatialSliceLinkColor H e)
      (⟨e, rfl⟩ :
        PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenSpatialSliceLinkColor H e))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
        H N hN beta hbeta
        (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f)

/-- Arbitrary link-indexed bounded representatives: the vacuum-integrated
actual full response sums are bounded by the canonical target-fiber variances. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_canonicalFiberVarianceFunctional_sum
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    (∫⁻ C,
      ENNReal.ofReal
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          norm
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                (F target) (hF target) (bound target) (hbound target) C 0) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
            H N hN beta hbeta target (F target) := by
  have hAmplitude :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_canonicalFiberVarianceFunctional_sum
      N hN s hs beta hbeta hcut H distinguishedSource
      F hF bound hbound
  have hPoint :
      ∀ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            norm
              (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                  H N hN beta hbeta C distinguishedSource source target
                  (C distinguishedSource) (C source)
                  (F target) (hF target) (bound target) (hbound target) C 0) ^ 2) ≤
          ENNReal.ofReal
            (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
              (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
                  H N hN beta hbeta C distinguishedSource
                  (F target) (hF target) (bound target) (hbound target)
                  source target) ^ 2) := by
    intro C
    exact
      ENNReal.ofReal_le_ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFullResponseL2_sum_norm_sq_sum_le_fixedBackgroundResponseAmplitude_sum_sq
          H N hN beta hbeta C distinguishedSource
          F hF bound hbound)
  exact
    (lintegral_mono hPoint).trans hAmplitude

/-- For the canonical-prefix family, each canonical fiber variance is bounded
by the squared norm of the exact Hilbert stage residual at the preserved
prefix. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_canonicalPrefix_canonicalFiberVariance_sum_le_stageResidual_norm_sq_sum_ofReal
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (pre suffix :
      (e : PeriodicHypercubicEvenSpatialSliceLink H) →
        List
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)))
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e)
    (hSplit :
      ∀ e,
        (Finset.univ :
          Finset
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
          pre e ++
            (⟨e, rfl⟩ :
              PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
              suffix e)
    (hFresh :
      ∀ e,
        (⟨e, rfl⟩ :
          PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre e)
    (hRep :
      ∀ e,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta
            (F e) (hF e) (bound e) (hbound e) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e)
            (pre e) f)
    (hLocal :
      ∀ e,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f e) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta e (F e)) ≤
      ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          norm
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
              H N hN beta hbeta e (pre e) f) ^ 2) := by
  classical
  have hEach :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
            H N hN beta hbeta e (F e) ≤
          ENNReal.ofReal
            (norm
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
                H N hN beta hbeta e (pre e) f) ^ 2) := by
    intro e
    have hProfile :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
        H N hN beta hbeta e (pre e) (suffix e) f
        (hSplit e) (hFresh e)
    have hLocal' :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ≤
          norm
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
              H N hN beta hbeta e (pre e) f) := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector]
        using (hLocal e).trans_eq hProfile
    have hSq :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ^ 2 ≤
          norm
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
              H N hN beta hbeta e (pre e) f) ^ 2 :=
      (sq_le_sq₀
        (norm_nonneg _)
        (norm_nonneg _)).2 hLocal'
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta e (F e) =
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
              H N hN beta hbeta e
              (F e) (hF e) (bound e) (hbound e)‖ ^ 2) := by
            symm
            exact
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_norm_sq_ofReal_eq_variance
                H N hN beta hbeta e
                (F e) (hF e) (bound e) (hbound e)
      _ ≤
        ENNReal.ofReal
          (norm
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
              H N hN beta hbeta e (pre e) f) ^ 2) :=
        ENNReal.ofReal_le_ofReal hSq
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta e (F e)) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ENNReal.ofReal
          (norm
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
              H N hN beta hbeta e (pre e) f) ^ 2) := by
        exact Finset.sum_le_sum (fun e _ => hEach e)
    _ =
      ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          norm
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
              H N hN beta hbeta e (pre e) f) ^ 2) := by
        symm
        simpa using
          (ENNReal.ofReal_sum_of_nonneg
            (s := (Finset.univ :
              Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
            (f := fun e =>
              norm
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
                  H N hN beta hbeta e (pre e) f) ^ 2)
            (fun e _ => sq_nonneg _))

/-- Choose the canonical-prefix representatives so that the actual full
response energy is charged directly to the exact stage-residual vectors. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_stageResidual_norm_sq_sum_ofReal
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (pre suffix :
        (e : PeriodicHypercubicEvenSpatialSliceLink H) →
          List
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e)))
      (F :
        PeriodicHypercubicEvenSpatialSliceLink H →
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : ∀ e, StronglyMeasurable (F e))
      (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
      (hbound : ∀ e z, ‖F e z‖ ≤ bound e),
      (∀ e,
        (Finset.univ :
          Finset
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
            pre e ++
              (⟨e, rfl⟩ :
                PeriodicHypercubicEvenFixedSpatialColorLink H
                  (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
                suffix e) ∧
      (∀ e,
        (⟨e, rfl⟩ :
          PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre e) ∧
      (∀ e,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta
            (F e) (hF e) (bound e) (hbound e) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e)
            (pre e) f) ∧
      (∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            norm
              (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                  H N hN beta hbeta C distinguishedSource source target
                  (C distinguishedSource) (C source)
                  (F target) (hF target) (bound target) (hbound target) C 0) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
            s beta *
          ENNReal.ofReal
            (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              norm
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
                  H N hN beta hbeta e (pre e) f) ^ 2) := by
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_with_canonicalPrefixWitness
        H N hN beta hbeta f hf with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hLocal⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, ?_⟩
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_canonicalFiberVarianceFunctional_sum
      N hN s hs beta hbeta hcut H distinguishedSource
      F hF bound hbound
  have hVariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_canonicalPrefix_canonicalFiberVariance_sum_le_stageResidual_norm_sq_sum_ofReal
      H N hN beta hbeta f
      pre suffix F hF bound hbound
      hSplit hFresh hRep hLocal
  exact
    hResponse.trans
      (mul_le_mul_right
        hVariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta))

end

end MGAP4D.MathlibAnalytic
