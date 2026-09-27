import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointStageResidualPathLoss
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairResponseResidualStrictCutoff
import Mathlib.Tactic

/-!
# Strict response energy below the exact sweep path-loss carrier

PR #4858 charges the actual link-indexed full response sums to

  rhoResp(s,beta) * ofReal(6 * sweepPathLoss(f)).

PR #4859 supplies a strictly positive, volume-independent interval on which

  rhoResp(s,beta) < 1.

This file composes those results.  On the strict response cutoff, the complete
vacuum-integrated response energy is therefore bounded by the exact ordered
one-link sweep path-loss carrier itself:

  responseEnergy <= ofReal(6 * sweepPathLoss(f)).

We also package the positive ENNReal energy gap

  1 - rhoResp(s,beta) > 0,

which is the scalar quantity needed by later coercive absorption.

No new analytic estimate, probability law, factor two, response symmetry, or
finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance strictResponsePathLossSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance strictResponsePathLossSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Positive response-energy gap below one. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualEnergyGap
    (s beta : ℝ) : ℝ≥0∞ :=
  1 -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
      s beta

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualEnergyGap_pos
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
          s hs) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualEnergyGap
        s beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualEnergyGap
  exact
    tsub_pos_iff_lt.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff_spec
        s hs beta hbeta hcut)

/-- On the strict response cutoff, choose the canonical-prefix family so that
the actual full response energy is below the exact sweep path-loss energy
itself. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_sixSweepPathLoss_ofReal
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
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
        ENNReal.ofReal
          (6 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
              H N hN beta hbeta f) := by
  have hShell :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff_le_shellCutoff
        s hs)
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSweepPathLoss_ofReal
        N hN s hs beta hbeta hShell H distinguishedSource f hf with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hResponse⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, ?_⟩
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
      s beta
  let E : ℝ≥0∞ :=
    ENNReal.ofReal
      (6 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f)
  have hRho : rho < 1 := by
    simpa [rho] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff_spec
        s hs beta hbeta hcut
  have hMul : rho * E ≤ E := by
    calc
      rho * E ≤ 1 * E := by
        gcongr
        exact hRho.le
      _ = E := one_mul E
  exact hResponse.trans (by simpa [rho, E] using hMul)

end

end MGAP4D.MathlibAnalytic
