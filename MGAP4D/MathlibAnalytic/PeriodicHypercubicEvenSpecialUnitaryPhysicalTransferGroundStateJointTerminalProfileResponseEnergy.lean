import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectTerminalProfileRenewal
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFullResponseExactStageResidual
import Mathlib.Tactic

/-!
# Response energy on a generic link profile and the terminal sweep profile

The existing response theorem bounds the actual full response-sum energy by
the sum of canonical target-fiber variances.  The stage-specific downstream
result then specializes those variances to canonical first-sweep residuals.

For the renewal route we instead need to use the PR #4895 cyclic second-sweep
representatives and the PR #4896 terminal profile.

This file factors out the missing generic profile bridge:

  if ||r_e|| <= profile(e) for every target e,

then

  sum_e CanonicalFiberVariance(e) <= ofReal(sum_e profile(e)^2),

and therefore

  fullResponseEnergy
    <= rhoResp(s,beta) * ofReal(sum_e profile(e)^2).

Finally the PR #4895 representative family is inserted with the PR #4896
terminal profile, giving a response-energy bound charged exactly to

  6 * terminalSweepPathLoss(f).

No response symmetry, source/target reordering, positive-beta commutativity,
finite-cardinality factor, factor two, or new cutoff is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance terminalProfileResponseEnergySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance terminalProfileResponseEnergySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance terminalProfileResponseEnergySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance terminalProfileResponseEnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance terminalProfileResponseEnergySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance terminalProfileResponseEnergySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Generic coefficient-one bridge from linkwise canonical localPart bounds to
the summed canonical target-fiber variance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointLinkIndexedCanonicalFiberVariance_sum_le_profile_sq_sum_ofReal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ e, 0 ≤ profile e)
    (hLocal :
      ∀ e,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ≤
          profile e) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta e (F e)) ≤
      ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile e ^ 2) := by
  classical
  have hEach :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
            H N hN beta hbeta e (F e) ≤
          ENNReal.ofReal (profile e ^ 2) := by
    intro e
    have hSq :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ^ 2 ≤
          profile e ^ 2 :=
      (sq_le_sq₀
        (norm_nonneg _)
        (hProfileNonneg e)).2
        (hLocal e)
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
      _ ≤ ENNReal.ofReal (profile e ^ 2) :=
        ENNReal.ofReal_le_ofReal hSq
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta e (F e)) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ENNReal.ofReal (profile e ^ 2) := by
          exact Finset.sum_le_sum (fun e _ => hEach e)
    _ =
      ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile e ^ 2) := by
          symm
          simpa using
            (ENNReal.ofReal_sum_of_nonneg
              (s := (Finset.univ :
                Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
              (f := fun e => profile e ^ 2)
              (fun e _ => sq_nonneg (profile e)))

/-- Generic response-energy receiver on any nonnegative link profile dominating
the canonical localPart norms. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_profile_sq_sum_ofReal
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
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
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ e, 0 ≤ profile e)
    (hLocal :
      ∀ e,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ≤
          profile e) :
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
          (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile e ^ 2) := by
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_canonicalFiberVarianceFunctional_sum
      N hN s hs beta hbeta hcut H distinguishedSource
      F hF bound hbound
  have hVariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointLinkIndexedCanonicalFiberVariance_sum_le_profile_sq_sum_ofReal
      H N hN beta hbeta F hF bound hbound
      profile hProfileNonneg hLocal
  exact
    hResponse.trans
      (mul_le_mul_left'
        hVariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta))

/-- Choose the cyclic second-sweep representatives from PR #4895 and charge
their actual full response-sum energy to the exact terminal profile energy,
equivalently to six times the normalized terminal sweep path loss. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSecondSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_sixTerminalSweepPathLoss_ofReal
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
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
          realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e))
            (suffix e ++ pre e)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta e
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                H N hN beta hbeta
                (periodicHypercubicEvenSpatialSliceLinkColor H e)
                (pre e) f))) ∧
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
            (6 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
                H N hN beta hbeta f) := by
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSecondSweep_linkIndexedRepresentatives_with_cyclicPrefixWitness
        H N hN beta hbeta f hf with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hLocal⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, ?_⟩
  let profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
      H N hN beta hbeta f
  have hProfileNonneg : ∀ e, 0 ≤ profile e := by
    intro e
    simpa [profile] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_nonneg
        H N hN beta hbeta f e
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_profile_sq_sum_ofReal
      N hN s hs beta hbeta hcut H distinguishedSource
      F hF bound hbound profile hProfileNonneg
      (by
        intro e
        simpa [profile] using hLocal e)
  have hTerminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_normalized_sq_sum_eq_terminalSweepPathLoss
      H N hN beta hbeta f
  have hSum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile e ^ 2) =
        6 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
            H N hN beta hbeta f := by
    change
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
          H N hN beta hbeta f e ^ 2) =
        6 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
            H N hN beta hbeta f
    nlinarith
  rw [hSum] at hResponse
  exact hResponse

end

end MGAP4D.MathlibAnalytic
