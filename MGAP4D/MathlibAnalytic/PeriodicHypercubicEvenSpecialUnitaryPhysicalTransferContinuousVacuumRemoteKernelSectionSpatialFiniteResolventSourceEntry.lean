import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanCovarianceTelescope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationMass
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalCrossingDenominatorFloor
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance remoteKernelSectionSpatialFiniteResolventSourceEntrySpecialUnitaryIsTopologicalGroup
    (N : Nat) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance remoteKernelSectionSpatialFiniteResolventSourceEntrySpecialUnitaryCompactSpace
    (N : Nat) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupCompactSpace N

local instance remoteKernelSectionSpatialFiniteResolventSourceEntrySpecialUnitarySecondCountableTopology
    (N : Nat) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupSecondCountableTopology N

local instance remoteKernelSectionSpatialFiniteResolventSourceEntrySpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionSpatialFiniteResolventSourceEntrySpecialUnitaryBorelSpace
    (N : Nat) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupBorelSpace N

local instance remoteKernelSectionSpatialFiniteResolventSourceEntrySpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionSpatialFiniteResolventSourceEntryKernelSectionProbabilityMeasure
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
    H N hN beta hbeta C

/-- The exact coordinate-variation profile of the source crossing-ratio
observable.  It is supported on the single physical source fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation
    (H : Nat)
    (beta : Real)
    (source e : PeriodicHypercubicEvenSpatialSliceLink H) : Real :=
  if e = source then Real.exp (2 * beta) - Real.exp (-2 * beta) else 0

/-- The singleton source crossing-ratio variation profile is nonnegative for
nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation_nonneg
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    forall e,
      0 <=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation
          H beta source e := by
  intro e
  by_cases he : e = source
  · subst e
    simp only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation,
      if_pos]
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation,
      he]

/-- Varying one left fiber changes the source crossing-ratio only at the source
fiber, where the exact interval width exp(2 beta)-exp(-2 beta) is a valid
variation bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatio_variation_le
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) Complex) :
    forall
      (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
      |(specialUnitaryWilsonRelativeKernel N beta ((Function.update C e u) source) h /
            specialUnitaryWilsonRelativeKernel N beta ((Function.update C e u) source) k) -
        (specialUnitaryWilsonRelativeKernel N beta ((Function.update C e v) source) h /
            specialUnitaryWilsonRelativeKernel N beta ((Function.update C e v) source) k)| <=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation
          H beta source e := by
  intro e C u v
  by_cases he : e = source
  · subst e
    simp [Function.update_apply]
    have hu :=
      specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
        N hN beta hbeta u h k
    have hv :=
      specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
        N hN beta hbeta v h k
    simp only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation,
      if_pos]
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  · have hsu : (Function.update C e u) source = C source := by
      simp [Function.update_apply, he, Ne.symm he]
    have hsv : (Function.update C e v) source = C source := by
      simp [Function.update_apply, he, Ne.symm he]
    rw [hsu, hsv, sub_self, abs_zero]
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation,
      he]

/-- The physical-left variation profile of the actual two-step terminal target
observable.  It is the already-proved singleton target-ratio profile propagated
for exactly two restricted random-scan steps. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (target e : PeriodicHypercubicEvenSpatialSliceLink H) : Real :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
    H beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
      H beta target)
    2 (Sum.inl e)

/-- The propagated two-step terminal left-variation profile is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile_nonneg
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    forall e,
      0 <=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile
          H beta hbeta target e := by
  intro e
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
        H beta target)
      2 (Sum.inl e)

/-- The actual two-step terminal target observable is strongly measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable_stronglyMeasurable
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g1 g2 k : Matrix.specialUnitaryGroup (Fin N) Complex) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
        H N hN beta hbeta B target source g1 g2 k) := by
  let F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
    fun C =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g1 /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g2
  have hF : StronglyMeasurable F := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_stronglyMeasurable
        H N beta B target g1 g2
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable,
    F] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
      H N hN beta hbeta B target source g2 k F hF 2

/-- Under a remote target/source geometry, the actual two-step terminal target
observable lies in L2 of the fixed-k kernel-section probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (g1 g2 k : Matrix.specialUnitaryGroup (Fin N) Complex) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
        H N hN beta hbeta B target source g1 g2 k)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  let F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
    fun C =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g1 /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g2
  have hFStrong : StronglyMeasurable F := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_stronglyMeasurable
        H N beta B target g1 g2
  have hF : MemLp F 2 mu := by
    refine MemLp.of_bound hFStrong.aestronglyMeasurable (Real.exp (16 * beta)) ?_
    exact ae_of_all _ fun C => by
      rw [abs_of_pos
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_pos
          H N beta C B target g1 g2)]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
          H N hN beta hbeta C B target g1 g2
  simpa [
    mu,
    F,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScanExpectationIterate_memLp_two
      H N hN beta hbeta B hne hNoShare g2 k F hF 2

/-- The propagated two-step profile controls every physical-left fiber
variation of the actual terminal target observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable_fiberVariation_le
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g1 g2 k : Matrix.specialUnitaryGroup (Fin N) Complex) :
    forall
      (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
          H N hN beta hbeta B target source g1 g2 k (Function.update C e u) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
          H N hN beta hbeta B target source g1 g2 k (Function.update C e v)| <=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile
          H beta hbeta target e := by
  let F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
    fun C =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g1 /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g2
  let variation : PeriodicHypercubicEvenSpatialSliceLink H -> Real :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
      H beta target
  have hFStrong : StronglyMeasurable F := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_stronglyMeasurable
        H N beta B target g1 g2
  have hVariationNonneg : forall e, 0 <= variation e := by
    simpa [variation] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
        H beta target
  have hVariation :
      forall
        (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |F (Function.update C e u) - F (Function.update C e v)| <= variation e := by
    simpa [F, variation] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_variation_le
        H N hN beta hbeta B target g1 g2
  intro e C u v
  simpa [
    F,
    variation,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le
      H N hN beta hbeta B target source g2 k F hFStrong variation
      hVariationNonneg hVariation 2 e C u v

/-- Spatially sensitive finite-resolvent bridge for the exact terminal
kernel-section covariance.

Because the source crossing ratio has a singleton variation profile, the
generic sum over all physical fibers from the finite covariance telescope
collapses exactly to one source entry of the finite resolvent generated by the
two-step terminal target profile.  This is still finite-volume and finite-M:
no vanishing remainder or spatial decay is asserted here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovariance_partial_telescope_abs_le_crossingWidth_mul_sourceFiniteResolventProfile
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hTarget :
      target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source source)
    (g1 g2 h k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (M : Nat) :
    |realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        (fun A =>
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
          H N hN beta hbeta B target source g1 g2 k) -
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        (fun A =>
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
            H N hN beta hbeta B target source g1 g2 k)
          M)| <=
      (Real.exp (2 * beta) - Real.exp (-2 * beta)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile
            H beta hbeta target)
          M (Sum.inl source) := by
  classical
  have hRemote :
      target ∉
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source source := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
      hTarget
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H source source target hRemote with
    ⟨_hSourceTarget, hne, hNoShare⟩
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  let crossing :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
    fun A =>
      specialUnitaryWilsonRelativeKernel N beta (A source) h /
        specialUnitaryWilsonRelativeKernel N beta (A source) k
  let terminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
      H N hN beta hbeta B target source g1 g2 k
  let crossingVariation : PeriodicHypercubicEvenSpatialSliceLink H -> Real :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation
      H beta source
  let terminalVariation : PeriodicHypercubicEvenSpatialSliceLink H -> Real :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile
      H beta hbeta target
  have hCrossingStrong : StronglyMeasurable crossing := by
    have hNumContinuous :
        Continuous
          (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            specialUnitaryWilsonRelativeKernel N beta (A source) h) :=
      (continuous_specialUnitaryWilsonRelativeKernel N beta).comp₂
        (continuous_apply source) continuous_const
    have hDenContinuous :
        Continuous
          (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            specialUnitaryWilsonRelativeKernel N beta (A source) k) :=
      (continuous_specialUnitaryWilsonRelativeKernel N beta).comp₂
        (continuous_apply source) continuous_const
    dsimp [crossing]
    exact
      (hNumContinuous.div hDenContinuous
        (fun A =>
          ne_of_gt
            (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) k))).stronglyMeasurable
  have hCrossingMemLp : MemLp crossing 2 mu := by
    refine MemLp.of_bound hCrossingStrong.aestronglyMeasurable (Real.exp (2 * beta)) ?_
    exact ae_of_all _ fun A => by
      dsimp [crossing]
      rw [Real.norm_eq_abs, abs_of_pos
        (div_pos
          (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) h)
          (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) k))]
      exact
        (specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
          N hN beta hbeta (A source) h k).2
  have hTerminalStrong : StronglyMeasurable terminal := by
    dsimp [terminal]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable_stronglyMeasurable
        H N hN beta hbeta B target source g1 g2 k
  have hTerminalMemLp : MemLp terminal 2 mu := by
    dsimp [terminal, mu]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable_memLp_two
        H N hN beta hbeta B hne hNoShare g1 g2 k
  have hCrossingVariationNonneg : forall e, 0 <= crossingVariation e := by
    simpa [crossingVariation] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation_nonneg
        H beta hbeta source
  have hTerminalVariationNonneg : forall e, 0 <= terminalVariation e := by
    simpa [terminalVariation] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalLeftVariationProfile_nonneg
        H beta hbeta target
  have hCrossingVariation :
      forall
        (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |crossing (Function.update C e u) -
          crossing (Function.update C e v)| <= crossingVariation e := by
    intro e C u v
    simpa [crossing, crossingVariation] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatio_variation_le
        H N hN beta hbeta source h k e C u v
  have hTerminalVariation :
      forall
        (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |terminal (Function.update C e u) -
          terminal (Function.update C e v)| <= terminalVariation e := by
    intro e C u v
    simpa [terminal, terminalVariation] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable_fiberVariation_le
        H N hN beta hbeta B target source g1 g2 k e C u v
  have hBound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_finiteResolventProfile
      H N hN beta hbeta B hne hNoShare g2 k crossing terminal
      hCrossingStrong hTerminalStrong hCrossingMemLp hTerminalMemLp
      crossingVariation terminalVariation
      hCrossingVariationNonneg hTerminalVariationNonneg
      hCrossingVariation hTerminalVariation M
  change
    |realIntegralCovariance mu crossing terminal -
      realIntegralCovariance mu crossing
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k terminal M)| <= _
  have hCollapsed :
      (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        crossingVariation fiber *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta terminalVariation M (Sum.inl fiber)) =
        (Real.exp (2 * beta) - Real.exp (-2 * beta)) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta terminalVariation M (Sum.inl source) := by
    simp [
      crossingVariation,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceCrossingRatioVariation]
  rw [hCollapsed] at hBound
  simpa [mu, crossing, terminal, terminalVariation] using hBound

end

end MathlibAnalytic
end MGAP4D
