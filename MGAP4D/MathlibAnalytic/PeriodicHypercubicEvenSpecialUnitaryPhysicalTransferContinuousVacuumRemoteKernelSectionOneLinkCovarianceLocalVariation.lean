import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionDeterministicScheduleCovarianceTelescope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathRow
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance remoteKernelSectionOneLinkCovarianceLocalVariationSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionOneLinkCovarianceLocalVariationSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionOneLinkCovarianceLocalVariationKernelSectionProbabilityMeasure
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

/-- A proof-relevant variation bound on the resampled physical fiber controls
the actual remote one-link fluctuation pointwise.  This is a literal C5
sampling-and-reinsertion statement; it does not use a Gibbs-law
identification. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_abs_le_fiberVariation
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (hVariationNonneg : forall e, 0 <= variation e)
    (hVariation :
      forall (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |F (Function.update C e u) - F (Function.update C e v)| <= variation e)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta B target source fiber k g2 F A| <= variation fiber := by
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g2 A
  let phi : Matrix.specialUnitaryGroup (Fin N) Complex -> Real :=
    fun u => F (Function.update A fiber u)
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k g2 A
  have hUpdate : Measurable
      (fun u : Matrix.specialUnitaryGroup (Fin N) Complex =>
        Function.update A fiber u) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber).comp (measurable_const.prodMk measurable_id)
  have hPhi : StronglyMeasurable phi := by
    dsimp [phi]
    exact hF.comp_measurable hUpdate
  have hCurrent : Function.update A fiber (A fiber) = A := by
    classical
    funext e
    by_cases he : e = fiber
    · subst e
      simp
    · simp [Function.update, he]
  have hPhiVariation :
      forall u : Matrix.specialUnitaryGroup (Fin N) Complex,
        |F A - phi u| <= variation fiber := by
    intro u
    have h := hVariation fiber A (A fiber) u
    rw [hCurrent] at h
    simpa [phi] using h
  have hPhiBound :
      forall u : Matrix.specialUnitaryGroup (Fin N) Complex,
        norm (phi u) <= norm (variation fiber + |F A|) := by
    intro u
    have hTri : |phi u| <= |phi u - F A| + |F A| := by
      calc
        |phi u| = |(phi u - F A) + F A| := by
          congr 1
          ring
        _ <= |phi u - F A| + |F A| := by
          simpa [Real.norm_eq_abs] using norm_add_le (phi u - F A) (F A)
    have hVar : |phi u - F A| <= variation fiber := by
      simpa [abs_sub_comm] using hPhiVariation u
    have hRaw : |phi u| <= variation fiber + |F A| :=
      hTri.trans (add_le_add hVar (le_refl _))
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (hVariationNonneg fiber) (abs_nonneg (F A)))] using hRaw
  have hPhiInt : Integrable phi nu := by
    apply (integrable_const (variation fiber + |F A|)).mono hPhi.aestronglyMeasurable
    filter_upwards with u
    exact hPhiBound u
  have hDiffInt : Integrable (fun u => F A - phi u) nu :=
    (integrable_const (F A)).sub hPhiInt
  have hAbsDiffInt : Integrable (fun u => |F A - phi u|) nu := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hConstInt :
      Integrable (fun _u : Matrix.specialUnitaryGroup (Fin N) Complex => variation fiber) nu :=
    integrable_const (variation fiber)
  have hBridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_schedule_eq_schedule_cons
      H N hN beta hbeta B target source fiber [] k g2 F
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
  rw [hBridge]
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_cons,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_nil]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integral
      H N hN beta hbeta B target source fiber k g2 A F hF]
  change |F A - integral phi nu| <= variation fiber
  calc
    |F A - integral phi nu| =
        |integral (fun _u : Matrix.specialUnitaryGroup (Fin N) Complex => F A) nu -
          integral phi nu| := by
      simp
    _ = |integral (fun u => F A - phi u) nu| := by
      rw [integral_sub (integrable_const (F A)) hPhiInt]
    _ <= integral (fun u => |F A - phi u|) nu :=
      abs_integral_le_integral_abs
    _ <= integral
        (fun _u : Matrix.specialUnitaryGroup (Fin N) Complex => variation fiber) nu := by
      apply integral_mono hAbsDiffInt hConstInt
      intro u
      exact hPhiVariation u
    _ = variation fiber := by
      simp

/-- The actual remote one-link covariance Dirichlet pairing has a genuinely
two-sided local variation bound.  The right-hand side retains the variation of
both observables at the same physical fiber and introduces no global
oscillation sum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuations_realIntegralCovariance_abs_le_variation_mul_variation
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target != source)
    (hNoShare :
      not periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hFStrong : StronglyMeasurable F)
    (hGStrong : StronglyMeasurable G)
    (hF : MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)))
    (hG : MemLp G 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)))
    (variationF variationG : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (hVariationFNonneg : forall e, 0 <= variationF e)
    (hVariationGNonneg : forall e, 0 <= variationG e)
    (hVariationF :
      forall (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |F (Function.update C e u) - F (Function.update C e v)| <= variationF e)
    (hVariationG :
      forall (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |G (Function.update C e u) - G (Function.update C e v)| <= variationG e) :
    |realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 F)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 G)| <=
      variationF fiber * variationG fiber := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  let QF :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
      H N hN beta hbeta B target source fiber k g2 F
  let QG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
      H N hN beta hbeta B target source fiber k g2 G
  have hFInt : Integrable F mu :=
    memLp_one_iff_integrable.1 (hF.mono_exponent one_le_two)
  have hGInt : Integrable G mu :=
    memLp_one_iff_integrable.1 (hG.mono_exponent one_le_two)
  have hQFZero : integral QF mu = 0 := by
    simpa [QF, mu] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_integral_eq_zero
        H N hN beta hbeta B hne hNoShare fiber k g2 F hFInt
  have hQGZero : integral QG mu = 0 := by
    simpa [QG, mu] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_integral_eq_zero
        H N hN beta hbeta B hne hNoShare fiber k g2 G hGInt
  have hQFMem :
      MemLp QF 2 mu := by
    simpa [QF, mu] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_memLp_two
        H N hN beta hbeta B hne hNoShare fiber k g2 F hF
  have hQGMem :
      MemLp QG 2 mu := by
    simpa [QG, mu] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_memLp_two
        H N hN beta hbeta B hne hNoShare fiber k g2 G hG
  have hProductInt : Integrable (QF * QG) mu :=
    hQFMem.integrable_mul hQGMem
  have hAbsProductInt : Integrable (fun A => |QF A * QG A|) mu := by
    simpa [Pi.mul_apply, Real.norm_eq_abs] using hProductInt.norm
  have hConstInt :
      Integrable
        (fun _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          variationF fiber * variationG fiber)
        mu :=
    integrable_const (variationF fiber * variationG fiber)
  have hPointwise :
      forall A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |QF A * QG A| <= variationF fiber * variationG fiber := by
    intro A
    rw [abs_mul]
    exact mul_le_mul
      (by
        simpa [QF] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_abs_le_fiberVariation
            H N hN beta hbeta B target source fiber k g2 F hFStrong
            variationF hVariationFNonneg hVariationF A)
      (by
        simpa [QG] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_abs_le_fiberVariation
            H N hN beta hbeta B target source fiber k g2 G hGStrong
            variationG hVariationGNonneg hVariationG A)
      (abs_nonneg _)
      (hVariationFNonneg fiber)
  change |realIntegralCovariance mu QF QG| <=
    variationF fiber * variationG fiber
  unfold realIntegralCovariance
  rw [hQFZero, hQGZero]
  simp only [zero_mul, sub_zero]
  calc
    |integral (QF * QG) mu| <=
        integral (fun A => |QF A * QG A|) mu := by
      simpa [Pi.mul_apply] using
        (abs_integral_le_integral_abs :
          |integral (fun A => QF A * QG A) mu| <=
            integral (fun A => |QF A * QG A|) mu)
    _ <= integral
        (fun _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          variationF fiber * variationG fiber)
        mu := by
      apply integral_mono hAbsProductInt hConstInt
      intro A
      exact hPointwise A
    _ = variationF fiber * variationG fiber := by
      simp

end

end MathlibAnalytic
end MGAP4D
