import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceSourcePairBackgroundL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
import Mathlib.Tactic

/-!
# Source-specific pair/background L2 response carrier

PR #4724 already constructs the source-specific probability law

  nu_source(dA,du,dv),

and the associated dependent carrier `L2(nu_source)` required by the
transpose response assembler from PR #4723.

This file adds the missing coefficient-preserving response lift.  Any concrete
real response with an `L2` certificate can be packaged in that exact carrier.
If it is almost everywhere bounded by

  K(target,source) * amplitude,

then its L2 norm is bounded by the same quantity, with no cardinality or
Cauchy--Schwarz loss.

The theorem is intentionally independent of the eventual concrete
`BackwardLawResponse` formula.  The next physical unit only has to provide
its MemLp certificate and pointwise envelope estimate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance sourcePairBackgroundResponseL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairBackgroundResponseL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairBackgroundResponseL2SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairBackgroundResponseL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairBackgroundResponseL2SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairBackgroundResponseL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Package a concrete response in the exact source-specific pair/background
L2 carrier from PR #4724. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (R :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ)
    (hR :
      MemLp R 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂)) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairBackgroundL2
      H N hN beta hbeta B distinguishedSource k g₂ source :=
  hR.toLp R

/-- The source-specific response carrier has the declared concrete response as
its a.e. representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (R :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ)
    (hR :
      MemLp R 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂)) :
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2
        H N hN beta hbeta B distinguishedSource source k g₂ R hR z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂]
      R := by
  exact hR.coeFn_toLp

/-- A pointwise nonnegative constant bound lifts to the source-pair/background
L2 norm with coefficient one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2_norm_le_of_ae_bound
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (R :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ)
    (hR :
      MemLp R 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hBound :
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂,
        ‖R z‖ ≤ M) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2
        H N hN beta hbeta B distinguishedSource source k g₂ R hR‖ ≤ M := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let response :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2
      H N hN beta hbeta B distinguishedSource source k g₂ R hR
  let hConst :
      MemLp
        (fun _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) => M)
        2 μ :=
    memLp_const M
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure_isProbabilityMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  have hResponseRep :
      (fun z => response z) =ᵐ[μ] R := by
    simpa [response, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2] using
      hR.coeFn_toLp
  have hConstRep :
      (fun z => hConst.toLp
        (fun _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) => M) z) =ᵐ[μ]
        (fun _ => M) := by
    exact hConst.coeFn_toLp
  have hPoint :
      ∀ᵐ z ∂μ,
        ‖response z‖ ≤
          ‖hConst.toLp
            (fun _ :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                  Matrix.specialUnitaryGroup (Fin N) ℂ) => M) z‖ := by
    filter_upwards [hResponseRep, hConstRep, hBound] with z hResp hC hB
    rw [hResp, hC]
    simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hB
  calc
    ‖response‖ ≤
        ‖hConst.toLp
          (fun _ :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ) => M)‖ :=
      Lp.norm_le_norm_of_ae_le hPoint
    _ = M := by
      rw [MemLp.toLp_const]
      have hConstNorm :=
        Lp.norm_const'
          (μ := μ)
          (p := (2 : ENNReal))
          (c := M)
          (by norm_num)
          (by norm_num)
      simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hConstNorm
    _ = M := rfl

/-- Physical envelope specialization: a concrete response bounded a.e. by
`K(target,source) * amplitude` has the exact transpose-oriented L2 norm bound
with no loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2_norm_le_envelope_mul_amplitude
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (R :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ)
    (hR :
      MemLp R 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂))
    (amplitude : ℝ)
    (hAmplitude : 0 ≤ amplitude)
    (hBound :
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂,
        ‖R z‖ ≤
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * amplitude) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2
        H N hN beta hbeta B distinguishedSource source k g₂ R hR‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source * amplitude := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairBackgroundResponseL2_norm_le_of_ae_bound
      H N hN beta hbeta B distinguishedSource source k g₂ R hR
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source * amplitude)
      (mul_nonneg
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence_nonneg target source)
        hAmplitude)
      hBound

end

end MathlibAnalytic
end MGAP4D
