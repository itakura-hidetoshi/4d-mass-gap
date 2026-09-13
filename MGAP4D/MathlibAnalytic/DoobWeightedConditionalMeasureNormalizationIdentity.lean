import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAENormalizedFiberProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Multiplying expectation against a normalized Doob weighted measure by its
normalizing mass recovers the corresponding unnormalized weighted integral.

The nonzero and finite mass receipts are explicit: no cancellation is performed
at a zero or infinite normalization mass. -/
theorem doobWeightMass_mul_lintegral_doobWeightedMeasure
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (w g : α → ENNReal)
    (hw : AEMeasurable w μ)
    (hg : AEMeasurable g μ)
    (hMassZero : doobWeightMass μ w ≠ 0)
    (hMassTop : doobWeightMass μ w ≠ ∞) :
    doobWeightMass μ w * (∫⁻ x, g x ∂doobWeightedMeasure μ w) =
      ∫⁻ x, w x * g x ∂μ := by
  change doobWeightMass μ w *
      (∫⁻ x, g x ∂μ.withDensity (fun x => w x / doobWeightMass μ w)) =
    ∫⁻ x, w x * g x ∂μ
  rw [lintegral_withDensity_eq_lintegral_mul₀ (hw.div_const _) hg]
  simp only [Pi.mul_apply, div_eq_mul_inv]
  rw [show
    (fun x => w x * (doobWeightMass μ w)⁻¹ * g x) =
      (fun x => (w x * g x) * (doobWeightMass μ w)⁻¹) by
        funext x
        ac_rfl]
  rw [lintegral_mul_const'' _ (hw.mul hg)]
  calc
    doobWeightMass μ w *
        ((∫⁻ x, w x * g x ∂μ) * (doobWeightMass μ w)⁻¹) =
      (∫⁻ x, w x * g x ∂μ) *
        (doobWeightMass μ w * (doobWeightMass μ w)⁻¹) := by
      ac_rfl
    _ = ∫⁻ x, w x * g x ∂μ := by
      rw [ENNReal.mul_inv_cancel hMassZero hMassTop, mul_one]

local instance normalizationIdentitySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance normalizationIdentitySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance normalizationIdentitySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance normalizationIdentitySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance normalizationIdentitySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance normalizationIdentitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForNormalizationIdentity
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- For Haar-a.e. left boundary and Haar-a.e. retained off-target context,
multiplying expectation against the literal normalized split target fiber by
its exact target-fiber mass recovers the corresponding unnormalized weighted
Haar integral.

This is a fiberwise normalization identity only.  It does not assert outer
measurability of the family of normalized fibers and does not identify them
with a regular conditional distribution or with the Wilson one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiber_normalizationIdentity_ae
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ENNReal)
    (hF :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
          AEMeasurable
            (F left retained)
            (Measure.pi
              (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
                normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta left target retained *
          (∫⁻ targetCfg,
            F left retained targetCfg
            ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained)) =
        ∫⁻ targetCfg,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
              H N hN beta hbeta left target (targetCfg, retained) *
            F left retained targetCfg
          ∂(Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) := by
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have hObs :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂μOff,
          AEMeasurable (F left retained) μTarget := by
    simpa [μTarget, μOff] using hF
  have hWeight :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂μOff,
          AEMeasurable
            (fun targetCfg :
                PeriodicHypercubicEvenSpatialSliceTargetLink H target →
                  Matrix.specialUnitaryGroup (Fin N) ℂ =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
                H N hN beta hbeta left target (targetCfg, retained)) μTarget := by
    simpa [μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_ae_targetFiber
        H N hN beta hbeta target)
  have hMass :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂μOff,
          0 <
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta left target retained ∧
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta left target retained < ∞ := by
    simpa [μOff] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_ae_pos_lt_top
        H N hN beta hbeta target)
  filter_upwards [hObs, hWeight, hMass] with left hObsLeft hWeightLeft hMassLeft
  filter_upwards [hObsLeft, hWeightLeft, hMassLeft] with retained hObs' hWeight' hMass'
  let w :
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ENNReal :=
    fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
        H N hN beta hbeta left target (targetCfg, retained)
  have hMassZero : doobWeightMass μTarget w ≠ 0 := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_eq_doobWeightMass
      H N hN beta hbeta left target retained]
    exact ne_of_gt hMass'.1
  have hMassTop : doobWeightMass μTarget w ≠ ∞ := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_eq_doobWeightMass
      H N hN beta hbeta left target retained]
    exact ne_of_lt hMass'.2
  simpa [μTarget, w,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_eq_doobWeightMass] using
    (doobWeightMass_mul_lintegral_doobWeightedMeasure
      μTarget w (F left retained) hWeight' hObs' hMassZero hMassTop)

end

end MathlibAnalytic
end MGAP4D
