import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoSourceChangeCrossRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Pure algebraic linearization of the four-integral two-tilt defect.

This form introduces no quotient and no new measure-theoretic hypothesis. It
separates the change of the weighted observable numerator from the change of
the normalizing mass, which is the exact interface needed before exposing a
source-kernel difference. -/
theorem realIntegral_twoTilt_crossRatio_defect_eq_integralDifference_defect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ) :
    (∫ x, w x * f x * r x ∂μ) * (∫ x, w x * s x ∂μ) -
        (∫ x, w x * f x * s x ∂μ) * (∫ x, w x * r x ∂μ) =
      (∫ x, w x * s x ∂μ) *
          ((∫ x, w x * f x * r x ∂μ) -
            ∫ x, w x * f x * s x ∂μ) -
        (∫ x, w x * f x * s x ∂μ) *
          ((∫ x, w x * r x ∂μ) -
            ∫ x, w x * s x ∂μ) := by
  ring

/-- Under exactly the integrability needed for integral subtraction, the
quotient-free two-tilt defect is linear in the pointwise source-tilt difference
`r - s`.

No likelihood ratio `r / s` is formed. This theorem therefore preserves a
future distance-sensitive estimate on the source change itself. -/
theorem realIntegral_twoTilt_crossRatio_defect_eq_sourceDifference_defect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwfrInt : Integrable (fun x => w x * f x * r x) μ)
    (hwfsInt : Integrable (fun x => w x * f x * s x) μ) :
    (∫ x, w x * f x * r x ∂μ) * (∫ x, w x * s x ∂μ) -
        (∫ x, w x * f x * s x ∂μ) * (∫ x, w x * r x ∂μ) =
      (∫ x, w x * s x ∂μ) *
          (∫ x, w x * f x * (r x - s x) ∂μ) -
        (∫ x, w x * f x * s x ∂μ) *
          (∫ x, w x * (r x - s x) ∂μ) := by
  have hObsSub :
      (∫ x, w x * f x * (r x - s x) ∂μ) =
        (∫ x, w x * f x * r x ∂μ) -
          ∫ x, w x * f x * s x ∂μ := by
    rw [← integral_sub hwfrInt hwfsInt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hMassSub :
      (∫ x, w x * (r x - s x) ∂μ) =
        (∫ x, w x * r x ∂μ) -
          ∫ x, w x * s x ∂μ := by
    rw [← integral_sub hwrInt hwsInt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hObsSub, hMassSub]
  exact realIntegral_twoTilt_crossRatio_defect_eq_integralDifference_defect μ w r s f

/-- The normalized two-tilt expectation change is therefore expressed by a
literal source-tilt difference once the two weighted observable numerators are
integrable. Both exact normalizing masses remain visible. -/
theorem realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_sourceDifference_defect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwrNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * r x)
    (hRMassPos : 0 < ∫ x, w x * r x ∂μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwsNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * s x)
    (hSMassPos : 0 < ∫ x, w x * s x ∂μ)
    (hwfrInt : Integrable (fun x => w x * f x * r x) μ)
    (hwfsInt : Integrable (fun x => w x * f x * s x) μ) :
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
        ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
          ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
      (∫ x, w x * s x ∂μ) *
          (∫ x, w x * f x * (r x - s x) ∂μ) -
        (∫ x, w x * f x * s x ∂μ) *
          (∫ x, w x * (r x - s x) ∂μ) := by
  rw [realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_crossRatio_defect
    μ w r s f hwrInt hwrNonneg hRMassPos hwsInt hwsNonneg hSMassPos]
  exact realIntegral_twoTilt_crossRatio_defect_eq_sourceDifference_defect
    μ w r s f hwrInt hwsInt hwfrInt hwfsInt

local instance referenceTwoSourceKernelDifferenceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceTwoSourceKernelDifferenceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceTwoSourceKernelDifferenceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceTwoSourceKernelDifferenceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceTwoSourceKernelDifferenceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceTwoSourceKernelDifferenceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Quotient-free C5 source-change identity with the source dependence exposed
as the literal difference of the two one-slab kernels.

The target link, source link, source values `k₁,k₂`, target fiber, and exact
partition functions remain explicit. The additional assumptions are precisely
the two weighted-observable integrability hypotheses needed to commute
subtraction with the real integral. No distance decay, likelihood-ratio bound,
or identification with the full four-dimensional single-link conditional law
is assumed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_twoSourceChange_cross_mul_eq_sourceKernelDifference
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hf₁ : Integrable
      (fun g =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
          f g *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
              H N beta B source fiber k₁ A g)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (hf₂ : Integrable
      (fun g =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
          f g *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
              H N beta B source fiber k₂ A g)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k₁ g₂ A *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k₂ g₂ A *
      ((∫ g, f g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target source fiber k₁ g₂ A) -
        ∫ g, f g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target source fiber k₂ g₂ A) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k₂ g₂ A *
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
            f g *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
                H N beta B source fiber k₁ A g -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
                H N beta B source fiber k₂ A g)
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) -
      (∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
            f g *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
              H N beta B source fiber k₂ A g
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) *
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
                H N beta B source fiber k₁ A g -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
                H N beta B source fiber k₂ A g)
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
      H N hN beta hbeta B target fiber g₂ A
  let r :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
      H N beta B source fiber k₁ A
  let s :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
      H N beta B source fiber k₂ A
  have hwrEq :
      (fun g => w g * r g) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
          H N hN beta hbeta B target source fiber k₁ g₂ A := by
    funext g
    rfl
  have hwsEq :
      (fun g => w g * s g) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
          H N hN beta hbeta B target source fiber k₂ g₂ A := by
    funext g
    rfl
  have hwrInt : Integrable (fun g => w g * r g) μ := by
    rw [hwrEq]
    simpa [μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B target source fiber k₁ g₂ A
  have hwsInt : Integrable (fun g => w g * s g) μ := by
    rw [hwsEq]
    simpa [μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B target source fiber k₂ g₂ A
  have hwfrInt : Integrable (fun g => w g * f g * r g) μ := by
    simpa [μ, w, r] using hf₁
  have hwfsInt : Integrable (fun g => w g * f g * s g) μ := by
    simpa [μ, w, s] using hf₂
  have hDefect :=
    realIntegral_twoTilt_crossRatio_defect_eq_sourceDifference_defect
      μ w r s f hwrInt hwsInt hwfrInt hwfsInt
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k₁ g₂ A *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k₂ g₂ A *
      ((∫ g, f g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target source fiber k₁ g₂ A) -
        ∫ g, f g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target source fiber k₂ g₂ A) =
      (∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
            f g *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
              H N beta B source fiber k₁ A g
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k₂ g₂ A -
      (∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
            f g *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
              H N beta B source fiber k₂ A g
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k₁ g₂ A :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_twoSourceChange_cross_mul_eq_crossRatio_defect
        H N hN beta hbeta B target source fiber k₁ k₂ g₂ A f
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k₂ g₂ A *
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
            f g *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
                H N beta B source fiber k₁ A g -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
                H N beta B source fiber k₂ A g)
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) -
      (∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
            f g *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
              H N beta B source fiber k₂ A g
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) *
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
              H N hN beta hbeta B target fiber g₂ A g *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
                H N beta B source fiber k₁ A g -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
                H N beta B source fiber k₂ A g)
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_eq_commonTargetWeight_mul_sourceKernel_integral
          H N hN beta hbeta B target source fiber k₁ g₂ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_eq_commonTargetWeight_mul_sourceKernel_integral
          H N hN beta hbeta B target source fiber k₂ g₂ A]
      simpa [μ, w, r, s] using hDefect

end

end MathlibAnalytic
end MGAP4D
