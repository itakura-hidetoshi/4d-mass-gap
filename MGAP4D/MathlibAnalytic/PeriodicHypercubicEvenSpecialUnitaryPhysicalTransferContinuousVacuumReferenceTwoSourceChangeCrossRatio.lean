import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceSourceChangeCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkRawDoobFactorization
import MGAP4D.MathlibAnalytic.RealIntegralCrossRatioCovarianceLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance referenceTwoSourceChangeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceTwoSourceChangeSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceTwoSourceChangeSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceTwoSourceChangeSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceTwoSourceChangeSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceTwoSourceChangeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Cross-multiplying expectations under two independently tilted positive
weights removes both normalization denominators and leaves the literal
four-integral cross-ratio defect.

This quotient-free identity keeps both source tilts visible.  In particular,
it does not identify either normalized law with a conditional distribution and
does not divide one source tilt by the other. -/
theorem realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_crossRatio_defect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwrNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * r x)
    (hRMassPos : 0 < ∫ x, w x * r x ∂μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwsNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * s x)
    (hSMassPos : 0 < ∫ x, w x * s x ∂μ) :
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
        ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
          ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
      (∫ x, w x * f x * r x ∂μ) * (∫ x, w x * s x ∂μ) -
        (∫ x, w x * f x * s x ∂μ) * (∫ x, w x * r x ∂μ) := by
  have hR :=
    realIntegralWeightedProbabilityMeasure_integral
      μ (fun x => w x * r x) f hwrInt hwrNonneg hRMassPos
  have hS :=
    realIntegralWeightedProbabilityMeasure_integral
      μ (fun x => w x * s x) f hwsInt hwsNonneg hSMassPos
  have hRJoint :
      (∫ x, (w x * r x) * f x ∂μ) =
        ∫ x, w x * f x * r x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hSJoint :
      (∫ x, (w x * s x) * f x ∂μ) =
        ∫ x, w x * f x * s x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hR, hS, hRJoint, hSJoint]
  field_simp [ne_of_gt hRMassPos, ne_of_gt hSMassPos]
  <;> ring

/-- If the second tilt is pointwise nonzero, the quotient-free two-tilt defect
can additionally be localized by the existing four-integral cross-ratio API as
an unnormalized covariance numerator under the second tilted weight.

The nonvanishing hypothesis is intentionally explicit: the preceding theorem
is the preferred interface when source-distance information must be retained
without introducing a likelihood-ratio quotient. -/
theorem realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_weightedCovarianceNumerator
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwrNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * r x)
    (hRMassPos : 0 < ∫ x, w x * r x ∂μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwsNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * s x)
    (hSMassPos : 0 < ∫ x, w x * s x ∂μ)
    (hsNe : ∀ x, s x ≠ 0) :
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
        ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
          ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
      realIntegralWeightedCovarianceNumerator μ
        (fun x => w x * s x) f (fun x => r x / s x) := by
  calc
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
          ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
            ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
        (∫ x, w x * f x * r x ∂μ) * (∫ x, w x * s x ∂μ) -
          (∫ x, w x * f x * s x ∂μ) * (∫ x, w x * r x ∂μ) :=
      realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_crossRatio_defect
        μ w r s f hwrInt hwrNonneg hRMassPos hwsInt hwsNonneg hSMassPos
    _ = realIntegralWeightedCovarianceNumerator μ
          (fun x => w x * s x) f (fun x => r x / s x) := by
      simpa using
        (real_integral_crossRatio_defect_eq_weightedCovarianceNumerator
          μ w f (fun _ => (1 : ℝ)) r s (by intro x; simp) hsNe)

/-- The part of the literal C5 one-link reference density that is common to
two changes of the same remote source value.  The source-dependent one-slab
kernel is deliberately not absorbed into this weight. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A fiber g) *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A fiber g)
      B target g₂

/-- The source-sensitive one-slab kernel on a selected target fiber.  Both the
source link and its inserted value remain explicit for later distance-sensitive
estimates. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    H N beta
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N A fiber g)
    (Function.update B source k)

/-- The literal C5 one-link fiber density factors exactly as the common
continuous-vacuum/target-local weight times the source-sensitive one-slab
kernel.  No full four-dimensional conditional-law identification is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_commonTargetWeight_mul_sourceKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A =
      fun g =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
            H N hN beta hbeta B target fiber g₂ A g *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
            H N beta B source fiber k A g := by
  rfl

/-- The named C5 fiber partition function is exactly the integral of the
common target weight times the source-sensitive one-slab kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_eq_commonTargetWeight_mul_sourceKernel_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
        H N hN beta hbeta B target source fiber k g₂ A =
      ∫ g,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
            H N hN beta hbeta B target fiber g₂ A g *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
            H N beta B source fiber k A g
        ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  rfl

/-- Quotient-free two-source comparison for the literal C5 normalized reference
fiber law.  The exact partition masses are retained, while the two source
values stay visible only through their respective one-slab kernels.  This is
the interface intended for a later distance-sensitive same-color estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_twoSourceChange_cross_mul_eq_crossRatio_defect
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) :
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
          H N hN beta hbeta B target source fiber k₁ g₂ A := by
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
  have hwrNonneg : ∀ᵐ g ∂μ, 0 ≤ w g * r g := by
    filter_upwards with g
    rw [congrFun hwrEq g]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B target source fiber k₁ g₂ A g).le
  have hwsNonneg : ∀ᵐ g ∂μ, 0 ≤ w g * s g := by
    filter_upwards with g
    rw [congrFun hwsEq g]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B target source fiber k₂ g₂ A g).le
  have hRMassPos : 0 < ∫ g, w g * r g ∂μ := by
    rw [hwrEq]
    simpa [μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
        H N hN beta hbeta B target source fiber k₁ g₂ A
  have hSMassPos : 0 < ∫ g, w g * s g ∂μ := by
    rw [hwsEq]
    simpa [μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
        H N hN beta hbeta B target source fiber k₂ g₂ A
  have hTwo :=
    realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_crossRatio_defect
      μ w r s f hwrInt hwrNonneg hRMassPos hwsInt hwsNonneg hSMassPos
  rw [hwrEq, hwsEq] at hTwo
  simpa [μ, w, r, s,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure] using hTwo

end

end MathlibAnalytic
end MGAP4D
