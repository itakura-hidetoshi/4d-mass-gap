import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseTargetMajorant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferVacuumResponseAmplitudeMatrix
import Mathlib.Tactic

/-!
# Fixed-background response amplitude matrix

PR #4835 packages, at one fixed outer boundary C, the response-energy matrix

  E_resp^C(source,target)

and proves

  E_resp^C(source,target)
    <= ofReal(K_pin(target,source)^2) * M_target(C),

where M_target(C) is source-independent.

This file takes exact real square roots, in the same style as PR #4818.

The only new finiteness point is the fixed-C target kernel-section residual
energy.  For a bounded concrete representative F, both F(C,A) and its
target-fiber probability mean are bounded by |bound|, so the residual square
is bounded by (2|bound|)^2 under a probability law.  Hence the residual energy,
the deweighted target majorant, and the response-energy right-hand side are
finite.

We define

  U_target^C = sqrt(toReal(M_target(C))),
  A_resp^C(source,target) = sqrt(toReal(E_resp^C(source,target)))

and prove

  A_resp^C(source,target)
    <= K_pin(target,source) * U_target^C

for every ordered pair, including the zero diagonal.

No new estimate, cutoff, response coefficient, factor two beyond the literal
boundedness proof for finiteness, or finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundResponseAmplitudeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedBackgroundResponseAmplitudeSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedBackgroundResponseAmplitudeSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedBackgroundResponseAmplitudeSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundResponseAmplitudeSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedBackgroundResponseAmplitudeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Fixed-C source-independent target amplitude. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
        H N hN s beta hbeta C target F))

/-- Fixed-C response amplitude matrix. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseEnergyMatrix
        H N hN beta hbeta C distinguishedSource F hF bound hbound source target))

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude_nonneg
    (H N : ℕ) (hN : 0 < N)
    (s beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
        H N hN s beta hbeta C target F := by
  exact Real.sqrt_nonneg _

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_nonneg
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
        H N hN beta hbeta C distinguishedSource F hF bound hbound source target := by
  exact Real.sqrt_nonneg _

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_diag
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource e :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
        H N hN beta hbeta C distinguishedSource F hF bound hbound e e = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix]

/-- For a bounded concrete representative, the fixed-C target residual energy
is finite. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_ne_top_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C target F ≠ ⊤ := by
  let μref :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta C target target (C target) (C target)
  letI : IsProbabilityMeasure μref :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C target target (C target) (C target)
  have hμ :
      μref =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
    simpa [μref] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection
        H N hN beta hbeta C target target
  have hPoint :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (F (C, A) -
          ∫ g,
            F (C, Function.update A target g)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta C A target) ^ 2 ≤
          (2 * |bound|) ^ 2 := by
    intro A
    let κref :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta C target target target
        (C target) (C target) A
    letI : IsProbabilityMeasure κref := by
      dsimp [κref]
      infer_instance
    have hκ :
        κref =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta C A target := by
      simpa [κref] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A target target target
    have hFA : |F (C, A)| ≤ |bound| := by
      have h := hbound (C, A)
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_abs_self bound)
    have hMean :
        ‖∫ g, F (C, Function.update A target g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta C A target‖ ≤ |bound| := by
      rw [← hκ]
      have h :=
        norm_integral_le_of_norm_le_const
          (μ := κref)
          (C := |bound|)
          (f := fun g => F (C, Function.update A target g))
          (Filter.Eventually.of_forall fun g => by
            have hg := hbound (C, Function.update A target g)
            exact hg.trans (le_abs_self bound))
      simpa using h
    have hMeanAbs :
        |∫ g, F (C, Function.update A target g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta C A target| ≤ |bound| := by
      simpa [Real.norm_eq_abs] using hMean
    have hAbs :
        |F (C, A) -
          ∫ g, F (C, Function.update A target g)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta C A target| ≤
          2 * |bound| := by
      calc
        |F (C, A) -
          ∫ g, F (C, Function.update A target g)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta C A target| ≤
            |F (C, A)| +
              |∫ g, F (C, Function.update A target g)
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                  H N hN beta hbeta C A target| := abs_sub _ _
        _ ≤ |bound| + |bound| := add_le_add hFA hMeanAbs
        _ = 2 * |bound| := by ring
    have hLeft0 :
        0 ≤
          |F (C, A) -
            ∫ g, F (C, Function.update A target g)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta C A target| :=
      abs_nonneg _
    have hRight0 : 0 ≤ 2 * |bound| :=
      mul_nonneg (by norm_num) (abs_nonneg _)
    have hSqAbs :=
      (sq_le_sq₀ hLeft0 hRight0).2 hAbs
    simpa [sq_abs] using hSqAbs
  have hBound :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target F ≤
        ENNReal.ofReal ((2 * |bound|) ^ 2) := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
    rw [← hμ]
    calc
      (∫⁻ A,
        ENNReal.ofReal
          ((F (C, A) -
              ∫ g,
                F (C, Function.update A target g)
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                  H N hN beta hbeta C A target) ^ 2)
        ∂μref) ≤
          ∫⁻ _A, ENNReal.ofReal ((2 * |bound|) ^ 2) ∂μref := by
            apply lintegral_mono
            intro A
            exact ENNReal.ofReal_le_ofReal (hPoint A)
      _ = ENNReal.ofReal ((2 * |bound|) ^ 2) := by simp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBound

/-- The fixed-C target majorant is finite on the strict physical-sweep
interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant_ne_top
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
        H N hN s beta hbeta C target F ≠ ⊤ := by
  let c : ℝ≥0∞ :=
    ENNReal.ofReal
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta) ^ 2)
  let gap : ℝ≥0∞ := 1 - c
  have hc : c < 1 := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_sq_ofReal_lt_one_of_strictPhysicalSweepCutoff
        s beta hbeta hcut
  have hGapPos : 0 < gap := by
    simpa [gap] using (tsub_pos_iff_lt.mpr hc)
  have hGapZero : gap ≠ 0 := ne_of_gt hGapPos
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
  change
    gap⁻¹ *
      ((ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target F) ≠ ⊤
  apply ENNReal.mul_ne_top
  · exact ENNReal.inv_ne_top.2 hGapZero
  · apply ENNReal.mul_ne_top
    · exact
        ENNReal.add_ne_top.2
          ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
    · exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_ne_top_of_bounded
          H N hN beta hbeta C target F hF bound hbound

/-- Off-diagonal fixed-C square-root response bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_le_canonicalPinFree_mul_targetAmplitude_of_ne
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
        H N hN beta hbeta C distinguishedSource F hF bound hbound source target ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta C target F := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let E : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseEnergyMatrix
      H N hN beta hbeta C distinguishedSource F hF bound hbound source target
  let M : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
      H N hN s beta hbeta C target F
  have hEnergy : E ≤ ENNReal.ofReal ((K.influence target source) ^ 2) * M := by
    simpa [E, M, K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseEnergyMatrix_le_canonicalPinFree_sq_mul_targetMajorant
        N hN s hs beta hbeta hcut H C distinguishedSource source target
        F hF bound hbound
  have hMTop : M ≠ ⊤ := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant_ne_top
        N hN s hs beta hbeta hcut H C target F hF bound hbound
  have hRhsTop :
      ENNReal.ofReal ((K.influence target source) ^ 2) * M ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hMTop
  have hToReal :
      E.toReal ≤
        (ENNReal.ofReal ((K.influence target source) ^ 2) * M).toReal :=
    ENNReal.toReal_mono hRhsTop hEnergy
  have hToReal' :
      E.toReal ≤ (K.influence target source) ^ 2 * M.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at hToReal
    exact hToReal
  have hK0 : 0 ≤ K.influence target source :=
    K.influence_nonneg target source
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
        H N hN beta hbeta C distinguishedSource F hF bound hbound source target =
      Real.sqrt E.toReal := by rfl
    _ ≤ Real.sqrt ((K.influence target source) ^ 2 * M.toReal) :=
      Real.sqrt_le_sqrt hToReal'
    _ =
      Real.sqrt ((K.influence target source) ^ 2) * Real.sqrt M.toReal := by
      rw [Real.sqrt_mul (sq_nonneg _)]
    _ =
      K.influence target source * Real.sqrt M.toReal := by
      rw [Real.sqrt_sq hK0]
    _ =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta C target F := by
      rfl

/-- All-pairs fixed-C amplitude bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_le_canonicalPinFree_mul_targetAmplitude
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
        H N hN beta hbeta C distinguishedSource F hF bound hbound source target ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta C target F := by
  by_cases hEq : target = source
  · subst target
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_diag]
    exact
      mul_nonneg
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)).influence_nonneg source source)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude_nonneg
          H N hN s beta hbeta C source F)
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_le_canonicalPinFree_mul_targetAmplitude_of_ne
        N hN s hs beta hbeta hcut H C distinguishedSource source target hEq
        F hF bound hbound

end

end MGAP4D.MathlibAnalytic
