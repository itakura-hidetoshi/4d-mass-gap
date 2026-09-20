import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceResponseControlledWeightedRandomScanOrbit
import Mathlib.Tactic

/-!
# Response-controlled source forcing resolvent

The cross-boundary bounded-test majorant is supported on the single diagonal
fiber = source.  Hence the right-source forcing in one random-scan step is
exactly a normalized one-coordinate term, with no volume-growing sum.

Combining that exact diagonal reduction with the target-centered weighted
random-scan orbit from the preceding theorem unit gives a geometric forcing
series.  When the response-controlled weighted column coefficient is strictly
below one, the reciprocal random-scan normalization cancels exactly against
the finite-volume cardinality:
  |Lambda|^{-1} (1-q)^{-1} = (1-c_R)^{-1}.

Thus the accumulated right-source discrepancy admits a volume-independent
weighted resolvent bound.  No remote kappa certificate, covariance decay,
sweep contraction, coercivity, or mass-gap input is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance responseControlledSourceForcingResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The cross-boundary one-scan forcing is exactly the single diagonal
fiber contribution. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing_eq_diagonal
    (H : ℕ)
    (beta : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing
        H beta source variation =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        variation source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing
  rw [Finset.sum_eq_single source]
  · ring
  · intro fiber _hFiber hne
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      Ne.symm hne]
  · simp

/-- The diagonal cross-boundary coefficient is nonnegative in the physical
regime beta >= 0. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant_self_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta source source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
  simp only [if_pos rfl]
  have hExp : 1 ≤ Real.exp (8 * beta) := by
    apply Real.one_le_exp.mpr
    nlinarith
  have hSq : 1 ≤ (Real.exp (8 * beta)) ^ 2 := by
    nlinarith [Real.exp_pos (8 * beta)]
  exact
    mul_nonneg (by norm_num)
      (div_nonneg
        (sub_nonneg.mpr hSq)
        (by positivity))

/-- A target-centered pointwise weighted bound on a variation profile controls
the one-scan source forcing at the represented source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing_le_weighted
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (distinguishedTarget source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (bound : ℝ)
    (hVariationBound :
      variation source ≤
        bound *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s distinguishedTarget source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing
        H beta source variation ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing_eq_diagonal]
  have hInv :
      0 ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hMajorant :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant_self_nonneg
      H beta hbeta source
  calc
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        variation source ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        (bound *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s distinguishedTarget source) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hVariationBound hMajorant) hInv
    _ =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source := by
      ring

/-- The singleton fixed-right target-ratio variation profile is bounded by
exp(16 beta) times the target-centered exponential weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_le_exp_sixteen_mul_weight
    (H : ℕ)
    (beta s : ℝ)
    (hs : 1 ≤ s)
    (target e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target e ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target e := by
  by_cases he : e = target
  · subst e
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation]
  · have hWeight :
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s target e := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
          H s (le_trans (by norm_num) hs) target e
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
      he,
      mul_nonneg (Real.exp_pos _).le hWeight]

/-- Each forcing term along the response-controlled orbit has geometric
target-centered decay. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing_responseControlledIterate_le_weightedRate_pow
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s distinguishedTarget R responseCoefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        variation e ≤
          bound *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget e)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing
        H beta source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
          H beta hbeta distinguishedTarget R hRNonneg variation n) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        (finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)) ^ n *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source := by
  have hOrbit :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_le_weightedRate_pow_mul
      H beta hbeta s hs distinguishedTarget R hRNonneg
      responseCoefficient hResponseCoefficient hResponseWeighted
      variation hVariationNonneg bound hBoundNonneg hVariationBound n source
  have hForcing :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing_le_weighted
      H beta hbeta s distinguishedTarget source
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
        H beta hbeta distinguishedTarget R hRNonneg variation n)
      ((finiteInfluenceKernelReciprocalRandomScanRate
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient)) ^ n * bound)
      (by simpa [mul_assoc] using hOrbit)
  simpa [mul_assoc] using hForcing

/-- The accumulated source discrepancy is bounded by the finite geometric
forcing series. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_le_weightedGeometricSeries
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s distinguishedTarget R responseCoefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        variation e ≤
          bound *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget e)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta distinguishedTarget source R hRNonneg variation n ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source *
        finiteRealGeometricSeries
          (finiteInfluenceKernelReciprocalRandomScanRate
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
              beta s responseCoefficient))
          n := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_eq_sum_sourceForcing]
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient)
  let C :=
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta source source *
      bound *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s distinguishedTarget source
  calc
    (∑ j ∈ Finset.range n,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing
        H beta source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
          H beta hbeta distinguishedTarget R hRNonneg variation j)) ≤
      ∑ j ∈ Finset.range n, C * rate ^ j := by
        apply Finset.sum_le_sum
        intro j _hj
        have hStep :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceForcing_responseControlledIterate_le_weightedRate_pow
            H beta hbeta s hs distinguishedTarget source R hRNonneg
            responseCoefficient hResponseCoefficient hResponseWeighted
            variation hVariationNonneg bound hBoundNonneg hVariationBound j
        simpa [C, rate, mul_assoc, mul_left_comm, mul_comm] using hStep
    _ = C * finiteRealGeometricSeries rate n := by
      rw [finiteRealGeometricSeries]
      rw [Finset.mul_sum]
    _ =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source *
        finiteRealGeometricSeries
          (finiteInfluenceKernelReciprocalRandomScanRate
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
              beta s responseCoefficient))
          n := by
      rfl

/-- Under strict weighted response-controlled coefficient, the accumulated
right-source discrepancy has a volume-independent resolvent bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_le_weightedResolvent
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s distinguishedTarget R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        variation e ≤
          bound *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget e)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta distinguishedTarget source R hRNonneg variation n ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  let coefficient :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
      beta s responseCoefficient
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H) coefficient
  have hCardNat :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨distinguishedTarget⟩
  have hCoefficientNonneg : 0 ≤ coefficient := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient_nonneg
        beta s responseCoefficient hbeta hResponseCoefficient
  have hRateNonneg : 0 ≤ rate := by
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hCardNat coefficient hCoefficientNonneg
  have hRateLtOne : rate < 1 := by
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_lt_one
        hCardNat coefficient (by simpa [coefficient] using hCoefficientLtOne)
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_le_weightedGeometricSeries
      H beta hbeta s hs distinguishedTarget source R hRNonneg
      responseCoefficient hResponseCoefficient hResponseWeighted
      variation hVariationNonneg bound hBoundNonneg hVariationBound n
  have hGeom :=
    finiteRealGeometricSeries_le_inv_one_sub
      rate hRateNonneg hRateLtOne n
  have hInv :
      0 ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hMajorant :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant_self_nonneg
      H beta hbeta source
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hWeight :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
      H s hsNonneg distinguishedTarget source
  have hPrefactor :
      0 ≤
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta source source *
          bound *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s distinguishedTarget source := by
    positivity
  have hCancel :=
    inv_card_mul_inv_one_sub_reciprocalRate
      hCardNat coefficient (by simpa [coefficient] using hCoefficientLtOne)
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta distinguishedTarget source R hRNonneg variation n ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source *
        finiteRealGeometricSeries rate n := by
          simpa [rate, coefficient] using hBase
    _ ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source *
        (1 - rate)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hGeom hPrefactor
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source *
        (1 - coefficient)⁻¹ := by
          calc
            (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
                  beta source source *
                bound *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
                  H s distinguishedTarget source *
                (1 - rate)⁻¹ =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
                  beta source source *
                bound *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
                  H s distinguishedTarget source *
                ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
                  (1 - rate)⁻¹) := by
                    ring
            _ =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
                  beta source source *
                bound *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
                  H s distinguishedTarget source *
                (1 - coefficient)⁻¹ := by
                    rw [hCancel]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
          rfl

/-- Specialization to the literal singleton fixed-right target-ratio variation.
This is the volume-independent accumulated forcing bound needed by the
stationary response closure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioAccumulatedSourceDiscrepancy_le_weightedResolvent
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s target R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta target source R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        n ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_le_weightedResolvent
      H beta hbeta s hs target source R hRNonneg
      responseCoefficient hResponseCoefficient hResponseWeighted
      hCoefficientLtOne
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
        H beta target)
      (Real.exp (16 * beta))
      (Real.exp_pos _).le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_le_exp_sixteen_mul_weight
        H beta s hs target)
      n

end

end MathlibAnalytic
end MGAP4D
