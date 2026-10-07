import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorTerminalContraction
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-!
# Terminal-free strict posterior resolvent bound for the Gram--Schmidt seed

PR #5247 controls the terminal posterior covariance by a geometric
random-scan tail under an explicit strict row coefficient.  The finite
resolvent term itself already satisfies a transpose-subinvariance inequality.

This file sums that finite-dimensional inequality before taking any limit.
For every finite truncation M,

  (1 - rho) Tot(w_M) <= Tot(v),

hence, whenever rho < 1,

  Tot(w_M) <= (1 - rho)^(-1) Tot(v).

The estimate is uniform in M.  Combining it with PR #5247's geometric terminal
bound and sending M to infinity removes the terminal covariance completely:

  |Cov(L_source,O)|
    <= (width(beta)/2) (1-rho)^(-1) Tot(v).

The arbitrary-observable source re-tilt identity from PR #5246 then gives the
matching terminal-free source-response estimate after division by the exact
source-mean floor exp(-8 beta).  Both statements are finally specialized to
the theorem-generated four-link Gram--Schmidt seed profile.

Strictness remains an explicit hypothesis.  It is not inferred from the
non-strict posterior influence data.  No covariance/L2-coordinate
identification, positive-depth hard support, or heat-bath/Euclidean-time
identification is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance p3PosteriorStrictResolventTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3PosteriorStrictResolventCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3PosteriorStrictResolventSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3PosteriorStrictResolventMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3PosteriorStrictResolventBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3PosteriorStrictResolventSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For a nonnegative profile, the transpose interaction of the literal
posterior influence matrix is bounded by a uniform row coefficient times the
total profile mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_transposeInteraction_le_rowCoefficient_mul_total
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (rowCoefficient : ℝ)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ rowCoefficient)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hw : ∀ source : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ w source) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source * w target) ≤
      rowCoefficient * finiteProductVariationTotal w := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source * w target) ≤
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        rowCoefficient * w target := by
      apply Finset.sum_le_sum
      intro target _htarget
      rw [← Finset.sum_mul]
      exact
        mul_le_mul_of_nonneg_right
          (hRowSum target)
          (hw target)
    _ = rowCoefficient * finiteProductVariationTotal w := by
      unfold finiteProductVariationTotal
      rw [← Finset.mul_sum]

/-- The finite posterior random-scan resolvent satisfies the exact
unnormalized strict-gap total-mass inequality, uniformly in the truncation
depth. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_gap_mul_total_le
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariation :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ rowCoefficient)
    (M : ℕ) :
    (1 - rowCoefficient) *
        finiteProductVariationTotal
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
            D variation M) ≤
      finiteProductVariationTotal variation := by
  let w :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
      D variation M
  have hw :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ w source := by
    intro source
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_nonneg
        D variation hVariation M source
  have hSub :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        w source ≤
          variation source +
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              D.influence target source * w target := by
    intro source
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_subinvariant
        D variation hVariation hEdge M source
  have hSummed :
      finiteProductVariationTotal w ≤
        finiteProductVariationTotal variation +
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              D.influence target source * w target) := by
    unfold finiteProductVariationTotal
    calc
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H, w source) ≤
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            (variation source +
              ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                D.influence target source * w target) := by
          apply Finset.sum_le_sum
          intro source _hsource
          exact hSub source
      _ =
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            variation source) +
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              D.influence target source * w target := by
          rw [Finset.sum_add_distrib]
  have hInteraction :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_transposeInteraction_le_rowCoefficient_mul_total
      D rowCoefficient hRowSum w hw
  have hTotal :
      finiteProductVariationTotal w ≤
        finiteProductVariationTotal variation +
          rowCoefficient * finiteProductVariationTotal w :=
    hSummed.trans (add_le_add_right hInteraction _)
  change
    (1 - rowCoefficient) * finiteProductVariationTotal w ≤
      finiteProductVariationTotal variation
  calc
    (1 - rowCoefficient) * finiteProductVariationTotal w =
        finiteProductVariationTotal w -
          rowCoefficient * finiteProductVariationTotal w := by
      ring
    _ ≤ finiteProductVariationTotal variation := by
      exact sub_le_iff_le_add.mpr hTotal

/-- Under an explicit strict posterior row coefficient, the total mass of every
finite posterior resolvent is uniformly bounded by the reciprocal row gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_total_le_inv_gap_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariation :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ rowCoefficient)
    (M : ℕ) :
    finiteProductVariationTotal
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          D variation M) ≤
      (1 - rowCoefficient)⁻¹ * finiteProductVariationTotal variation := by
  let w :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
      D variation M
  have hGapPos : 0 < 1 - rowCoefficient := sub_pos.mpr hRowLtOne
  have hGapNe : 1 - rowCoefficient ≠ 0 := ne_of_gt hGapPos
  have hGap :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_gap_mul_total_le
      D variation hVariation hEdge rowCoefficient hRowSum M
  have hScaled :=
    mul_le_mul_of_nonneg_left hGap (inv_nonneg.mpr hGapPos.le)
  change
    finiteProductVariationTotal w ≤
      (1 - rowCoefficient)⁻¹ * finiteProductVariationTotal variation
  calc
    finiteProductVariationTotal w =
        (1 - rowCoefficient)⁻¹ *
          ((1 - rowCoefficient) * finiteProductVariationTotal w) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤
        (1 - rowCoefficient)⁻¹ *
          finiteProductVariationTotal variation := hScaled

/-- Pointwise strict-resolvent bound obtained from the uniform total-mass
estimate and nonnegativity of the finite posterior resolvent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_le_inv_gap_mul_total
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariation :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient)
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
        D variation M source ≤
      (1 - rowCoefficient)⁻¹ * finiteProductVariationTotal variation := by
  let w :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
      D variation M
  have hw :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ w e := by
    intro e
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_nonneg
        D variation hVariation M e
  have hSourceTotal :
      w source ≤ finiteProductVariationTotal w := by
    unfold finiteProductVariationTotal
    exact
      Finset.single_le_sum
        (fun e _he => hw e)
        (Finset.mem_univ source)
  exact
    hSourceTotal.trans
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_total_le_inv_gap_mul
        D variation hVariation hEdge rowCoefficient hRowLtOne hRowSum M)

/-- Under an explicit strict posterior row coefficient, the finite covariance
telescope has a terminal-free resolvent bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_strictResolvent
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        O| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        ((1 - rowCoefficient)⁻¹ *
          finiteProductVariationTotal P.variation) := by
  let radius :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta / 2
  let total := finiteProductVariationTotal P.variation
  let gapInv := (1 - rowCoefficient)⁻¹
  let q :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H) rowCoefficient
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let bound := radius * (gapInv * total)
  have hRadius : 0 ≤ radius := by
    dsimp [radius]
    exact
      div_nonneg
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
          beta hbeta)
        (by norm_num)
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hEdge rowCoefficient hRowNonneg
  have hqLtOne : q < 1 := by
    dsimp [q]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_lt_one
        hEdge rowCoefficient hRowLtOne
  have hPow :
      Tendsto (fun M : ℕ => q ^ M) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLtOne
  have hTail :
      Tendsto
        (fun M : ℕ => ‖L‖ * (q ^ M * total))
        atTop (nhds 0) := by
    have hInner :
        Tendsto (fun M : ℕ => q ^ M * total) atTop (nhds 0) := by
      simpa using hPow.mul_const total
    simpa using tendsto_const_nhds.mul hInner
  have hRhs :
      Tendsto
        (fun M : ℕ => bound + ‖L‖ * (q ^ M * total))
        atTop (nhds bound) := by
    simpa using tendsto_const_nhds.add hTail
  have hBound :
      ∀ M : ℕ,
        |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B L O| ≤
          bound + ‖L‖ * (q ^ M * total) := by
    intro M
    have hFinite :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_finiteResolvent_add_geometricTail
        source sourceValue P D hEdge rowCoefficient hRowNonneg hRowSum M
    have hResolvent :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_le_inv_gap_mul_total
        D P.variation P.variation_nonneg hEdge rowCoefficient hRowLtOne hRowSum M source
    have hFirst :
        radius *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
              D P.variation M source ≤
          radius * (gapInv * total) :=
      mul_le_mul_of_nonneg_left hResolvent hRadius
    simpa [radius, total, gapInv, q, L, bound] using
      hFinite.trans (add_le_add hFirst le_rfl)
  have hLimit :
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L O| ≤ bound :=
    ge_of_tendsto' hRhs hBound
  simpa [radius, total, gapInv, L, bound] using hLimit

/-- Terminal-free arbitrary-observable source-retilt response under the same
explicit strict posterior row coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedBCFExpectation_sub_mean_abs_le_strictResolvent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient) :
    |(∫ A,
        O A
        ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B).tilted
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt
            H N beta B source sourceValue))) -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B O| ≤
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        ((1 - rowCoefficient)⁻¹ *
          finiteProductVariationTotal P.variation)) /
      Real.exp (-8 * beta) := by
  let K :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta / 2) *
      ((1 - rowCoefficient)⁻¹ *
        finiteProductVariationTotal P.variation)
  have hCov :
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B source sourceValue)
          O| ≤ K := by
    simpa [K] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_strictResolvent
        source sourceValue P D hEdge rowCoefficient hRowNonneg hRowLtOne hRowSum
  have hRadius :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
            beta / 2 := by
    exact
      div_nonneg
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
          beta hbeta)
        (by norm_num)
  have hGapInv : 0 ≤ (1 - rowCoefficient)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hRowLtOne.le)
  have hTotal :
      0 ≤ finiteProductVariationTotal P.variation := by
    unfold finiteProductVariationTotal
    exact Finset.sum_nonneg fun e _he => P.variation_nonneg e
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hRadius (mul_nonneg hGapInv hTotal)
  simpa [K] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedBCFExpectation_sub_mean_abs_le_of_covariance
      H N hN beta hbeta B source sourceValue O K hK hCov

/-- Gram--Schmidt seed specialization of the terminal-free covariance bound. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_strictResolvent
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode)| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        ((1 - rowCoefficient)⁻¹ *
          finiteProductVariationTotal
            (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
              H mode).variation) := by
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_strictResolvent
      source sourceValue
      (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
        H mode)
      D hEdge rowCoefficient hRowNonneg hRowLtOne hRowSum

/-- Gram--Schmidt seed specialization of the terminal-free source re-tilt
response bound. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_sourceTiltedExpectation_sub_mean_abs_le_strictResolvent
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient) :
    |(∫ A,
        periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode A
        ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B).tilted
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt
            H 2 beta B source sourceValue))) -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode)| ≤
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        ((1 - rowCoefficient)⁻¹ *
          finiteProductVariationTotal
            (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
              H mode).variation)) /
      Real.exp (-8 * beta) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedBCFExpectation_sub_mean_abs_le_strictResolvent
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
      source sourceValue
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H mode)
      (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
        H mode)
      D hEdge rowCoefficient hRowNonneg hRowLtOne hRowSum

end

end MathlibAnalytic
end MGAP4D
