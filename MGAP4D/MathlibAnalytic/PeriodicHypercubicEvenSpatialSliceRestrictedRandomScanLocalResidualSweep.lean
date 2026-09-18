import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveNeighborResidualColumnBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRestrictedRandomScanGeometricResidual
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance spatialSliceRestrictedRandomScanLocalResidualSweepFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For a physical spatial-link random scan, a strict volume-independent
column coefficient becomes a volume-independent exponential envelope after a
whole number of physical-link sweeps.  The one-step reciprocal rate itself
still depends on the finite volume; only the full-sweep envelope is uniform. -/
theorem
    periodicHypercubicEvenSpatialSlice_reciprocalRandomScanRate_pow_card_mul_le_expSweep
    (H : ℕ)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnLtOne : columnCoefficient < 1)
    (sweeps : ℕ) :
    finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H)
          columnCoefficient ^
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps) ≤
      Real.exp (-(1 - columnCoefficient) * (sweeps : ℝ)) := by
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let n : ℕ := Fintype.card Link
  let rate : ℝ :=
    finiteInfluenceKernelReciprocalRandomScanRate Link columnCoefficient
  let x : ℝ := (n : ℝ)⁻¹ * (1 - columnCoefficient)
  change rate ^ (n * sweeps) ≤
    Real.exp (-(1 - columnCoefficient) * (sweeps : ℝ))
  have hCard : 0 < n := by
    dsimp [n, Link]
    exact periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hGapNonneg : 0 ≤ 1 - columnCoefficient :=
    (sub_pos.mpr hColumnLtOne).le
  have hxNonneg : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hGapNonneg
  have hRateNonneg : 0 ≤ rate := by
    dsimp [rate]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hCard columnCoefficient hColumnNonneg
  have hComplement : 1 - rate = x := by
    dsimp [rate, x, n, Link]
    exact
      one_sub_finiteInfluenceKernelReciprocalRandomScanRate
        (periodicHypercubicEvenSpatialSliceLink_card_pos H)
        columnCoefficient
  have hRateEq : rate = 1 - x := by
    linarith
  have hStep : rate ≤ Real.exp (-x) := by
    rw [hRateEq]
    have hExp := Real.add_one_le_exp (-x)
    nlinarith
  have hPow :
      rate ^ (n * sweeps) ≤
        (Real.exp (-x)) ^ (n * sweeps) :=
    pow_le_pow_left₀ hRateNonneg hStep (n * sweeps)
  have hCardNe : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCard
  calc
    rate ^ (n * sweeps) ≤
        (Real.exp (-x)) ^ (n * sweeps) := hPow
    _ = Real.exp (((n * sweeps : ℕ) : ℝ) * (-x)) := by
      exact (Real.exp_nat_mul (-x) (n * sweeps)).symm
    _ = Real.exp (-(1 - columnCoefficient) * (sweeps : ℝ)) := by
      congr 1
      dsimp [x]
      rw [Nat.cast_mul]
      field_simp [hCardNe]
      <;> ring

/-- A local-plus-residual pointwise bound on the physical left-left block of an
augmented influence kernel gives a uniform column coefficient
`18 * eta + rho`.  This theorem only concerns the physical left restriction;
it makes no claim about represented right-source coordinates. -/
theorem
    periodicHypercubicEvenSpatialSlice_sumLeftRestriction_columnSum_le_eighteen_mul_add_residualBound
    (H : ℕ)
    (K :
      FiniteNonnegativeInfluenceKernelData
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)))
    (residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hResidualNonneg : ∀ target source, 0 ≤ residual target source)
    (hPointwise : ∀ target source,
      K.influence (Sum.inl target) (Sum.inl source) ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          eta else 0) + residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelColumnSum
        (finiteInfluenceKernelSumLeftRestriction K)
        source ≤
      18 * eta + rho := by
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      K.influence (Sum.inl target) (Sum.inl source)) ≤
        18 * eta + rho
  exact
    periodicHypercubicEvenSpatialSlice_influenceColumnSum_le_eighteen_mul_add_residualBound
      H
      (fun target source =>
        K.influence (Sum.inl target) (Sum.inl source))
      residual eta rho hEtaNonneg hResidualNonneg hPointwise
      hResidualColumn source

/-- Under the strict local-plus-residual gate `18 * eta + rho < 1`, every
physical-left coordinate of the restricted random-scan variation profile
contracts after `sweeps` whole physical-link sweeps by the uniform envelope
`exp (-(1 - (18 * eta + rho)) * sweeps)`.

This is an abstract sparse/local carrier theorem.  It does not assert that the
older dense distinct-fiber C5 carrier satisfies the hypotheses. -/
theorem
    periodicHypercubicEvenSpatialSlice_sumRestrictedTargetRandomScanVariationIterate_inl_le_expSweep_of_local_residual
    (H : ℕ)
    (K :
      FiniteNonnegativeInfluenceKernelData
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)))
    (residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hRhoNonneg : 0 ≤ rho)
    (hResidualNonneg : ∀ target source, 0 ≤ residual target source)
    (hPointwise : ∀ target source,
      K.influence (Sum.inl target) (Sum.inl source) ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          eta else 0) + residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (hStrict : 18 * eta + rho < 1)
    (variation :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤ variation (Sum.inl e))
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        variation (Sum.inl e) ≤ bound)
    (sweeps : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K
        (fun target : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl target)
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        (Sum.inl source) ≤
      Real.exp (-(1 - (18 * eta + rho)) * (sweeps : ℝ)) * bound := by
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let columnCoefficient : ℝ := 18 * eta + rho
  have hCard : 0 < Fintype.card Link := by
    simpa [Link] using periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hColumnNonneg : 0 ≤ columnCoefficient := by
    dsimp [columnCoefficient]
    exact add_nonneg (mul_nonneg (by norm_num) hEtaNonneg) hRhoNonneg
  have hColumnLtOne : columnCoefficient < 1 := by
    simpa [columnCoefficient] using hStrict
  have hColumnSum :
      ∀ source : Link,
        finiteInfluenceKernelColumnSum
            (finiteInfluenceKernelSumLeftRestriction K)
            source ≤
          columnCoefficient := by
    intro e
    simpa [Link, columnCoefficient] using
      periodicHypercubicEvenSpatialSlice_sumLeftRestriction_columnSum_le_eighteen_mul_add_residualBound
        H K residual eta rho hEtaNonneg hResidualNonneg hPointwise
        hResidualColumn e
  have hBase :=
    finiteInfluenceKernelSumRestrictedTargetRandomScanVariationIterate_inl_le_rate_pow_mul
      K hCard columnCoefficient hColumnNonneg hColumnSum
      variation hVariationNonneg bound hBoundNonneg hVariationBound
      (Fintype.card Link * sweeps) source
  have hSweep :=
    periodicHypercubicEvenSpatialSlice_reciprocalRandomScanRate_pow_card_mul_le_expSweep
      H columnCoefficient hColumnNonneg hColumnLtOne sweeps
  calc
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K
        (fun target : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl target)
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        (Sum.inl source) ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          Link columnCoefficient ^
        (Fintype.card Link * sweeps) * bound := by
          simpa [Link] using hBase
    _ ≤ Real.exp (-(1 - columnCoefficient) * (sweeps : ℝ)) * bound :=
      mul_le_mul_of_nonneg_right hSweep hBoundNonneg
    _ = Real.exp (-(1 - (18 * eta + rho)) * (sweeps : ℝ)) * bound := by
      rfl

/-- Summing the preceding coordinatewise estimate gives the finite-volume
terminal-mass envelope.  The only remaining explicit volume factor is the
number of physical links; the contraction exponent itself is volume
independent and can therefore be driven by choosing more sweeps at fixed
finite volume. -/
theorem
    periodicHypercubicEvenSpatialSlice_sumRestrictedTargetRandomScanVariationIterate_leftTotal_le_card_mul_expSweep_of_local_residual
    (H : ℕ)
    (K :
      FiniteNonnegativeInfluenceKernelData
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)))
    (residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hRhoNonneg : 0 ≤ rho)
    (hResidualNonneg : ∀ target source, 0 ≤ residual target source)
    (hPointwise : ∀ target source,
      K.influence (Sum.inl target) (Sum.inl source) ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          eta else 0) + residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (hStrict : 18 * eta + rho < 1)
    (variation :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤ variation (Sum.inl e))
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        variation (Sum.inl e) ≤ bound)
    (sweeps : ℕ) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K
        (fun target : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl target)
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        (Sum.inl source)) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (Real.exp (-(1 - (18 * eta + rho)) * (sweeps : ℝ)) * bound) := by
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K
        (fun target : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl target)
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        (Sum.inl source)) ≤
      ∑ _source : PeriodicHypercubicEvenSpatialSliceLink H,
        (Real.exp (-(1 - (18 * eta + rho)) * (sweeps : ℝ)) * bound) := by
      apply Finset.sum_le_sum
      intro source _
      exact
        periodicHypercubicEvenSpatialSlice_sumRestrictedTargetRandomScanVariationIterate_inl_le_expSweep_of_local_residual
          H K residual eta rho hEtaNonneg hRhoNonneg hResidualNonneg
          hPointwise hResidualColumn hStrict variation hVariationNonneg
          bound hBoundNonneg hVariationBound sweeps source
    _ =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (Real.exp (-(1 - (18 * eta + rho)) * (sweeps : ℝ)) * bound) := by
      simp [nsmul_eq_mul]

end

end MathlibAnalytic
end MGAP4D
