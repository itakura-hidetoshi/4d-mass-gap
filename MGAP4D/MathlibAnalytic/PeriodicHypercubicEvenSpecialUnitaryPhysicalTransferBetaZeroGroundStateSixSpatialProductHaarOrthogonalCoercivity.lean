import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarCommonFixedBoundary
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialRandomScanRayleigh
import Mathlib.Tactic

/-!
# Beta-zero six-spatial pair-Haar orthogonal coercivity

The common fixed sector of the actual six beta-zero pair-Haar color
projections has been identified with the complete left-boundary L2 subspace.
This file works purely on that literal pair-Haar Hilbert carrier.

For vectors orthogonal to the common fixed sector, the full sweep lies in the
common fixed sector. Pythagoras therefore makes the full-sweep defect at
least the original norm. The commuting-projection tensorization inequality
then yields an explicit normalized six-color coercivity coefficient 1/6,
and equivalently a random-scan Rayleigh factor 5/6.

No physical top-orthogonal transport is asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

/-- If a projection occurs in a commuting idempotent sweep, pre-applying that
projection does not change the final sweep. -/
theorem realHilbertProjectionSweep_absorb_of_mem
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (c : C)
    (cs : List C)
    (hc : c ∈ cs)
    (x : E) :
    realHilbertProjectionSweep P cs (P c x) =
      realHilbertProjectionSweep P cs x := by
  induction cs generalizing x with
  | nil =>
      simp at hc
  | cons d ds ih =>
      simp only [List.mem_cons] at hc
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      rcases hc with hcd | hc
      · subst d
        have hcc : P c (P c x) = P c x := by
          have h :=
            congrArg (fun Q : E →L[ℝ] E => Q x) (hIdem c)
          simpa only [ContinuousLinearMap.comp_apply] using h
        rw [hcc]
      · rw [hComm d c x]
        exact ih (x := P d x) hc

/-- Every projection occurring in a commuting idempotent sweep fixes the
output of that sweep. -/
theorem realHilbertProjectionSweep_apply_fixed_of_mem
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (c : C)
    (cs : List C)
    (hc : c ∈ cs)
    (x : E) :
    P c (realHilbertProjectionSweep P cs x) =
      realHilbertProjectionSweep P cs x := by
  calc
    P c (realHilbertProjectionSweep P cs x) =
        realHilbertProjectionSweep P cs (P c x) :=
      realHilbertProjectionSweep_commute P hComm c cs x
    _ = realHilbertProjectionSweep P cs x :=
      realHilbertProjectionSweep_absorb_of_mem
        P hIdem hComm c cs hc x

/-- The actual beta-zero six-spatial full-sweep output belongs to the complete
left-boundary common-fixed sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_apply_mem_fst
    (H N : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
        H N x ∈
      lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_self_iff_mem_fst
      H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
        H N x)).1
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_self_iff
      H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
        H N x)).2
  intro c
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep]
    using
      realHilbertProjectionSweep_apply_fixed_of_mem
        (fun d =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N d)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
          H N)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_commute
          H N)
        c
        ((Finset.univ : Finset (Fin 6)).toList)
        (by simp)
        x

/-- On the orthogonal complement of the complete left-boundary common-fixed
sector, the unnormalized six-color residual sum dominates the full norm
squared. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaar_residualSum_ge_norm_sq
    (H N : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N)
    (hx : x ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))ᗮ) :
    ‖x‖ ^ 2 ≤
      ∑ c : Fin 6,
        ‖x -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N c x‖ ^ 2 := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
      H N
  have hS_mem :
      S x ∈
        lpMeas ℝ ℝ
          (MeasurableSpace.comap Prod.fst
            (inferInstance : MeasurableSpace
              (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
          2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_apply_mem_fst
        H N x
  have horth : inner ℝ x (S x) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hS_mem hx
  have hnorm :
      ‖x‖ ^ 2 ≤ ‖x - S x‖ ^ 2 := by
    rw [norm_sub_sq_real, horth]
    nlinarith [sq_nonneg ‖S x‖]
  have htensor :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_tensorization
      H N x
  exact hnorm.trans (by simpa [S] using htensor)

/-- Explicit beta-zero six-color Poincare coefficient on the literal
pair-Haar centered sector: the normalized residual energy has coefficient
1/6. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaar_normalizedResidualEnergy_ge_one_sixth
    (H N : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N)
    (hx : x ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))ᗮ) :
    (1 / 6 : ℝ) * ‖x‖ ^ 2 ≤
      groundStateJointColorNormalizedResidualEnergy
        (fun c =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N c)
        x := by
  have hsum :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaar_residualSum_ge_norm_sq
      H N x hx
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum (show 0 ≤ (1 / 6 : ℝ) by norm_num)
  simpa [groundStateJointColorNormalizedResidualEnergy, one_div] using hscaled

/-- Literal beta-zero normalized random-scan operator for the actual six
pair-Haar spatial-color projections. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  groundStateJointColorRandomScanOperator
    (fun c =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N c)

/-- Equivalent exact beta-zero Rayleigh contraction on the literal centered
pair-Haar sector: the random-scan factor is 5/6. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan_rayleigh_le_five_sixths
    (H N : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N)
    (hx : x ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))ᗮ) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan
          H N x)
        x ≤
      (5 / 6 : ℝ) * ‖x‖ ^ 2 := by
  have hframe :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaar_normalizedResidualEnergy_ge_one_sixth
      H N x hx
  have hRayleigh :=
    (groundStateJointColorFrame_iff_randomScanRayleigh_le
      (fun c =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_symmetric
        H N)
      (1 / 6 : ℝ)
      x).1 hframe
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan]
    using hRayleigh

end

end MGAP4D.MathlibAnalytic
