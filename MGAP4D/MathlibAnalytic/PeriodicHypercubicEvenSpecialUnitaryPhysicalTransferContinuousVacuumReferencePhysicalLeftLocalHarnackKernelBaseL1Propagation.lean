import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveGraph
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinIterateKernel
import Mathlib.Tactic

/-!
# Base-L1 propagation for the physical local Harnack kernel

The actual continuous-vacuum physical envelope has now been split exactly into
its intrinsic active-neighbor Harnack kernel plus the remote vacuum residual.
This file records the geometric propagation of the local kernel itself.

The key facts are:

* the local kernel is symmetric because intrinsic active-neighbor adjacency is
  symmetric;
* every row, as well as every column, is bounded by `18 * eta(beta)`;
* a nonzero degree-`d` recursive influence coefficient can move the embedded
  periodic link-base L1 coordinate by at most `2*d`;
* consequently, a base-L1 separation of at least `2*D` kills every degree
  `d < D` coefficient exactly;
* every degree-`d` coefficient is bounded by `(18*eta(beta))^d`.

These statements concern only the local Harnack carrier.  They do not assert
that the remote vacuum residual is zero, small, or controlled by the local
kernel.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalHarnackBaseL1SpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The intrinsic active-neighbor Harnack kernel is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_influence_comm
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta).influence target source =
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta).influence source target := by
  classical
  have hMem :
      target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source ↔
        source ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H target := by
    rw [
      periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff,
      periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff]
    constructor
    · rintro ⟨hNe, hShare⟩
      exact
        ⟨Ne.symm hNe,
          (periodicHypercubicEvenSpatialSliceLinksSharePlaquette_comm
            H source target).mpr hShare⟩
    · rintro ⟨hNe, hShare⟩
      exact
        ⟨Ne.symm hNe,
          (periodicHypercubicEvenSpatialSliceLinksSharePlaquette_comm
            H target source).mpr hShare⟩
  by_cases hActive :
      target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
  · have hActive' :
        source ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H target :=
      hMem.mp hActive
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel,
      hActive, hActive']
  · have hActive' :
        source ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H target := by
      intro h
      exact hActive (hMem.mpr h)
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel,
      hActive, hActive']

/-- For the local Harnack kernel, row and column sums agree exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_eq_columnSum
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta)
        target =
      finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta)
        target := by
  classical
  unfold finiteInfluenceKernelRowSum finiteInfluenceKernelColumnSum
  apply Finset.sum_congr rfl
  intro source _
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_influence_comm
      H beta hbeta target source

/-- Every local Harnack row is bounded by the same volume-independent
eighteen-neighbor coefficient as every column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_le_eighteen_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta)
        target ≤
      18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_eq_columnSum]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_columnSum_le_eighteen_mul
      H beta hbeta target

/-- A nonzero degree-`d` local-Harnack influence coefficient connects two
spatial links whose embedded periodic link-base L1 distance is at most `2*d`.
This is proved directly from the recursive influence kernel and the literal
one-step active-neighbor geometry. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_finiteInfluenceIterateKernel_ne_zero_imp_baseL1Distance_le_two_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ d : ℕ,
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceIterateKernel
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence
            d target source ≠ 0 →
          periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) ≤
            2 * d := by
  intro d
  induction d with
  | zero =>
      intro target source hNe
      have hEq : target = source := by
        by_contra hTargetSource
        apply hNe
        simp [finiteInfluenceIterateKernel, hTargetSource]
      subst source
      simp
  | succ d ih =>
      intro target source hNe
      let K :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta
      have hTerm :
          ∃ mid : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target mid *
                finiteInfluenceIterateKernel K.influence d mid source ≠ 0 := by
        by_contra hNone
        push_neg at hNone
        apply hNe
        change
          (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target mid *
              finiteInfluenceIterateKernel K.influence d mid source) = 0
        exact Finset.sum_eq_zero (fun mid _ => hNone mid)
      rcases hTerm with ⟨mid, hProd⟩
      have hParts := mul_ne_zero_iff.mp hProd
      have hActive :
          target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H mid :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_active_of_influence_ne_zero
          H beta hbeta target mid hParts.1
      have hAdjMidTarget :
          (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj mid target :=
        (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
          H mid target).mpr hActive
      have hAdjTargetMid :
          (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj target mid :=
        hAdjMidTarget.symm
      have hStep :
          periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H mid) ≤ 2 :=
        periodicHypercubicEvenSpatialSliceActiveGraph_adj_baseL1Distance_le_two
          H hAdjTargetMid
      have hRest :
          periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H mid)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) ≤
            2 * d := by
        simpa [K] using ih mid source hParts.2
      have hTriangle :=
        periodicHypercubicEdgeBaseL1Distance_triangle
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H mid)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
      omega

/-- If the embedded base-L1 distance is at least `2*D`, every local-Harnack
iterate coefficient of degree strictly below `D` vanishes exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_finiteInfluenceIterateKernel_eq_zero_of_two_mul_le_baseL1Distance
    (H D d : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))
    (hd : d < D) :
    finiteInfluenceIterateKernel
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        d target source = 0 := by
  by_contra hNe
  have hUpper :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_finiteInfluenceIterateKernel_ne_zero_imp_baseL1Distance_le_two_mul
      H beta hbeta d target source hNe
  omega

/-- Every degree-`d` local-Harnack coefficient is bounded by the explicit
volume-independent power `(18 * eta(beta))^d`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_finiteInfluenceIterateKernel_le_pow
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (d : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceIterateKernel
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        d target source ≤
      (18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) ^ d := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  have hRho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hRow :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ∑ f : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence e f ≤ rho := by
    intro e
    simpa [K, rho, finiteInfluenceKernelRowSum] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_le_eighteen_mul
        H beta hbeta e
  simpa [K, rho] using
    finiteInfluenceIterateKernel_le_pow
      K.influence K.influence_nonneg rho hRho hRow d target source

end

end MathlibAnalytic
end MGAP4D
