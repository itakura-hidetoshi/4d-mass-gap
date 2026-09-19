import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveGraph
import Mathlib.Tactic

/-!
# Base-L1 propagation for the physical local Harnack kernel

The actual continuous-vacuum physical envelope has now been split exactly into
its intrinsic active-neighbor Harnack kernel plus the remote vacuum residual.
This file records the geometric propagation of the local kernel itself.

The local recursive iterate is defined here directly.  Keeping this carrier
local avoids importing the older full-edge Dobrushin stack, whose independent
legacy measurable-space instance conflicts with the current continuous-vacuum
import lane.

The key facts are:

* the local kernel is symmetric because intrinsic active-neighbor adjacency is
  symmetric;
* every row, as well as every column, is bounded by `18 * eta(beta)`;
* a nonzero degree-`d` recursive local coefficient can move the embedded
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
    constructor
    · intro hActive
      have hAdj :
          (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj source target :=
        (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
          H source target).mpr hActive
      exact
        (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
          H target source).mp hAdj.symm
    · intro hActive
      have hAdj :
          (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj target source :=
        (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
          H target source).mpr hActive
      exact
        (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
          H source target).mp hAdj.symm
  change
    (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence beta
    else 0) =
    (if source ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H target then
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence beta
    else 0)
  by_cases hActive :
      target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
  · have hActive' :
        source ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H target :=
      hMem.mp hActive
    simp only [hActive, hActive', if_true]
  · have hActive' :
        source ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H target := by
      intro h
      exact hActive (hMem.mpr h)
    simp only [hActive, hActive', if_false]

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

/-- Recursive powers of the physical local Harnack influence kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ℕ →
      PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpatialSliceLink H → ℝ
  | 0, target, source => if target = source then 1 else 0
  | d + 1, target, source =>
      ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence target mid *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
          H beta hbeta d mid source

/-- Every local-Harnack iterate coefficient is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ d : ℕ,
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
            H beta hbeta d target source := by
  intro d
  induction d with
  | zero =>
      intro target source
      by_cases hEq : target = source
      · simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel, hEq]
      · simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel, hEq]
  | succ d ih =>
      intro target source
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel]
      exact
        Finset.sum_nonneg fun mid _ =>
          mul_nonneg
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence_nonneg target mid)
            (ih mid source)

/-- Degree-`d` local-Harnack row mass is bounded by
`(18 * eta(beta))^d`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_rowSum_le_pow
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ d : ℕ,
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
            H beta hbeta d target source) ≤
          (18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta) ^ d := by
  intro d
  induction d with
  | zero =>
      intro target
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel,
        pow_zero]
      rw [Finset.sum_eq_single target]
      · simp
      · intro source _ hsource
        have hne : target ≠ source := by
          exact fun h => hsource h.symm
        simp [hne]
      · intro htarget
        exact False.elim (htarget (Finset.mem_univ target))
  | succ d ih =>
      intro target
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
            (∑ f : PeriodicHypercubicEvenSpatialSliceLink H,
              K.influence e f) ≤ rho := by
        intro e
        simpa [K, rho, finiteInfluenceKernelRowSum] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_le_eighteen_mul
            H beta hbeta e
      change
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target mid *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
                H beta hbeta d mid source) ≤
          rho ^ (d + 1)
      rw [Finset.sum_comm]
      calc
        (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target mid *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
                H beta hbeta d mid source) =
            ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
              K.influence target mid *
                (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
                    H beta hbeta d mid source) := by
          apply Finset.sum_congr rfl
          intro mid _
          rw [Finset.mul_sum]
        _ ≤ ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
              K.influence target mid * rho ^ d := by
          apply Finset.sum_le_sum
          intro mid _
          exact
            mul_le_mul_of_nonneg_left
              (by simpa [rho] using ih mid)
              (K.influence_nonneg target mid)
        _ = (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
              K.influence target mid) * rho ^ d := by
          rw [Finset.sum_mul]
        _ ≤ rho * rho ^ d := by
          exact
            mul_le_mul_of_nonneg_right
              (hRow target)
              (pow_nonneg hRho d)
        _ = rho ^ (d + 1) := by
          rw [pow_succ]
          ring

/-- A nonzero degree-`d` local-Harnack coefficient connects two spatial
links whose embedded periodic link-base L1 distance is at most `2*d`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_ne_zero_imp_baseL1Distance_le_two_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ d : ℕ,
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
            H beta hbeta d target source ≠ 0 →
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
        simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel,
          hTargetSource]
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
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
                H beta hbeta d mid source ≠ 0 := by
        by_contra hNone
        push Not at hNone
        apply hNe
        change
          (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target mid *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
                H beta hbeta d mid source) = 0
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
            2 * d :=
        ih mid source hParts.2
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_eq_zero_of_two_mul_le_baseL1Distance
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
        H beta hbeta d target source = 0 := by
  by_contra hNe
  have hUpper :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_ne_zero_imp_baseL1Distance_le_two_mul
      H beta hbeta d target source hNe
  omega

/-- Every degree-`d` local-Harnack coefficient is bounded by the explicit
volume-independent power `(18 * eta(beta))^d`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_le_pow
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (d : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
        H beta hbeta d target source ≤
      (18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) ^ d := by
  have hSingle :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
          H beta hbeta d target source ≤
        ∑ other : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
            H beta hbeta d target other := by
    exact
      Finset.single_le_sum
        (fun other _ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_nonneg
            H beta hbeta d target other)
        (Finset.mem_univ source)
  exact
    hSingle.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_rowSum_le_pow
        H beta hbeta d target)

end

end MathlibAnalytic
end MGAP4D
