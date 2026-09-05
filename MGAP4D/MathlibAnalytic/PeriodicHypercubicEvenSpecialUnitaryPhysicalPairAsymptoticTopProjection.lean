import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopPowerDecay
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct Topology

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairAsymptoticTopProjectionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairAsymptoticTopProjectionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairAsymptoticTopProjectionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairAsymptoticTopProjectionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairAsymptoticTopProjectionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairAsymptoticTopProjectionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairAsymptoticTopProjectionSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section AsymptoticTopProjection

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "TTspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan H N hN beta hbeta
local notation "TT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "PP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N

/-- Normalized pair transfer fixes the entire completed top-top block, not only
its decomposable generators.  The extension from the algebraic span is through
the closed kernel of `S₂ - id`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_fixed
    (t : PairE) (ht : t ∈ TT) :
    S₂ t = t := by
  let A : PairE →L[ℝ] PairE := S₂ - ContinuousLinearMap.id ℝ PairE
  have hspan : TTspan ≤ A.ker := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan]
    refine Submodule.span_le.2 ?_
    rintro z ⟨⟨u, v⟩, rfl⟩
    change A
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
        H N hN beta hbeta u v) = 0
    simp [A,
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_top_top]
  have hclosure : TT ≤ A.ker := by
    change TTspan.topologicalClosure ≤ A.ker
    exact TTspan.topologicalClosure_minimal hspan A.isClosed_ker
  have htA := hclosure ht
  change A t = 0 at htA
  have hzero : S₂ t - t = 0 := by
    simpa [A] using htA
  exact sub_eq_zero.mp hzero

/-- Every power of normalized pair transfer fixes the completed top-top block. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_pow_fixed
    (k : ℕ) (t : PairE) (ht : t ∈ TT) :
    (S₂ ^ k) t = t := by
  induction k with
  | zero => simp
  | succ k ih =>
      change (S₂ ^ k) (S₂ t) = t
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_fixed
        H N hN beta hbeta t ht]
      exact ih

/-- On the completed non-top sector, powers of normalized pair transfer converge
strongly to zero at every fixed finite volume. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_tendsto_zero
    (n : PairE) (hn : n ∈ NN) :
    Tendsto (fun k : ℕ => (S₂ ^ k) n) atTop (nhds 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) ?_
  · rw [dist_zero_right]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
        H N hN beta hbeta k n hn
  · have hpow : Tendsto (fun k : ℕ => ‖R‖ ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg R)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one
          H N hN beta hbeta)
    have hmul :
        Tendsto (fun k : ℕ => ‖R‖ ^ k * ‖n‖) atTop (nhds (0 * ‖n‖)) :=
      hpow.mul tendsto_const_nhds
    simpa using hmul

/-- Quantitative approach of any completed physical pair vector to its completed
top-top orthogonal projection. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_sub_topProjection_norm_le
    (k : ℕ) (x : PairE) (hx : x ∈ PP) :
    ‖(S₂ ^ k) x - TT.starProjection x‖ ≤
      ‖R‖ ^ k * ‖(TTᗮ).starProjection x‖ := by
  have hn : (TTᗮ).starProjection x ∈ NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_mem_nonTop
      H N hN beta hbeta x hx
  have ht : TT.starProjection x ∈ TT :=
    Submodule.starProjection_apply_mem TT x
  have hsplit : TT.starProjection x + (TTᗮ).starProjection x = x := by
    calc
      TT.starProjection x + (TTᗮ).starProjection x =
          TT.starProjection x + (x - TT.starProjection x) := by
        rw [Submodule.starProjection_orthogonal_val (K := TT)]
      _ = x := by abel
  calc
    ‖(S₂ ^ k) x - TT.starProjection x‖ =
        ‖(S₂ ^ k) ((TTᗮ).starProjection x)‖ := by
      rw [← hsplit, map_add,
        periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_pow_fixed
          H N hN beta hbeta k (TT.starProjection x) ht]
      simp
    _ ≤ ‖R‖ ^ k * ‖(TTᗮ).starProjection x‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
        H N hN beta hbeta k ((TTᗮ).starProjection x) hn

/-- At each fixed finite volume, normalized physical pair-transfer powers
converge strongly on the completed physical pair carrier to the orthogonal
projection onto the full completed top-top block.  This is deliberately a
full-top-sector statement and does not assert vacuum uniqueness. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_tendsto_topProjection
    (x : PairE) (hx : x ∈ PP) :
    Tendsto (fun k : ℕ => (S₂ ^ k) x) atTop (nhds (TT.starProjection x)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) ?_
  · rw [dist_eq_norm]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_sub_topProjection_norm_le
        H N hN beta hbeta k x hx
  · have hpow : Tendsto (fun k : ℕ => ‖R‖ ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg R)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one
          H N hN beta hbeta)
    have hmul :
        Tendsto
          (fun k : ℕ => ‖R‖ ^ k * ‖(TTᗮ).starProjection x‖)
          atTop
          (nhds (0 * ‖(TTᗮ).starProjection x‖)) :=
      hpow.mul tendsto_const_nhds
    simpa using hmul

/-- Audit-visible finite-volume asymptotic projection package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAsymptoticTopProjectionPackage :
    Prop where
  topFixed :
    ∀ t : PairE, t ∈ TT → S₂ t = t
  topPowerFixed :
    ∀ (k : ℕ) (t : PairE), t ∈ TT → (S₂ ^ k) t = t
  nonTopStrongZero :
    ∀ n : PairE, n ∈ NN →
      Tendsto (fun k : ℕ => (S₂ ^ k) n) atTop (nhds 0)
  quantitativeProjection :
    ∀ (k : ℕ) (x : PairE), x ∈ PP →
      ‖(S₂ ^ k) x - TT.starProjection x‖ ≤
        ‖R‖ ^ k * ‖(TTᗮ).starProjection x‖
  strongTopProjection :
    ∀ x : PairE, x ∈ PP →
      Tendsto (fun k : ℕ => (S₂ ^ k) x) atTop (nhds (TT.starProjection x))

/-- Construct the finite-volume asymptotic top-projection package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairAsymptoticTopProjectionPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAsymptoticTopProjectionPackage
      H N hN beta hbeta :=
  { topFixed :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_fixed
        H N hN beta hbeta
    topPowerFixed :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_pow_fixed
        H N hN beta hbeta
    nonTopStrongZero :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_tendsto_zero
        H N hN beta hbeta
    quantitativeProjection :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_sub_topProjection_norm_le
        H N hN beta hbeta
    strongTopProjection :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_tendsto_topProjection
        H N hN beta hbeta }

end AsymptoticTopProjection

end

end MathlibAnalytic
end MGAP4D
