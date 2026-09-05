import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAsymptoticTopProjection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferCoercivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairRelativePoincareTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairRelativePoincareCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairRelativePoincareSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairRelativePoincareMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairRelativePoincareBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairRelativePoincareSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairRelativePoincareSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section RelativePoincareEstimate

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "TT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "PP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N

/-- At each fixed finite volume, the transfer residual controls the component
orthogonal to the full completed top-top block.  This is relative to the physical
pair carrier and does not assert that the top block is one-dimensional. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_residual_coercive
    (x : PairE) (hx : x ∈ PP) :
    (1 - ‖R‖) * ‖((TT)ᗮ).starProjection x‖ ≤ ‖x - S₂ x‖ := by
  let t : PairE := (TT).starProjection x
  let n : PairE := ((TT)ᗮ).starProjection x
  have hn : n ∈ NN := by
    dsimp [n]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_mem_nonTop
        H N hN beta hbeta x hx
  have ht : t ∈ TT := by
    dsimp [t]
    exact Submodule.starProjection_apply_mem (TT) x
  have hsplit : t + n = x := by
    dsimp [t, n]
    calc
      (TT).starProjection x + ((TT)ᗮ).starProjection x =
          (TT).starProjection x + (x - (TT).starProjection x) := by
        rw [Submodule.starProjection_orthogonal_val (K := TT)]
      _ = x := by abel
  have hfix : S₂ t = t :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_fixed
      H N hN beta hbeta t ht
  have hres : x - S₂ x = n - S₂ n := by
    calc
      x - S₂ x = (t + n) - S₂ (t + n) := by rw [hsplit]
      _ = (t + n) - (t + S₂ n) := by rw [map_add, hfix]
      _ = n - S₂ n := by abel
  have hcoerc : (1 - ‖R‖) * ‖n‖ ≤ ‖n - S₂ n‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_id_sub_normalizedTransfer_coercive
      H N hN beta hbeta n hn
  calc
    (1 - ‖R‖) * ‖((TT)ᗮ).starProjection x‖ =
        (1 - ‖R‖) * ‖n‖ := by rfl
    _ ≤ ‖n - S₂ n‖ := hcoerc
    _ = ‖x - S₂ x‖ := by rw [hres]

/-- Equivalent Poincare form: the residual controls the norm-distance from `x`
to its orthogonal projection onto the full completed top-top block. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_sub_topProjection_residual_coercive
    (x : PairE) (hx : x ∈ PP) :
    (1 - ‖R‖) * ‖x - (TT).starProjection x‖ ≤ ‖x - S₂ x‖ := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_residual_coercive
      H N hN beta hbeta x hx
  rw [Submodule.starProjection_orthogonal_val (K := TT)] at h
  exact h

/-- Quantitative finite-volume Poincare estimate in inverse-factor form.  The
constant depends on the fixed finite-volume data through `R`; no scale-uniform
lower bound is claimed. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_norm_le_residual
    (x : PairE) (hx : x ∈ PP) :
    ‖((TT)ᗮ).starProjection x‖ ≤
      (1 - ‖R‖)⁻¹ * ‖x - S₂ x‖ := by
  have hcoerc :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_residual_coercive
      H N hN beta hbeta x hx
  have hdelta : 0 < 1 - ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferResidualFactor_pos
      H N hN beta hbeta
  have hdiv :
      ‖((TT)ᗮ).starProjection x‖ ≤ ‖x - S₂ x‖ / (1 - ‖R‖) := by
    exact (le_div_iff₀ hdelta).2 (by simpa [mul_comm] using hcoerc)
  calc
    ‖((TT)ᗮ).starProjection x‖ ≤ ‖x - S₂ x‖ / (1 - ‖R‖) := hdiv
    _ = (1 - ‖R‖)⁻¹ * ‖x - S₂ x‖ := by rw [inv_mul_eq_div]

/-- Distance-to-top formulation of the same finite-volume Poincare estimate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_dist_topProjection_le_residual
    (x : PairE) (hx : x ∈ PP) :
    dist x ((TT).starProjection x) ≤
      (1 - ‖R‖)⁻¹ * ‖x - S₂ x‖ := by
  rw [dist_eq_norm]
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_norm_le_residual
      H N hN beta hbeta x hx
  rw [Submodule.starProjection_orthogonal_val (K := TT)] at h
  exact h

/-- Audit-visible finite-volume relative Poincare package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairRelativePoincarePackage :
    Prop where
  relativeOrthogonalCoercive :
    ∀ x : PairE, x ∈ PP →
      (1 - ‖R‖) * ‖((TT)ᗮ).starProjection x‖ ≤ ‖x - S₂ x‖
  projectionDistanceCoercive :
    ∀ x : PairE, x ∈ PP →
      (1 - ‖R‖) * ‖x - (TT).starProjection x‖ ≤ ‖x - S₂ x‖
  relativeOrthogonalPoincare :
    ∀ x : PairE, x ∈ PP →
      ‖((TT)ᗮ).starProjection x‖ ≤
        (1 - ‖R‖)⁻¹ * ‖x - S₂ x‖
  distancePoincare :
    ∀ x : PairE, x ∈ PP →
      dist x ((TT).starProjection x) ≤
        (1 - ‖R‖)⁻¹ * ‖x - S₂ x‖

/-- Construct the finite-volume relative Poincare package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairRelativePoincarePackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairRelativePoincarePackage
      H N hN beta hbeta :=
  { relativeOrthogonalCoercive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_residual_coercive
        H N hN beta hbeta
    projectionDistanceCoercive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_sub_topProjection_residual_coercive
        H N hN beta hbeta
    relativeOrthogonalPoincare :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_norm_le_residual
        H N hN beta hbeta
    distancePoincare :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_dist_topProjection_le_residual
        H N hN beta hbeta }

end RelativePoincareEstimate

end

end MathlibAnalytic
end MGAP4D
