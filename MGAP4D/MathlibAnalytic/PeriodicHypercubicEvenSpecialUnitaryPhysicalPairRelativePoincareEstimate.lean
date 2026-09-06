import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAsymptoticTopProjection

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
local notation "PP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N

/-- At each fixed finite volume, the one-step transfer residual controls the
component orthogonal to the full completed top-top block.  The proof is a direct
consequence of the already established one-step approach-to-top estimate and the
triangle inequality; no top-sector simplicity is used. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_residual_coercive
    (x : PairE) (hx : x ∈ PP) :
    (1 - ‖R‖) * ‖((TT)ᗮ).starProjection x‖ ≤ ‖x - S₂ x‖ := by
  have hstep :
      ‖S₂ x - (TT).starProjection x‖ ≤
        ‖R‖ * ‖((TT)ᗮ).starProjection x‖ := by
    simpa using
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_sub_topProjection_norm_le
        H N hN beta hbeta 1 x hx)
  have htri := norm_add_le (x - S₂ x) (S₂ x - (TT).starProjection x)
  have hsum :
      (x - S₂ x) + (S₂ x - (TT).starProjection x) =
        x - (TT).starProjection x := by
    abel
  rw [hsum] at htri
  have horth :
      ‖((TT)ᗮ).starProjection x‖ = ‖x - (TT).starProjection x‖ := by
    rw [Submodule.starProjection_orthogonal_val (K := TT)]
  rw [← horth] at htri
  nlinarith

/-- Equivalent finite-volume Poincare form written as distance from the full
completed top-top orthogonal projection. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_sub_topProjection_residual_coercive
    (x : PairE) (hx : x ∈ PP) :
    (1 - ‖R‖) * ‖x - (TT).starProjection x‖ ≤ ‖x - S₂ x‖ := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_relativeOrthogonal_residual_coercive
      H N hN beta hbeta x hx
  rw [Submodule.starProjection_orthogonal_val (K := TT)] at h
  exact h

end RelativePoincareEstimate

end

end MathlibAnalytic
end MGAP4D
