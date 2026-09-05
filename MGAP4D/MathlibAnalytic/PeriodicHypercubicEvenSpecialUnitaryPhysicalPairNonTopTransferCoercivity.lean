import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairNonTopCoercivityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairNonTopCoercivityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairNonTopCoercivitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairNonTopCoercivityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairNonTopCoercivityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairNonTopCoercivitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairNonTopCoercivitySpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section NonTopTransferCoercivity

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator H N hN beta hbeta

/-- The finite-volume residual factor inherited from strict non-top contraction
is positive.  No scale-uniform lower bound is asserted. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferResidualFactor_pos :
    0 < 1 - ‖R‖ := by
  exact sub_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta)

/-- On the ambient realization of the completed physical non-top block, the
residual of normalized pair transfer controls the vector norm with factor
`1 - ‖R‖`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_id_sub_normalizedTransfer_coercive
    (x : PairE) (hx : x ∈ NN) :
    (1 - ‖R‖) * ‖x‖ ≤ ‖x - S₂ x‖ := by
  have hS : ‖S₂ x‖ ≤ ‖R‖ * ‖x‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_norm_le
      H N hN beta hbeta x hx
  have htri := norm_add_le (x - S₂ x) (S₂ x)
  rw [sub_add_cancel] at htri
  nlinarith

/-- The bundled completed non-top transfer has the same quantitative residual
lower bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_id_sub_coercive
    (x : NN) :
    (1 - ‖R‖) * ‖x‖ ≤ ‖x - SN x‖ := by
  have hSN : ‖SN‖ ≤ ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le
      H N hN beta hbeta
  have hApply0 : ‖SN x‖ ≤ ‖SN‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        H N hN beta hbeta) x
  have hApply : ‖SN x‖ ≤ ‖R‖ * ‖x‖ :=
    hApply0.trans
      (mul_le_mul_of_nonneg_right hSN (norm_nonneg x))
  have htri := norm_add_le (x - SN x) (SN x)
  rw [sub_add_cancel] at htri
  nlinarith

/-- The residual operator `id - SN` has trivial kernel on the completed non-top
sector, quantitatively strengthening the absence of nonzero fixed vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopIdSubTransfer_ker_eq_bot :
    (ContinuousLinearMap.id ℝ NN - SN).ker = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hzero : x - SN x = 0 := by
      simpa using hx
    have hcoerc :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_id_sub_coercive
        H N hN beta hbeta x
    rw [hzero, norm_zero] at hcoerc
    have hdelta : 0 < 1 - ‖R‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferResidualFactor_pos
        H N hN beta hbeta
    have hxnorm : ‖x‖ = 0 := by
      nlinarith [norm_nonneg x]
    have hxzero : x = 0 := norm_eq_zero.mp hxnorm
    simpa [hxzero]
  · exact bot_le

/-- Every unit vector in the completed non-top sector stays a definite positive
distance from being fixed by normalized transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_unit_residual_ge
    (x : NN) (hx : ‖x‖ = 1) :
    1 - ‖R‖ ≤ ‖x - SN x‖ := by
  have hcoerc :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_id_sub_coercive
      H N hN beta hbeta x
  simpa [hx] using hcoerc

/-- Audit-visible finite-volume non-top transfer coercivity package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferCoercivityPackage :
    Prop where
  residualFactorPositive : 0 < 1 - ‖R‖
  ambientCoercive :
    ∀ x : PairE, x ∈ NN →
      (1 - ‖R‖) * ‖x‖ ≤ ‖x - S₂ x‖
  restrictedCoercive :
    ∀ x : NN,
      (1 - ‖R‖) * ‖x‖ ≤ ‖x - SN x‖
  residualKernelTrivial :
    (ContinuousLinearMap.id ℝ NN - SN).ker = ⊥
  unitResidual :
    ∀ x : NN, ‖x‖ = 1 →
      1 - ‖R‖ ≤ ‖x - SN x‖

/-- Construct the finite-volume non-top transfer coercivity package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferCoercivityPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferCoercivityPackage
      H N hN beta hbeta :=
  { residualFactorPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferResidualFactor_pos
        H N hN beta hbeta
    ambientCoercive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_id_sub_normalizedTransfer_coercive
        H N hN beta hbeta
    restrictedCoercive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_id_sub_coercive
        H N hN beta hbeta
    residualKernelTrivial :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopIdSubTransfer_ker_eq_bot
        H N hN beta hbeta
    unitResidual :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_unit_residual_ge
        H N hN beta hbeta }

end NonTopTransferCoercivity

end

end MathlibAnalytic
end MGAP4D
