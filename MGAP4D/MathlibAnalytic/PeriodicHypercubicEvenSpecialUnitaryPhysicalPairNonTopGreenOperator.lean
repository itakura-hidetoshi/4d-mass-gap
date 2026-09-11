import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealResolventBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- Generic right-inverse identity for the resolvent at the real point `1`.
Keeping this argument carrier-independent avoids unfolding the physical-pair
carrier inside the ring-inverse calculation. -/
private theorem continuousLinearMap_oneShift_resolvent_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (hres : (1 : ℝ) ∈ resolventSet ℝ T) (y : E) :
    (resolvent T (1 : ℝ)) y - T ((resolvent T (1 : ℝ)) y) = y := by
  have hmul :
      (algebraMap ℝ (E →L[ℝ] E) (1 : ℝ) - T) *
          resolvent T (1 : ℝ) = 1 := by
    unfold resolvent
    exact Ring.mul_inverse_cancel _ hres
  have happly := congrArg (fun F : E →L[ℝ] E => F y) hmul
  simpa [ContinuousLinearMap.algebraMap_apply] using happly

/-- Generic left-inverse identity for the resolvent at the real point `1`. -/
private theorem continuousLinearMap_resolvent_oneShift_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (hres : (1 : ℝ) ∈ resolventSet ℝ T) (x : E) :
    (resolvent T (1 : ℝ)) (x - T x) = x := by
  have hmul :
      resolvent T (1 : ℝ) *
          (algebraMap ℝ (E →L[ℝ] E) (1 : ℝ) - T) = 1 := by
    unfold resolvent
    exact Ring.inverse_mul_cancel _ hres
  have happly := congrArg (fun F : E →L[ℝ] E => F x) hmul
  simpa [ContinuousLinearMap.algebraMap_apply] using happly

local instance physicalPairNonTopGreenTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairNonTopGreenCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairNonTopGreenSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairNonTopGreenMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairNonTopGreenBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairNonTopGreenSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairNonTopGreenSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section NonTopGreenOperator

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator H N hN beta hbeta

/-- The finite-volume non-top Green operator is the real resolvent at `1`,
i.e. the inverse of `I - SN` on the completed non-top sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator :
    NN →L[ℝ] NN :=
  resolvent SN (1 : ℝ)

/-- The finite-volume Green denominator is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_gap_positive :
    0 < 1 - ‖R‖ := by
  exact sub_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one
      H N hN beta hbeta)

/-- The Green operator is a right inverse of `I - SN`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_rightInverse
    (y : NN) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator
        H N hN beta hbeta y -
      SN
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator
          H N hN beta hbeta y) = y := by
  have hfactor : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one
      H N hN beta hbeta
  have hres : (1 : ℝ) ∈ resolventSet ℝ SN := by
    apply
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_mem_realResolventSet_of_factor_lt_abs
        H N hN beta hbeta (1 : ℝ)
    simpa using hfactor
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator] using
    continuousLinearMap_oneShift_resolvent_apply SN hres y

/-- The Green operator is also a left inverse of `I - SN`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_leftInverse
    (x : NN) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator
        H N hN beta hbeta (x - SN x) = x := by
  have hfactor : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one
      H N hN beta hbeta
  have hres : (1 : ℝ) ∈ resolventSet ℝ SN := by
    apply
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_mem_realResolventSet_of_factor_lt_abs
        H N hN beta hbeta (1 : ℝ)
    simpa using hfactor
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator] using
    continuousLinearMap_resolvent_oneShift_apply SN hres x

/-- Pointwise finite-volume Green estimate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_apply_norm_le
    (y : NN) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator
        H N hN beta hbeta y‖ ≤
      (1 - ‖R‖)⁻¹ * ‖y‖ := by
  have hfactor : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one
      H N hN beta hbeta
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_bound
      H N hN beta hbeta (1 : ℝ) (by simpa using hfactor) y)

/-- Operator norm of the finite-volume Green operator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_norm_le :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator
        H N hN beta hbeta‖ ≤
      (1 - ‖R‖)⁻¹ := by
  have hfactor : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one
      H N hN beta hbeta
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_le
      H N hN beta hbeta (1 : ℝ) (by simpa using hfactor))

/-- Every finite-volume completed non-top Poisson equation
`x - SN x = y` has exactly one solution, namely the Green image of `y`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_existsUnique
    (y : NN) :
    ∃! x : NN, x - SN x = y := by
  let G : NN →L[ℝ] NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator
      H N hN beta hbeta
  have hright : G y - SN (G y) = y := by
    dsimp [G]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_rightInverse
        H N hN beta hbeta y
  refine ⟨G y, hright, ?_⟩
  intro x hx
  have hleft : G (x - SN x) = x := by
    dsimp [G]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_leftInverse
        H N hN beta hbeta x
  calc
    x = G (x - SN x) := hleft.symm
    _ = G y := congrArg (fun z : NN => G z) hx

end NonTopGreenOperator

end

end MathlibAnalytic
end MGAP4D
