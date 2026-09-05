import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairReducedTransferRangeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairReducedTransferRangeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairReducedTransferRangeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairReducedTransferRangeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairReducedTransferRangeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairReducedTransferRangeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairReducedTransferRangeSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section ReducedTransferRange

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
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator H N hN beta hbeta
local notation "G" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator H N hN beta hbeta
local notation "D" =>
  ContinuousLinearMap.id ℝ PairE - S₂

/-- On the completed physical pair carrier, `I - S₂` lands in the completed
non-top block.  The top component cancels because normalized pair transfer fixes
the full completed top-top block. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_id_sub_normalizedTransfer_mem_nonTop
    (x : PairE) (hx : x ∈ PP) :
    x - S₂ x ∈ NN := by
  rcases
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_exists_topTop_add_nonTop
      H N hN beta hbeta x hx with
    ⟨t, ht, n, hn, hsum⟩
  have hfix : S₂ t = t :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_fixed
      H N hN beta hbeta t ht
  have hSn : S₂ n ∈ NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_invariant
      H N hN beta hbeta hn
  have heq : x - S₂ x = n - S₂ n := by
    calc
      x - S₂ x = (t + n) - S₂ (t + n) := by rw [hsum]
      _ = (t + n) - (t + S₂ n) := by rw [map_add, hfix]
      _ = n - S₂ n := by abel
  rw [heq]
  exact (NN).sub_mem hn hSn

/-- Every completed non-top vector has a completed non-top preimage under
`I - S₂`, with the finite-volume Green bound.  This is a reduced inverse
statement only; no inverse is asserted on the full physical carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_exists_reduced_preimage_norm_le
    (n : PairE) (hn : n ∈ NN) :
    ∃ y : PairE,
      y ∈ NN ∧
      y - S₂ y = n ∧
      ‖y‖ ≤ (1 - ‖R‖)⁻¹ * ‖n‖ := by
  let nN : NN := ⟨n, hn⟩
  let yN : NN := G nN
  have hrightN : yN - SN yN = nN := by
    dsimp [yN]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_rightInverse
        H N hN beta hbeta nN
  have hrightVal := congrArg (fun z : NN => (z : PairE)) hrightN
  have hright : (yN : PairE) - S₂ (yN : PairE) = n := by
    simpa [nN] using hrightVal
  have hboundN : ‖yN‖ ≤ (1 - ‖R‖)⁻¹ * ‖nN‖ := by
    dsimp [yN]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_apply_norm_le
        H N hN beta hbeta nN
  have hbound : ‖(yN : PairE)‖ ≤ (1 - ‖R‖)⁻¹ * ‖n‖ := by
    simpa [nN] using hboundN
  exact ⟨(yN : PairE), yN.property, hright, hbound⟩

/-- The image of `I - S₂` on the completed physical pair carrier is exactly the
completed non-top block.  Together with the fixed-space theorem, this gives the
finite-volume kernel/range split without asserting top-sector simplicity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_map_id_sub_normalizedTransfer_eq_nonTopBlockClosure :
    (PP).map D.toLinearMap = NN := by
  apply le_antisymm
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    change x - S₂ x ∈ NN
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_id_sub_normalizedTransfer_mem_nonTop
        H N hN beta hbeta x hx
  · intro n hn
    rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_exists_reduced_preimage_norm_le
        H N hN beta hbeta n hn with
      ⟨y, hyN, hyEq, _⟩
    have hyP : y ∈ PP :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_le_physicalPairCarrier
        H N hN beta hbeta hyN
    refine ⟨y, hyP, ?_⟩
    change y - S₂ y = n
    exact hyEq

/-- Equivalently, the finite-volume reduced range of `I - S₂` is the orthogonal
complement of the completed top-top block relative to the physical pair carrier.
The intersection with `PP` is essential; no ambient full-Haar equality is claimed. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_map_id_sub_normalizedTransfer_eq_carrier_inf_topTopOrthogonal :
    (PP).map D.toLinearMap = PP ⊓ (TT)ᗮ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_map_id_sub_normalizedTransfer_eq_nonTopBlockClosure
    H N hN beta hbeta]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopClosure_eq_carrier_inf_topTopOrthogonal
      H N hN beta hbeta

/-- The reduced preimage is unique inside the completed non-top block. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_existsUnique_reduced_preimage
    (n : PairE) (hn : n ∈ NN) :
    ∃! y : NN, (y : PairE) - S₂ (y : PairE) = n := by
  let nN : NN := ⟨n, hn⟩
  rcases
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator_existsUnique
      H N hN beta hbeta nN with
    ⟨y, hy, hyUnique⟩
  refine ⟨y, ?_, ?_⟩
  · have hyVal := congrArg (fun z : NN => (z : PairE)) hy
    simpa [nN] using hyVal
  · intro z hz
    apply hyUnique z
    apply Subtype.ext
    simpa [nN] using hz

/-- Audit-visible finite-volume reduced transfer range package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairReducedTransferRangePackage :
    Prop where
  carrierDifferenceNonTop :
    ∀ x : PairE, x ∈ PP → x - S₂ x ∈ NN
  rangeEqNonTop :
    (PP).map D.toLinearMap = NN
  relativeOrthogonalRange :
    (PP).map D.toLinearMap = PP ⊓ (TT)ᗮ
  quantitativePreimage :
    ∀ n : PairE, n ∈ NN →
      ∃ y : PairE,
        y ∈ NN ∧ y - S₂ y = n ∧
          ‖y‖ ≤ (1 - ‖R‖)⁻¹ * ‖n‖
  uniqueReducedPreimage :
    ∀ n : PairE, n ∈ NN →
      ∃! y : NN, (y : PairE) - S₂ (y : PairE) = n

/-- Construct the finite-volume reduced transfer range package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairReducedTransferRangePackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairReducedTransferRangePackage
      H N hN beta hbeta :=
  { carrierDifferenceNonTop :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_id_sub_normalizedTransfer_mem_nonTop
        H N hN beta hbeta
    rangeEqNonTop :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_map_id_sub_normalizedTransfer_eq_nonTopBlockClosure
        H N hN beta hbeta
    relativeOrthogonalRange :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_map_id_sub_normalizedTransfer_eq_carrier_inf_topTopOrthogonal
        H N hN beta hbeta
    quantitativePreimage :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_exists_reduced_preimage_norm_le
        H N hN beta hbeta
    uniqueReducedPreimage :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_existsUnique_reduced_preimage
        H N hN beta hbeta }

end ReducedTransferRange

end

end MathlibAnalytic
end MGAP4D
