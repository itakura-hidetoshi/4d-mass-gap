import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAsymptoticTopProjection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct Topology

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairFixedSpaceTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairFixedSpaceCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairFixedSpaceSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairFixedSpaceMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairFixedSpaceBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairFixedSpaceSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairFixedSpaceSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section FixedSpaceCharacterization

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "TT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "PP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N

local instance physicalPairFixedSpaceTopTopCompleteSpace : CompleteSpace TT := by
  have hclosed : IsClosed (TT : Set PairE) := by
    change IsClosed
      (((periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
          H N hN beta hbeta).topologicalClosure : Submodule ℝ PairE) : Set PairE)
    exact Submodule.isClosed_topologicalClosure _
  exact hclosed.completeSpace_coe

/-- Inside the completed physical pair carrier, a vector is fixed by normalized
pair transfer exactly when it lies in the full completed top-top block.  The
reverse implication is the completed top-block fixed theorem.  For the forward
implication, all powers remain at the fixed vector, while the finite-volume
asymptotic theorem sends those same powers to the top-top orthogonal projection;
uniqueness of limits identifies the vector with that projection. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_fixed_iff_mem_topTopBlockClosure
    (x : PairE) (hx : x ∈ PP) :
    S₂ x = x ↔ x ∈ TT := by
  constructor
  · intro hfix
    have hpow : ∀ k : ℕ, (S₂ ^ k) x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          change (S₂ ^ k) (S₂ x) = x
          rw [hfix]
          exact ih
    have hfun : (fun k : ℕ => (S₂ ^ k) x) = fun _ : ℕ => x := by
      funext k
      exact hpow k
    have hself : Tendsto (fun k : ℕ => (S₂ ^ k) x) atTop (nhds x) := by
      rw [hfun]
      exact tendsto_const_nhds
    have htop :
        Tendsto
          (fun k : ℕ => (S₂ ^ k) x)
          atTop
          (nhds ((TT).starProjection x)) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_tendsto_topProjection
        H N hN beta hbeta x hx
    have heq : x = (TT).starProjection x :=
      tendsto_nhds_unique hself htop
    rw [heq]
    exact Submodule.starProjection_apply_mem TT x
  · intro ht
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_fixed
        H N hN beta hbeta x ht

/-- The relative eigenvalue-one fixed submodule of normalized pair transfer is
exactly the completed top-top block.  The intersection with the physical pair
carrier is essential; no statement is made about fixed vectors in the ambient
pair Haar space outside the physical carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_inf_normalizedTransfer_sub_id_ker_eq_topTopBlockClosure :
    PP ⊓ (S₂ - ContinuousLinearMap.id ℝ PairE).ker = TT := by
  apply le_antisymm
  · intro x hx
    have hxP : x ∈ PP := hx.1
    have hxK := hx.2
    have hfix : S₂ x = x := by
      change S₂ x - x = 0 at hxK
      exact sub_eq_zero.mp hxK
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_fixed_iff_mem_topTopBlockClosure
        H N hN beta hbeta x hxP).1 hfix
  · intro x hxT
    refine ⟨?_, ?_⟩
    · exact
        periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_le_physicalPairCarrier
          H N hN beta hbeta hxT
    · change S₂ x - x = 0
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_fixed
        H N hN beta hbeta x hxT]
      exact sub_self x

/-- There is no nonzero normalized-transfer fixed vector in the completed
non-top block.  This does not assert that the full top-top block is one
dimensional. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_fixed_eq_zero
    (n : PairE) (hn : n ∈ NN) (hfix : S₂ n = n) :
    n = 0 := by
  have hnP : n ∈ PP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_le_physicalPairCarrier
      H N hN beta hbeta hn
  have hnT : n ∈ TT :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_fixed_iff_mem_topTopBlockClosure
      H N hN beta hbeta n hnP).1 hfix
  have hOrtho : TT ⟂ NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_isOrtho_nonTopBlockClosure
      H N hN beta hbeta
  have hinner : inner ℝ n n = 0 :=
    hOrtho.inner_eq hnT hn
  exact inner_self_eq_zero.mp hinner

/-- Audit-visible finite-volume fixed-space characterization package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterizationPackage :
    Prop where
  fixedIffTop :
    ∀ x : PairE, x ∈ PP →
      (S₂ x = x ↔ x ∈ TT)
  relativeFixedSubmodule :
    PP ⊓ (S₂ - ContinuousLinearMap.id ℝ PairE).ker = TT
  nonTopFixedZero :
    ∀ n : PairE, n ∈ NN → S₂ n = n → n = 0

/-- Construct the finite-volume fixed-space characterization package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterizationPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterizationPackage
      H N hN beta hbeta :=
  { fixedIffTop :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_fixed_iff_mem_topTopBlockClosure
        H N hN beta hbeta
    relativeFixedSubmodule :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_inf_normalizedTransfer_sub_id_ker_eq_topTopBlockClosure
        H N hN beta hbeta
    nonTopFixedZero :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_fixed_eq_zero
        H N hN beta hbeta }

end FixedSpaceCharacterization

end

end MathlibAnalytic
end MGAP4D
