import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialGenuinePairHaarTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkConditionalExpectation
import Mathlib.Tactic

/-!
# Beta-zero one-link pair-Haar transport

At beta zero the genuine ground-state joint law is exactly the literal
spatial pair-Haar law.  The six-spatial color projections have already been
transported across that exact measure equality.  This unit exposes the
corresponding literal pair-Haar projection for one selected right-boundary
spatial link and proves the same exact transport statement link by link.

The construction is deliberately lossless:

* no Harnack comparison;
* no response coefficient;
* no finite-cardinality estimate;
* no commutativity assumption.

It provides the carrier needed to compare a complete same-color one-link
sweep with the beta-zero color block projection.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroOneLinkPairHaarTransportTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroOneLinkPairHaarTransportCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroOneLinkPairHaarTransportSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroOneLinkPairHaarTransportMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroOneLinkPairHaarTransportBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroOneLinkPairHaarTransportSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal pair-Haar conditional-expectation projection retaining the full
left boundary and all right-boundary coordinates except one selected link. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  (Submodule.subtypeL
    (lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target) 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))).comp
    (condExpL2 ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
        H N target))

/-- Literal application formula for one pair-Haar one-link projection. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_apply
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
        H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N target f =
      (condExpL2 ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
          H N target) f :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
          H N) := by
  rfl

/-- Each literal pair-Haar one-link conditional expectation is idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_idempotent
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
      H N target).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N target) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
      H N target := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_apply]
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N target
  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target ≤
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
    ⟨hm⟩
  let q : lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target) 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
    condExpL2 ℝ ℝ hm f
  change
    ((condExpL2 ℝ ℝ hm
      (q :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
          H N) :
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target) 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
        H N) = q
  have hq :
      (condExpL2 ℝ ℝ hm
        (q :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
            H N) :
        lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
            H N target) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q
  exact congrArg
    (fun x : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target) 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =>
      (x :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
          H N)) hq

/-- Each literal pair-Haar one-link conditional expectation is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_symmetric
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
      H N target :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N).IsSymmetric := by
  intro f g
  change
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N target f) g =
      inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N target g)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_apply]
  exact inner_condExpL2_left_eq_right
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N target)

/-- One literal pair-Haar one-link projection fixes a vector exactly when the
vector belongs to the corresponding retained-information L2 subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_fixed_iff_mem_lpMeas
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N target x = x ↔
      x ∈ lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target)
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N target
  constructor
  · intro hfixed
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target)
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
      condExpL2 ℝ ℝ hm x
    have hq :
        (q :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) =
          x := by
      simpa [q, hm] using hfixed
    rw [← hq]
    exact q.property
  · intro hx
    letI : Fact
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
            H N target ≤
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
      ⟨hm⟩
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target)
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
      ⟨x, hx⟩
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_apply]
    have hq :
        (condExpL2 ℝ ℝ hm
          (q :
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
          lpMeas ℝ ℝ
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
              H N target)
            2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    have hCoe := congrArg
      (fun z : lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
            H N target)
          2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =>
        (z :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N))
      hq
    simpa [q] using hCoe

/-- The exact beta-zero joint cast intertwines the genuine one-link conditional
expectation with its literal pair-Haar one-link projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_spatialLinkCondExp
    (H N : ℕ)
    (hN : 0 < N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN 0 (by norm_num) target z) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN z) := by
  let hJoint :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN
  change
    realL2CastOfMeasureEq hJoint
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN 0 (by norm_num) target z) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N target
        (realL2CastOfMeasureEq hJoint z)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_apply]
  exact
    realL2CastOfMeasureEq_condExpL2
      (m0 := (Prod.instMeasurableSpace :
        MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
      (m :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
        H N target)
      hJoint z

end

end MGAP4D.MathlibAnalytic
