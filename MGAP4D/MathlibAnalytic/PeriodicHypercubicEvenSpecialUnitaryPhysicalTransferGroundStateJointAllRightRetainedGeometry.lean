import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointFixedColorCommonFixedGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateSixRetainedBoundaryEquality

/-!
# All right-link fixed vectors retain exactly the left boundary

Reuse the existing fixed-color geometry and six-retained boundary equality.
The projection below is the literal fst-sigma-algebra condExpL2 on the SAME
joint measure. It is not a projection to constants, and no equality with a
separately presented boundary-adjoint operator is used without proof.
All results in this file hold at every nonnegative coupling.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype

namespace GroundStateSourceFixedPairEnergy

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "X" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "muJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "LeftSigma" => MeasurableSpace.comap (Prod.fst : X × X → X) (inferInstance : MeasurableSpace X)
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta

/-- Literal conditional expectation retaining the complete left boundary. -/
def allRightLeftRetainedCondExpL2 : JL2 →L[ℝ] JL2 :=
  (Submodule.subtypeL (lpMeas ℝ ℝ LeftSigma 2 muJ)).comp
    (condExpL2 (μ := muJ) (m := LeftSigma) ℝ ℝ measurable_fst.comap_le)

local notation "Cleft" => allRightLeftRetainedCondExpL2 H N hN beta hbeta

/-- The fixed range is the literal retained-information subspace. -/
theorem allRightLeftRetained_fixed_iff_mem (f : JL2) :
    Cleft f = f ↔ f ∈ lpMeas ℝ ℝ LeftSigma 2 muJ := by
  constructor
  · intro h
    rw [← h]
    exact (condExpL2 (μ := muJ) (m := LeftSigma) ℝ ℝ measurable_fst.comap_le f).property
  · intro hf
    letI : Fact (LeftSigma ≤ (inferInstance : MeasurableSpace (X × X))) :=
      ⟨measurable_fst.comap_le⟩
    let q : lpMeas ℝ ℝ LeftSigma 2 muJ := ⟨f, hf⟩
    have hq : condExpL2 (μ := muJ) (m := LeftSigma) ℝ ℝ measurable_fst.comap_le
        (q : JL2) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    exact congrArg (fun z : lpMeas ℝ ℝ LeftSigma 2 muJ => (z : JL2)) hq

theorem allRightLeftRetained_idempotent : (Cleft).comp Cleft = Cleft := by
  apply ContinuousLinearMap.ext
  intro f
  exact (allRightLeftRetained_fixed_iff_mem H N hN beta hbeta (Cleft f)).mpr
    (condExpL2 (μ := muJ) (m := LeftSigma) ℝ ℝ measurable_fst.comap_le f).property

theorem allRightLeftRetained_symmetric (f g : JL2) :
    inner ℝ (Cleft f) g = inner ℝ f (Cleft g) :=
  inner_condExpL2_left_eq_right (𝕜 := ℝ) measurable_fst.comap_le

/-- Every right-link projection fixes f exactly when f is left-boundary
measurable. The opposite boundary is NOT discarded. -/
theorem allRightLink_fixed_iff_leftRetained (f : JL2) :
    (∀ e : PeriodicHypercubicEvenSpatialSliceLink H, P e f = f) ↔ Cleft f = f := by
  constructor
  · intro hFixed
    have hColors : ∀ color : PeriodicHypercubicEvenGroundStateSpatialColor,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color f = f := by
      intro color
      exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_commonFixed_iff_color_fixed
        H N hN beta hbeta color f).mp (fun e => hFixed e.1)
    have hMem : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
        H N hN beta hbeta := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas,
        Submodule.mem_iInf]
      intro c
      exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_mem_lpMeas
        H N hN beta hbeta (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
        (hColors _)
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas_eq_fst
      H N hN beta hbeta] at hMem
    exact (allRightLeftRetained_fixed_iff_mem H N hN beta hbeta f).mpr hMem
  · intro hFixed e
    have hMem := (allRightLeftRetained_fixed_iff_mem H N hN beta hbeta f).mp hFixed
    apply (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_fixed_iff_mem_lpMeas
      H N hN beta hbeta e f).mpr
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hMem ⊢
    exact hMem.mono le_sup_left

/-- Orthogonal projection duality gives absorption, with no link commutation. -/
theorem allRightLeftRetained_absorb_link
    (e : PeriodicHypercubicEvenSpatialSliceLink H) (f : JL2) : Cleft (P e f) = Cleft f := by
  apply ext_inner_right ℝ
  intro g
  have hIdem : Cleft (Cleft g) = Cleft g := by
    exact congrArg (fun A : JL2 →L[ℝ] JL2 => A g)
      (allRightLeftRetained_idempotent H N hN beta hbeta)
  have hFixed : P e (Cleft g) = Cleft g :=
    (allRightLink_fixed_iff_leftRetained H N hN beta hbeta (Cleft g)).mpr hIdem e
  calc
    inner ℝ (Cleft (P e f)) g = inner ℝ (P e f) (Cleft g) :=
      allRightLeftRetained_symmetric H N hN beta hbeta _ _
    _ = inner ℝ f (P e (Cleft g)) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e f (Cleft g)
    _ = inner ℝ f (Cleft g) := by rw [hFixed]
    _ = inner ℝ (Cleft f) g := (allRightLeftRetained_symmetric H N hN beta hbeta f g).symm

theorem allRightLeftRetained_absorb_sweep
    (sources : List (PeriodicHypercubicEvenSpatialSliceLink H)) (f : JL2) :
    Cleft (realHilbertProjectionSweep P sources f) = Cleft f :=
  realHilbertNestedBlock_projectionSweep_absorb Cleft P sources
    (fun e _ g => allRightLeftRetained_absorb_link H N hN beta hbeta e g) f

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
