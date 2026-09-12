import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialFixedMeasurability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasureEquivalence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

set_option maxHeartbeats 1000000

local instance groundStateTwelveSpatialCommonFixedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateTwelveSpatialCommonFixedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateTwelveSpatialCommonFixedSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateTwelveSpatialCommonFixedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateTwelveSpatialCommonFixedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateTwelveSpatialCommonFixedSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Mutual absolute continuity upgrades to an exact equivalence of a.e.
identities between the genuine Wilson ground-state joint law and pair Haar.
This is only a null-set statement; no `L²` norm comparison is asserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_ae_eq_iff_pairHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {Z : Type*}
    (f g :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → Z) :
    f =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta] g ↔
      f =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N] g := by
  constructor
  · intro hfg
    exact
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
        H N hN beta hbeta).ae_eq hfg
  · intro hfg
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
        H N hN beta hbeta).ae_eq hfg

/-- One genuine right-color conditional expectation fixes a vector exactly when
that vector belongs to its actual retained-information `L²` subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_iff_mem_lpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN beta hbeta color z = z ↔
      z ∈ lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_mem_lpMeas
        H N hN beta hbeta color z
  · intro hz
    let hm :=
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
        H N color
    letI : Fact
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N color ≤
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
      ⟨hm⟩
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
      ⟨z, hz⟩
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_apply]
    have hq :
        (condExpL2 ℝ ℝ hm
          (q : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta) :
          lpMeas ℝ ℝ
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
              H N color) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
              H N hN beta hbeta)) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    have hCoe := congrArg
      (fun x : lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N color) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) =>
        (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta)) hq
    simpa [q] using hCoe

/-- Left-color counterpart of the exact fixed-range characterization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_fixed_iff_mem_lpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
        H N hN beta hbeta color z = z ↔
      z ∈ lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_fixed_mem_lpMeas
        H N hN beta hbeta color z
  · intro hz
    let hm :=
      periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
        H N color
    letI : Fact
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
            H N color ≤
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
      ⟨hm⟩
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
      ⟨z, hz⟩
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_apply]
    have hq :
        (condExpL2 ℝ ℝ hm
          (q : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta) :
          lpMeas ℝ ℝ
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
              H N color) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
              H N hN beta hbeta)) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    have hCoe := congrArg
      (fun x : lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
            H N color) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) =>
        (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta)) hq
    simpa [q] using hCoe

/-- Being fixed by all six right updates is exactly membership in the concrete
intersection of the six right-update retained-information `L²` ranges. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_fixed_iff_mem_rightSixRetained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (∀ c : Fin 6,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
        H N hN beta hbeta c z = z) ↔
      z ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
          H N hN beta hbeta := by
  constructor
  · intro hfixed
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas,
      Submodule.mem_iInf]
    intro c
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_iff_mem_lpMeas
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) z).1
        (hfixed c)
  · intro hz
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas,
      Submodule.mem_iInf] at hz
    intro c
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_iff_mem_lpMeas
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) z).2
        (hz c)

/-- Being fixed by all six left updates is exactly membership in the concrete
intersection of the six left-update retained-information `L²` ranges. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_fixed_iff_mem_leftSixRetained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (∀ c : Fin 6,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
        H N hN beta hbeta c z = z) ↔
      z ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
          H N hN beta hbeta := by
  constructor
  · intro hfixed
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas,
      Submodule.mem_iInf]
    intro c
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_fixed_iff_mem_lpMeas
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) z).1
        (hfixed c)
  · intro hz
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas,
      Submodule.mem_iInf] at hz
    intro c
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_fixed_iff_mem_lpMeas
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) z).2
        (hz c)

/-- Exact concrete description of the twelve-color common-fixed sector: it is
the intersection of the right-six and left-six retained-information `L²`
intersections.  No identification with constants is made here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff_mem_rightSix_leftSix_retained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (∀ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta c z = z) ↔
      z ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
            H N hN beta hbeta ∧
        z ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
            H N hN beta hbeta := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_mem_rightSix_leftSix_retained
        H N hN beta hbeta z
  · rintro ⟨hright, hleft⟩
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff
        H N hN beta hbeta z).2
        ⟨(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_fixed_iff_mem_rightSixRetained
            H N hN beta hbeta z).2 hright,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_fixed_iff_mem_leftSixRetained
            H N hN beta hbeta z).2 hleft⟩

/-- Every genuine left-boundary pullback belongs to the entire intersection of
right-update retained-information ranges.  The open coordinate-elimination
seam is the reverse inclusion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry_mem_rightSixRetained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
        H N hN beta hbeta u ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas,
    Submodule.mem_iInf]
  intro c
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry_mem_spatialColor_lpMeas
      H N hN beta hbeta
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) u

/-- Every genuine right-boundary pullback belongs to the entire intersection of
left-update retained-information ranges.  The open coordinate-elimination
seam is again the reverse inclusion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry_mem_leftSixRetained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
        H N hN beta hbeta u ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas,
    Submodule.mem_iInf]
  intro c
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry_mem_leftSpatialColor_lpMeas
      H N hN beta hbeta
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) u

end

end MathlibAnalytic
end MGAP4D
