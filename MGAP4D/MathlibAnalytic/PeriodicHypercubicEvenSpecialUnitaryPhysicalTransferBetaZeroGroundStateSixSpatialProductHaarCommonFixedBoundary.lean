import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarTensorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateSixRetainedBoundaryEquality
import Mathlib.Tactic

/-!
# Beta-zero six-spatial pair-Haar common-fixed boundary sector

This file identifies the fixed sector of the actual beta-zero six-spatial
pair-Haar full sweep with the complete left-boundary measurable L2 subspace.

No new centering object is introduced.  The proof reuses:

* the actual full-sweep fixed-vector characterization;
* the exact range geometry of each pair-Haar conditional expectation;
* the previously proved six-retained boundary equality;
* the exact beta-zero ground-state joint law = pair-Haar law.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroPairHaarCommonFixedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroPairHaarCommonFixedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroPairHaarCommonFixedSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroPairHaarCommonFixedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroPairHaarCommonFixedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroPairHaarCommonFixedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One actual beta-zero pair-Haar color projection fixes a vector exactly
when the vector belongs to the corresponding retained-information L2
subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_fixed_iff_mem_lpMeas
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
        H N color x = x ↔
      x ∈ lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color)
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
      H N color
  constructor
  · intro hfixed
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color)
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
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N color ≤
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
      ⟨hm⟩
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color)
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
      ⟨x, hx⟩
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_apply]
    have hq :
        (condExpL2 ℝ ℝ hm
          (q :
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
          lpMeas ℝ ℝ
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
              H N color)
            2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    have hCoe := congrArg
      (fun z : lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N color)
          2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =>
        (z :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N))
      hq
    simpa [q] using hCoe

/-- The intersection of the six actual beta-zero pair-Haar retained subspaces
is exactly the complete left-boundary measurable L2 subspace.  This is the
literal pair-Haar specialization of the previously proved ground-state
six-retained equality. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRetained_eq_fst
    (H N : ℕ)
    (hN : 0 < N) :
    (⨅ c : Fin 6,
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) =
      lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas_eq_fst
      H N hN 0 (by norm_num)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN] at h
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas]
    using h

/-- Canonical identification of the actual beta-zero six-spatial full-sweep
fixed sector: it is precisely the complete left-boundary measurable L2
subspace on the literal pair-Haar carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_self_iff_mem_fst
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
        H N x = x ↔
      x ∈ lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_self_iff]
  have hEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRetained_eq_fst
      H N hN
  constructor
  · intro hfixed
    rw [← hEq, Submodule.mem_iInf]
    intro c
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_fixed_iff_mem_lpMeas
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) x).1
        (hfixed c)
  · intro hx
    rw [← hEq, Submodule.mem_iInf] at hx
    intro c
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_fixed_iff_mem_lpMeas
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) x).2
        (hx c)

end

end MGAP4D.MathlibAnalytic
