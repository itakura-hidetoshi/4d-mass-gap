import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarTensorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarBoundaryAEMeasurability
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

/-- If a literal pair-Haar function is retained-measurable for every one of
the six right-update color sigma-algebras, then it is measurable with respect
to the complete left boundary.  This is the cast-free literal-carrier form of
the finite-product coordinate-elimination step underlying the six-retained
boundary theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStatePairHaar_rightSix_aestronglyMeasurable_fst
    (H N : ℕ)
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hcolors : ∀ c : Fin 6,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
        f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
      f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  classical
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let I := PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let η : Measure G := normalizedCompactHaar G
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N

  have he :
      MeasurePreserving E
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (Measure.pi (fun _ : I => η)) := by
    simpa [E, I, G, η] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
        H N

  have hcolors' : ∀ c : Fin 6,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G)
            (fun i : I => i ∈
              periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c)) ∘ E)
          (inferInstance : MeasurableSpace
            ({i : I // i ∈
              periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c} → G))]
        f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    intro c
    have hc := hcolors c
    rw [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedCoordinateRestriction]
      at hc
    rw [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_piRestriction_comp]
      at hc
    simpa [X, I, G, E] using hc

  have hall :=
    aestronglyMeasurable_piRestriction_iInter_finSix_of_measurePreserving_equiv
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      η E he
      (fun c i => i ∈
        periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c)
      f hcolors'

  have hpred :
      (fun i : I => ∀ c : Fin 6,
        i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c) =
      (fun i : I => i ∈
        periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H) := by
    funext i
    apply propext
    constructor
    · intro hi
      have hi' :
          i ∈ ⋂ c : Fin 6,
            periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c := by
        simpa only [Set.mem_iInter] using hi
      rw [
        periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet_iInter_eq_leftBoundary H]
        at hi'
      exact hi'
    · intro hi
      have hi' :
          i ∈ ⋂ c : Fin 6,
            periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c := by
        rw [
          periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet_iInter_eq_leftBoundary H]
        exact hi
      simpa only [Set.mem_iInter] using hi'

  rw [hpred] at hall

  have hboundaryMeasurable :
      Measurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace X)]
        ((pairHaarPiRestriction (K := G)
          (fun i : I => i ∈
            periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H)) ∘ E) := by
    letI : MeasurableSpace (X × X) :=
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace X)
    change Measurable
      ((pairHaarPiRestriction (K := G)
        (fun i : I => i ∈
          periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H)) ∘ E)
    rw [measurable_pi_iff]
    intro i
    rcases i with ⟨i, hi⟩
    cases i with
    | inl e =>
        have heq :
            (fun x : X × X =>
              ((pairHaarPiRestriction (K := G)
                (fun i : I => i ∈
                  periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H)) ∘ E)
                x ⟨Sum.inl e, hi⟩) =
              (fun x : X × X => x.1 e) := by
          funext x
          rfl
        rw [heq]
        exact
          (measurable_pi_apply e).comp
            (measurable_iff_comap_le.mpr le_rfl)
    | inr e =>
        change False at hi
        contradiction

  exact hall.mono (measurable_iff_comap_le.mp hboundaryMeasurable)

/-- The intersection of the six actual beta-zero pair-Haar retained subspaces
is exactly the complete left-boundary measurable L2 subspace.  This is proved
directly on the literal pair-Haar carrier, avoiding any dependent cast between
equal-measure Lp types. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRetained_eq_fst
    (H N : ℕ) :
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
  apply le_antisymm
  · intro x hx
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    apply
      periodicHypercubicEvenSpecialUnitaryGroundStatePairHaar_rightSix_aestronglyMeasurable_fst
        H N
        (x :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    rw [Submodule.mem_iInf] at hx
    intro c
    exact mem_lpMeas_iff_aestronglyMeasurable.mp (hx c)
  · intro x hx
    rw [Submodule.mem_iInf]
    intro c
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    exact
      (mem_lpMeas_iff_aestronglyMeasurable.mp hx).mono
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftMeasurableSpace_le_spatialColor
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))

/-- Canonical identification of the actual beta-zero six-spatial full-sweep
fixed sector: it is precisely the complete left-boundary measurable L2
subspace on the literal pair-Haar carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_self_iff_mem_fst
    (H N : ℕ)
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
      H N
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
