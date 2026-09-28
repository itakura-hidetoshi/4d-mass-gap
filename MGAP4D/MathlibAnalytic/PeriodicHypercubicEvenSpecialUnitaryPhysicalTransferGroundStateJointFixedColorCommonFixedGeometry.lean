import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSameColorOneLinkSweepEqualsColorBlock
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepContractionReceiver
import Mathlib.Tactic

/-!
# Fixed-color one-link common-fixed geometry at arbitrary beta

The retained sigma-algebras are geometric and do not depend on the coupling.
At positive beta the one-link conditional-expectation projections need not
commute, but their common fixed space can still be identified exactly.

Mutual absolute continuity of the genuine ground-state joint law and pair Haar
lets us perform the finite retained-support intersection in literal product
coordinates.  PRs #4885 and #4886 then show that intersecting every off-target
support in one fixed spatial color leaves exactly the off-color support.

Consequently, for every nonnegative beta,

  all same-color one-link projections fix x
    iff
  the genuine spatial-color projection fixes x.

No positive-beta commutativity is asserted or needed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance fixedColorCommonFixedGeometryTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedColorCommonFixedGeometryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedColorCommonFixedGeometrySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedColorCommonFixedGeometryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedColorCommonFixedGeometryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedColorCommonFixedGeometrySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One genuine ground-state one-link conditional expectation fixes a vector
exactly when the vector belongs to its retained-information L2 subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_fixed_iff_mem_lpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target x = x ↔
      x ∈ lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target)
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N target
  constructor
  · intro hfixed
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target)
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
      condExpL2 ℝ ℝ hm x
    have hq :
        (q :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta) = x := by
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
      ⟨x, hx⟩
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply]
    have hq :
        (condExpL2 ℝ ℝ hm
          (q :
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta) :
          lpMeas ℝ ℝ
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
              H N target)
            2
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
              H N hN beta hbeta)) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    have hCoe := congrArg
      (fun z : lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
            H N target)
          2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) =>
        (z :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta))
      hq
    simpa [q] using hCoe

/-- At every nonnegative beta, simultaneous fixedness under every one-link
projection of one spatial color is exactly fixedness under the genuine
spatial-color block projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_commonFixed_iff_color_fixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (∀ e : PeriodicHypercubicEvenFixedSpatialColorLink H color,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta e.1 x = x) ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN beta hbeta color x = x := by
  classical
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let I := PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let η : Measure G := normalizedCompactHaar G
  let ω := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N
  let cs :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
  let p :
      PeriodicHypercubicEvenFixedSpatialColorLink H color → I → Prop :=
    fun e i =>
      i ∈ periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet
        H e.1
  constructor
  · intro hfixed
    have he :
        MeasurePreserving E ω (Measure.pi (fun _ : I => η)) := by
      simpa [E, I, G, η, ω] using
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
          H N
    have hcs : cs ≠ [] := by
      simpa [cs] using
        periodicHypercubicEvenFixedSpatialColorLink_univ_toList_ne_nil H color
    have hEach :
        ∀ e ∈ cs,
          PairHaarSupportAEStronglyMeasurable
            ω E (p e) (x : X × X → ℝ) := by
      intro e _he
      have hmem :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_fixed_iff_mem_lpMeas
          H N hN beta hbeta e.1 x).1 (hfixed e)
      have hmeasJoint :=
        mem_lpMeas_iff_aestronglyMeasurable.mp hmem
      have hmeasPair :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
            H N e.1)
          (x : X × X → ℝ)).1 hmeasJoint
      rw [
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_retainedCoordinateRestriction,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction_eq_piRestriction_comp]
        at hmeasPair
      simpa [PairHaarSupportAEStronglyMeasurable, X, I, G, ω, E, p] using
        hmeasPair
    have hall :=
      aestronglyMeasurable_piRestriction_iInter_list_of_measurePreserving_equiv
        ω η E he p cs hcs (x : X × X → ℝ) hEach
    have hpred :
        (fun i : I => ∀ e ∈ cs, p e i) =
          (fun i : I =>
            i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
              H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color)) := by
      simpa [I, p, cs] using
        periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet_fixedColor_univList
          H color
    have hall' :
        PairHaarSupportAEStronglyMeasurable
          ω E
          (fun i : I =>
            i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
              H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color))
          (x : X × X → ℝ) := by
      rw [← hpred]
      exact hall
    have hcolorSpace :
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N color =
          MeasurableSpace.comap
            ((pairHaarPiRestriction (K := G)
              (fun i : I =>
                i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
                  H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color))) ∘ E)
            (inferInstance : MeasurableSpace
              ({i : I //
                i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
                  H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color)} → G)) := by
      have h :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedCoordinateRestriction
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin color)
      rw [
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_piRestriction_comp]
        at h
      simpa [E, I, G] using h
    have hcolorPair :
        AEStronglyMeasurable[
          periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N color]
          (x : X × X → ℝ) ω := by
      rw [hcolorSpace]
      simpa [PairHaarSupportAEStronglyMeasurable, X, I, G, ω, E] using hall'
    have hcolorJoint :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color)
        (x : X × X → ℝ)).2 hcolorPair
    apply
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_iff_mem_lpMeas
        H N hN beta hbeta color x).2
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr hcolorJoint
  · intro hcolor
    have hcolorMem :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_iff_mem_lpMeas
        H N hN beta hbeta color x).1 hcolor
    intro e
    apply
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_fixed_iff_mem_lpMeas
        H N hN beta hbeta e.1 x).2
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hcolorMem ⊢
    exact hcolorMem.mono <| by
      simpa [e.2] using
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le_spatialLink
          H N e.1

/-- At arbitrary nonnegative beta, the canonical complete same-color one-link
sweep has exactly the same fixed vectors as the genuine color block.  This
uses only self-adjoint idempotence of the individual one-link projections; no
cross-link commutativity is required. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweep_fixed_iff_color_fixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta color x = x ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN beta hbeta color x = x := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let cs :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
  change realHilbertProjectionSweep P cs x = x ↔ _
  rw [
    realHilbertProjectionSweep_apply_eq_self_iff_forall_mem_fixed
      P
      (fun e => by
        simpa [P,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
            H N hN beta hbeta e.1)
      (fun e a b =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
          H N hN beta hbeta e.1 a b)
      cs x]
  have hcommon :
      (∀ e ∈ cs, P e x = x) ↔
        ∀ e : PeriodicHypercubicEvenFixedSpatialColorLink H color,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e.1 x = x := by
    simp [cs, P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2]
  rw [hcommon]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_commonFixed_iff_color_fixed
      H N hN beta hbeta color x

end

end MGAP4D.MathlibAnalytic
