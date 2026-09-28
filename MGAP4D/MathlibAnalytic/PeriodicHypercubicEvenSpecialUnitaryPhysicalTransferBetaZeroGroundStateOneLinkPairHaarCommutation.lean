import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateOneLinkPairHaarTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkRetainedCoordinateBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarRangeInvariant
import MGAP4D.MathlibAnalytic.RealHilbertRangeInvariantProjectionCommute
import Mathlib.Tactic

/-!
# Beta-zero one-link pair-Haar commutation

The one-link retained sigma-algebras are now available as literal coordinate
restrictions on the pair-Haar joint carrier.  The generic product-Haar
conditional-expectation theorem from the six-color beta-zero analysis therefore
applies link by link.

This unit proves:

* conditioning on one pair-Haar off-target sigma-algebra preserves
  measurability with respect to every other off-target sigma-algebra;
* pairwise range invariance of the literal one-link projections;
* pairwise commutation of those projections;
* the fixed-color specialization used by the canonical same-color sweep.

No Wilson interaction estimate is used: this is exact beta-zero product-Haar
geometry.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroOneLinkPairHaarCommutationTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroOneLinkPairHaarCommutationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroOneLinkPairHaarCommutationSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroOneLinkPairHaarCommutationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroOneLinkPairHaarCommutationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroOneLinkPairHaarCommutationMetrizableSpace (N : ℕ) :
    TopologicalSpace.MetrizableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  inferInstance

local instance betaZeroOneLinkPairHaarCommutationCompletelyMetrizableSpace (N : ℕ) :
    TopologicalSpace.IsCompletelyMetrizableSpace
      (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  letI : MetricSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    TopologicalSpace.metrizableSpaceMetric
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  letI : CompleteSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := inferInstance
  exact MetricSpace.toIsCompletelyMetrizableSpace

local instance betaZeroOneLinkPairHaarCommutationPolishSpace (N : ℕ) :
    PolishSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  exact
    { toSecondCountableTopology :=
        betaZeroOneLinkPairHaarCommutationSecondCountableTopology N
      toIsCompletelyMetrizableSpace :=
        betaZeroOneLinkPairHaarCommutationCompletelyMetrizableSpace N }

local instance betaZeroOneLinkPairHaarCommutationStandardBorelSpace (N : ℕ) :
    StandardBorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  inferInstance

local instance betaZeroOneLinkPairHaarCommutationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Under pair Haar, conditioning on one off-target retained sigma-algebra
preserves AE strong measurability with respect to every other off-target
retained sigma-algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStatePairHaar_condExp_spatialLink_preserves_spatialLink
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hsource : AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N source]
      f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))
    (hfInt :
      Integrable f
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N source]
      ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)[
        f |
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target])
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  classical
  let I := PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let η : Measure G := normalizedCompactHaar G
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N
  let p : I → Prop := fun i =>
    i ∈ periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet
      H target
  let q : I → Prop := fun i =>
    i ∈ periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet
      H source
  let T := pairHaarPiThreeWayMeasurableEquiv (K := G) p q
  let e3 := E.trans T
  let ρ := Measure.pi (fun _ : PairHaarPiCommonIndex p q => η)
  let μ := Measure.pi (fun _ : PairHaarPiLeftOnlyIndex p q => η)
  let ν := Measure.pi (fun _ : PairHaarPiRightOnlyIndex p q => η)

  have he :
      MeasurePreserving E
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (Measure.pi (fun _ : I => η)) := by
    simpa [E, I, G, η] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
        H N

  have hT :
      MeasurePreserving T
        (Measure.pi (fun _ : I => η))
        ((ρ.prod μ).prod ν) := by
    simpa [T, ρ, μ, ν] using
      pairHaarPiThreeWayMeasurableEquiv_measurePreserving η p q

  have he3 :
      MeasurePreserving e3
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        ((ρ.prod μ).prod ν) := by
    exact he.trans hT

  have hpSpace :
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target =
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) p) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // p i} → G)) := by
    rw [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_retainedCoordinateRestriction,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction_eq_piRestriction_comp]

  have hqSpace :
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N source =
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) q) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // q i} → G)) := by
    rw [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_retainedCoordinateRestriction,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction_eq_piRestriction_comp]

  have hsource' :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) q) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // q i} → G))]
        f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    rw [← hqSpace]
    exact hsource

  have hrightLePi :=
    pairHaarPiRestriction_right_comap_le_threeWay_right (K := G) p q
  have hrightLe :
      MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) q) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // q i} → G)) ≤
        MeasurableSpace.comap
          (fun x => ((e3 x).1.1, (e3 x).2))
          (inferInstance : MeasurableSpace
            ((PairHaarPiCommonIndex p q → G) ×
              (PairHaarPiRightOnlyIndex p q → G))) := by
    have h := MeasurableSpace.comap_mono (g := E) hrightLePi
    simpa [e3, T, Function.comp_def, MeasurableSpace.comap_comp] using
      (show
        MeasurableSpace.comap E
            (MeasurableSpace.comap
              (pairHaarPiRestriction (K := G) q)
              (inferInstance : MeasurableSpace ({i : I // q i} → G))) ≤
          MeasurableSpace.comap E
            (MeasurableSpace.comap
              (fun x : I → G =>
                ((T x).1.1, (T x).2))
              (inferInstance : MeasurableSpace
                ((PairHaarPiCommonIndex p q → G) ×
                  (PairHaarPiRightOnlyIndex p q → G)))) from h)

  have hright :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (fun x => ((e3 x).1.1, (e3 x).2))
          (inferInstance : MeasurableSpace
            ((PairHaarPiCommonIndex p q → G) ×
              (PairHaarPiRightOnlyIndex p q → G)))]
        f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
    hsource'.mono hrightLe

  have hcollapse :=
    condExp_sharedBase_aestronglyMeasurable_of_measurePreserving_equiv
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      ρ μ ν e3 he3 f hright hfInt

  have hleftPi :=
    pairHaarPiThreeWay_left_comap_eq_restriction (K := G) p q
  have hleft :
      MeasurableSpace.comap
          (fun x => (e3 x).1)
          (inferInstance : MeasurableSpace
            ((PairHaarPiCommonIndex p q → G) ×
              (PairHaarPiLeftOnlyIndex p q → G))) =
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) p) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // p i} → G)) := by
    have h := congrArg (fun m => MeasurableSpace.comap E m) hleftPi
    simpa [e3, T, Function.comp_def, MeasurableSpace.comap_comp] using h

  have hbaseLePi :=
    pairHaarPiThreeWay_base_comap_le_restriction_right (K := G) p q
  have hbaseLe :
      MeasurableSpace.comap
          (fun x => (e3 x).1.1)
          (inferInstance : MeasurableSpace (PairHaarPiCommonIndex p q → G)) ≤
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) q) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // q i} → G)) := by
    have h := MeasurableSpace.comap_mono (g := E) hbaseLePi
    simpa [e3, T, Function.comp_def, MeasurableSpace.comap_comp] using
      (show
        MeasurableSpace.comap E
            (MeasurableSpace.comap
              (fun x : I → G => (T x).1.1)
              (inferInstance : MeasurableSpace
                (PairHaarPiCommonIndex p q → G))) ≤
          MeasurableSpace.comap E
            (MeasurableSpace.comap
              (pairHaarPiRestriction (K := G) q)
              (inferInstance : MeasurableSpace ({i : I // q i} → G))) from h)

  rw [hleft] at hcollapse
  have htarget := hcollapse.mono hbaseLe
  rw [← hpSpace, ← hqSpace] at htarget
  exact htarget

/-- The literal beta-zero pair-Haar one-link projection family is pairwise
range-invariant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_range_invariant
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N)
    (hx : x ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N source).toLinearMap.range) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N target x ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N source).toLinearMap.range := by
  rcases hx with ⟨y, rfl⟩

  have hzMeas :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N source]
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N source y :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    change
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N source]
        ((condExpL2 ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
            H N source)
          y :
            lpMeas ℝ ℝ
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
                H N source)
              2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
    exact lpMeas.aestronglyMeasurable _

  have hzInt :
      Integrable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N source y :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    rw [← memLp_one_iff_integrable]
    exact
      (Lp.memLp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N source y)).mono_exponent (by norm_num)

  have hcondMeas :=
    periodicHypercubicEvenSpecialUnitaryGroundStatePairHaar_condExp_spatialLink_preserves_spatialLink
      H N target source
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N source y :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      hzMeas hzInt

  let htargetLe :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N target

  have hL2Cond :
      (condExpL2 ℝ ℝ htargetLe
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N source y) :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)[
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
            H N source y :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) |
          periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
            H N target] := by
    simpa [htargetLe] using
      (Lp.memLp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N source y)).condExpL2_ae_eq_condExp
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
          H N target)

  have htargetMeas :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N source]
        ((condExpL2 ℝ ℝ htargetLe
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
            H N source y) :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    exact hcondMeas.congr hL2Cond.symm

  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N source ≤
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
    ⟨periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N source⟩

  let q :
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N source)
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
    ⟨
      (condExpL2 ℝ ℝ htargetLe
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N source y) :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N),
      mem_lpMeas_iff_aestronglyMeasurable.mpr htargetMeas
    ⟩

  refine ⟨
    (condExpL2 ℝ ℝ htargetLe
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N source y) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N), ?_⟩

  have hq :
      (condExpL2 ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
          H N source)
        (q :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
        lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
            H N source)
          2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q

  have hCoe := congrArg
    (fun u : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N source)
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =>
      (u :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N))
    hq

  simpa [q, htargetLe] using hCoe

/-- Literal beta-zero one-link pair-Haar projections commute pairwise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_commute
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N source x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
          H N target x) := by
  exact
    realHilbertProjection_commute_of_range_invariant
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
        H N source)
      (fun a b =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_symmetric
          H N target a b)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_idempotent
        H N source)
      (fun a b =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_symmetric
          H N source a b)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_range_invariant
        H N target source)
      x

/-- Fixed-color form of pairwise one-link pair-Haar commutation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection_commute
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e d : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
        H N color e
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
          H N color d x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
        H N color d
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
          H N color e x) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_commute
      H N e.1 d.1 x

end

end MGAP4D.MathlibAnalytic
