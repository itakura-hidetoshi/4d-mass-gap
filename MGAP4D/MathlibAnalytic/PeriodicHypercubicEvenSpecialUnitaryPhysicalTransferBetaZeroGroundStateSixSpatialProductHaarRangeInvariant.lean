import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarProjectionGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarBoundaryAEMeasurability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarPiAEIntersection
import MGAP4D.MathlibAnalytic.ProductProbabilitySharedBaseConditionalExpectation
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic

/-!
# Beta-zero six-spatial pair-Haar range invariance

This file connects the product-probability shared-base conditional expectation
collapse to the actual Wilson two-boundary pair-Haar color projections.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory

noncomputable section

local instance betaZeroRangeInvariantTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroRangeInvariantCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroRangeInvariantSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroRangeInvariantMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroRangeInvariantBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroRangeInvariantMetrizableSpace (N : ℕ) :
    TopologicalSpace.MetrizableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  inferInstance

local instance betaZeroRangeInvariantCompletelyMetrizableSpace (N : ℕ) :
    TopologicalSpace.IsCompletelyMetrizableSpace
      (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  letI : MetricSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    TopologicalSpace.metrizableSpaceMetric
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  letI : CompleteSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := inferInstance
  exact MetricSpace.toIsCompletelyMetrizableSpace

local instance betaZeroRangeInvariantPolishSpace (N : ℕ) :
    PolishSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  exact
    { toSecondCountableTopology := betaZeroRangeInvariantSecondCountableTopology N
      toIsCompletelyMetrizableSpace :=
        betaZeroRangeInvariantCompletelyMetrizableSpace N }

local instance betaZeroRangeInvariantStandardBorelSpace (N : ℕ) :
    StandardBorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  inferInstance

local instance betaZeroRangeInvariantSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Conditional expectation shared-base collapse transported across an exact
measure-preserving measurable equivalence to a three-factor product
probability space. -/
theorem condExp_sharedBase_aestronglyMeasurable_of_measurePreserving_equiv
    {Ω γ α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace γ] [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β]
    (ω : Measure Ω) (ρ : Measure γ) (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : Ω ≃ᵐ ((γ × α) × β))
    (he : MeasurePreserving e ω ((ρ.prod μ).prod ν))
    (f : Ω → ℝ)
    (hright : AEStronglyMeasurable[
      MeasurableSpace.comap (fun x : Ω => ((e x).1.1, (e x).2))
        (inferInstance : MeasurableSpace (γ × β))] f ω)
    (hfInt : Integrable f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap (fun x : Ω => (e x).1.1)
        (inferInstance : MeasurableSpace γ)]
      (ω[f | MeasurableSpace.comap (fun x : Ω => (e x).1)
        (inferInstance : MeasurableSpace (γ × α))]) ω := by
  let leftMap : Ω → γ × α := fun x => (e x).1
  let fiberMap : Ω → β := fun x => (e x).2
  let rightMap : Ω → γ × β := fun x => ((e x).1.1, (e x).2)
  let baseMap : Ω → γ := fun x => (e x).1.1

  have hleftMeas : Measurable leftMap := measurable_fst.comp e.measurable
  have hfiberMeas : Measurable fiberMap := measurable_snd.comp e.measurable

  have hrightMk :
      StronglyMeasurable[
        MeasurableSpace.comap rightMap
          (inferInstance : MeasurableSpace (γ × β))]
        (hright.mk f) := by
    simpa [rightMap] using hright.stronglyMeasurable_mk
  obtain ⟨g, hg, hfac⟩ := hrightMk.exists_eq_measurable_comp

  let F : (γ × α) × β → ℝ := fun z => g (z.1.1, z.2)
  have hF : StronglyMeasurable F := by
    exact hg.comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

  have hfMkInt : Integrable (hright.mk f) ω :=
    (integrable_congr hright.ae_eq_mk).mp hfInt

  have hsource :
      (fun x : Ω => F (leftMap x, fiberMap x)) = hright.mk f := by
    rw [hfac]
    rfl
  have hFInt :
      Integrable (fun x : Ω => F (leftMap x, fiberMap x)) ω := by
    rw [hsource]
    exact hfMkInt

  have hmapJoint :
      ω.map (fun x : Ω => (leftMap x, fiberMap x)) =
        (ρ.prod μ).prod ν := by
    simpa [leftMap, fiberMap] using he.map_eq

  have hmapLeft :
      ω.map leftMap = ρ.prod μ := by
    change ω.map (Prod.fst ∘ e) = ρ.prod μ
    rw [← Measure.map_map measurable_fst e.measurable, he.map_eq,
      Measure.map_fst_prod, measure_univ, one_smul]

  have hκ :
      ω.map (fun x : Ω => (leftMap x, fiberMap x)) =
        ω.map leftMap ⊗ₘ Kernel.const (γ × α) ν := by
    rw [hmapJoint, hmapLeft, Measure.compProd_const]

  have hk :
      condDistrib fiberMap leftMap ω =ᵐ[ω.map leftMap]
        Kernel.const (γ × α) ν := by
    exact
      condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
        (μ := ω)
        (X := leftMap)
        (Y := fiberMap)
        hleftMeas
        hfiberMeas
        hκ

  have hkLift :
      ∀ᵐ x ∂ω,
        condDistrib fiberMap leftMap ω (leftMap x) =
          Kernel.const (γ × α) ν (leftMap x) :=
    (hleftMeas.quasiMeasurePreserving ω).ae hk

  have hcondF :
      ω[
        (fun x : Ω => F (leftMap x, fiberMap x)) |
        MeasurableSpace.comap leftMap
          (inferInstance : MeasurableSpace (γ × α))] =ᵐ[ω]
        fun x => ∫ b, F (leftMap x, b) ∂ν := by
    have hcond :=
      condExp_prod_ae_eq_integral_condDistrib
        (μ := ω)
        (X := leftMap)
        (Y := fiberMap)
        hleftMeas
        hfiberMeas.aemeasurable
        hF
        hFInt
    refine hcond.trans ?_
    filter_upwards [hkLift] with x hx
    rw [hx]
    rfl

  let k : γ → ℝ := fun c => ∫ b, g (c, b) ∂ν
  have hkMeas : StronglyMeasurable k := by
    simpa [k, Function.uncurry] using hg.integral_prod_right'

  have hcondMk :
      ω[
        (hright.mk f) |
        MeasurableSpace.comap leftMap
          (inferInstance : MeasurableSpace (γ × α))] =ᵐ[ω]
        fun x => k (baseMap x) := by
    rw [← hsource]
    simpa [F, k, leftMap, baseMap] using hcondF

  have hcond :
      ω[
        f |
        MeasurableSpace.comap leftMap
          (inferInstance : MeasurableSpace (γ × α))] =ᵐ[ω]
        fun x => k (baseMap x) :=
    (condExp_congr_ae hright.ae_eq_mk).trans hcondMk

  have hbase :
      AEStronglyMeasurable[
        MeasurableSpace.comap baseMap
          (inferInstance : MeasurableSpace γ)]
        (fun x => k (baseMap x)) ω :=
    (hkMeas.comp_measurable
      (measurable_iff_comap_le.mpr le_rfl)).aestronglyMeasurable

  simpa [leftMap, baseMap] using hbase.congr hcond.symm

/-- The common/left-only output of the three-way reindexing generates exactly
the original left-retained coordinate sigma-algebra. -/
theorem pairHaarPiThreeWay_left_comap_eq_restriction
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q] :
    MeasurableSpace.comap
        (fun x : ι → K =>
          (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1)
        (inferInstance : MeasurableSpace
          ((PairHaarPiCommonIndex p q → K) ×
            (PairHaarPiLeftOnlyIndex p q → K))) =
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) p)
        (inferInstance : MeasurableSpace ({i : ι // p i} → K)) := by
  apply le_antisymm
  · apply measurable_iff_comap_le.mp
    let encode :
        ({i : ι // p i} → K) →
          ((PairHaarPiCommonIndex p q → K) ×
            (PairHaarPiLeftOnlyIndex p q → K)) :=
      fun y =>
        ((fun i => y ⟨i.1, i.2.1⟩),
          (fun i => y ⟨i.1.1, i.2⟩))
    have hencode : Measurable encode := by
      apply Measurable.prodMk
      · rw [measurable_pi_iff]
        intro i
        exact measurable_pi_apply (⟨i.1, i.2.1⟩ : {j : ι // p j})
      · rw [measurable_pi_iff]
        intro i
        exact measurable_pi_apply (⟨i.1.1, i.2⟩ : {j : ι // p j})
    have hEq :
        (fun x : ι → K =>
          (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1) =
        encode ∘ pairHaarPiRestriction (K := K) p := by
      funext x
      apply Prod.ext
      · funext i
        simp [encode, pairHaarPiThreeWayMeasurableEquiv, pairHaarPiRestriction,
          MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc]
      · funext i
        simp [encode, pairHaarPiThreeWayMeasurableEquiv, pairHaarPiRestriction,
          MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc]
    rw [hEq]
    exact hencode.comp (measurable_iff_comap_le.mpr le_rfl)
  · apply measurable_iff_comap_le.mp
    have hEq :
        pairHaarPiRestriction (K := K) p =
          pairHaarPiLeftDecoder (K := K) p q ∘
            (fun x : ι → K =>
              (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1) := by
      funext x
      exact (pairHaarPiLeftDecoder_threeWay (K := K) p q x).symm
    rw [hEq]
    exact
      (measurable_pairHaarPiLeftDecoder (K := K) p q).comp
        (measurable_iff_comap_le.mpr le_rfl)

/-- The original right-retained restriction sigma-algebra is contained in the
common/right-side sigma-algebra of the three-way reindexing. -/
theorem pairHaarPiRestriction_right_comap_le_threeWay_right
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q] :
    MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) q)
        (inferInstance : MeasurableSpace ({i : ι // q i} → K)) ≤
      MeasurableSpace.comap
        (fun x : ι → K =>
          ((pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1.1,
            (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).2))
        (inferInstance : MeasurableSpace
          ((PairHaarPiCommonIndex p q → K) ×
            (PairHaarPiRightOnlyIndex p q → K))) := by
  apply measurable_iff_comap_le.mp
  have hEq :
      pairHaarPiRestriction (K := K) q =
        pairHaarPiRightDecoder (K := K) p q ∘
          (fun x : ι → K =>
            ((pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1.1,
              (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).2)) := by
    funext x
    exact (pairHaarPiRightDecoder_threeWay (K := K) p q x).symm
  rw [hEq]
  exact
    (measurable_pairHaarPiRightDecoder (K := K) p q).comp
      (measurable_iff_comap_le.mpr le_rfl)

/-- The common block is measurable with respect to the original right-retained
restriction. -/
theorem pairHaarPiThreeWay_base_comap_le_restriction_right
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q] :
    MeasurableSpace.comap
        (fun x : ι → K =>
          (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1.1)
        (inferInstance : MeasurableSpace (PairHaarPiCommonIndex p q → K)) ≤
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) q)
        (inferInstance : MeasurableSpace ({i : ι // q i} → K)) := by
  apply measurable_iff_comap_le.mp
  let restrictCommon :
      ({i : ι // q i} → K) → (PairHaarPiCommonIndex p q → K) :=
    fun y i => y ⟨i.1, i.2.2⟩
  have hrestrictCommon : Measurable restrictCommon := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (⟨i.1, i.2.2⟩ : {j : ι // q j})
  have hEq :
      (fun x : ι → K =>
        (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1.1) =
        restrictCommon ∘ pairHaarPiRestriction (K := K) q := by
    rw [pairHaarPiThreeWay_base_eq_restriction (K := K) p q]
    funext x i
    rfl
  rw [hEq]
  exact hrestrictCommon.comp (measurable_iff_comap_le.mpr le_rfl)

/-- On finite independent product coordinates, conditional expectation onto
the p-retained coordinates preserves q-retained measurability. -/
theorem pairHaarPi_condExp_restriction_aestronglyMeasurable_right
    {ι K : Type*}
    [Fintype ι]
    [MeasurableSpace K]
    [StandardBorelSpace K]
    [Nonempty K]
    (η : Measure K)
    [IsProbabilityMeasure η]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q]
    (f : (ι → K) → ℝ)
    (hq : AEStronglyMeasurable[
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) q)
        (inferInstance : MeasurableSpace ({i : ι // q i} → K))]
      f (Measure.pi (fun _ : ι => η)))
    (hfInt : Integrable f (Measure.pi (fun _ : ι => η))) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) q)
        (inferInstance : MeasurableSpace ({i : ι // q i} → K))]
      ((Measure.pi (fun _ : ι => η))[
        f |
        MeasurableSpace.comap
          (pairHaarPiRestriction (K := K) p)
          (inferInstance : MeasurableSpace ({i : ι // p i} → K))])
      (Measure.pi (fun _ : ι => η)) := by
  let e := pairHaarPiThreeWayMeasurableEquiv (K := K) p q
  let ρ := Measure.pi (fun _ : PairHaarPiCommonIndex p q => η)
  let μ := Measure.pi (fun _ : PairHaarPiLeftOnlyIndex p q => η)
  let ν := Measure.pi (fun _ : PairHaarPiRightOnlyIndex p q => η)

  have he :
      MeasurePreserving e
        (Measure.pi (fun _ : ι => η))
        ((ρ.prod μ).prod ν) := by
    simpa [e, ρ, μ, ν] using
      pairHaarPiThreeWayMeasurableEquiv_measurePreserving η p q

  have hqRight :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (fun x : ι → K => ((e x).1.1, (e x).2))
          (inferInstance : MeasurableSpace
            ((PairHaarPiCommonIndex p q → K) ×
              (PairHaarPiRightOnlyIndex p q → K)))]
        f (Measure.pi (fun _ : ι => η)) := by
    exact hq.mono (by
      simpa [e] using
        pairHaarPiRestriction_right_comap_le_threeWay_right
          (K := K) p q)

  have hcollapse :=
    condExp_sharedBase_aestronglyMeasurable_of_measurePreserving_equiv
      (Measure.pi (fun _ : ι => η)) ρ μ ν e he f hqRight hfInt

  have hleft :=
    pairHaarPiThreeWay_left_comap_eq_restriction (K := K) p q
  have hbaseLe :=
    pairHaarPiThreeWay_base_comap_le_restriction_right (K := K) p q
  rw [hleft] at hcollapse
  exact hcollapse.mono (by simpa [e] using hbaseLe)

/-- Wilson-specific beta-zero conditional-expectation invariance:
conditioning on one actual right-boundary color-retained sigma-algebra
preserves measurability with respect to every other right-boundary color. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStatePairHaar_condExp_color_preserves_color
    (H N : ℕ)
    (c d : Fin 6)
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hd : AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d)]
      f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))
    (hfInt :
      Integrable f
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d)]
      ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)[
        f |
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)])
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  classical
  let I := PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let η : Measure G := normalizedCompactHaar G
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N
  let p : I → Prop :=
    fun i => i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c
  let q : I → Prop :=
    fun i => i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H d
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
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) =
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) p) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // p i} → G)) := by
    rw [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedCoordinateRestriction,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_piRestriction_comp]

  have hqSpace :
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d) =
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) q) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // q i} → G)) := by
    rw [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedCoordinateRestriction,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_piRestriction_comp]

  have hd' :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) q) ∘ E)
          (inferInstance : MeasurableSpace ({i : I // q i} → G))]
        f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    rw [← hqSpace]
    exact hd

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
    hd'.mono hrightLe

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
              (inferInstance : MeasurableSpace (PairHaarPiCommonIndex p q → G))) ≤
          MeasurableSpace.comap E
            (MeasurableSpace.comap
              (pairHaarPiRestriction (K := G) q)
              (inferInstance : MeasurableSpace ({i : I // q i} → G))) from h)

  rw [hleft] at hcollapse
  have htarget := hcollapse.mono hbaseLe
  rw [← hpSpace, ← hqSpace] at htarget
  exact htarget

/-- The actual beta-zero six-spatial pair-Haar color family is pairwise
range-invariant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_range_invariant
    (H N : ℕ)
    (c d : Fin 6)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N)
    (hx : x ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N d).toLinearMap.range) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N c x ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N d).toLinearMap.range := by
  rcases hx with ⟨y, rfl⟩

  have hzMeas :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d)]
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N d y :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    change
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d)]
        ((condExpL2 ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
            H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d))
          y :
            lpMeas ℝ ℝ
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
                H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d))
              2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
    exact lpMeas.aestronglyMeasurable _

  have hzInt :
      Integrable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N d y :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    rw [← memLp_one_iff_integrable]
    exact
      (Lp.memLp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N d y)).mono_exponent (by norm_num)

  have hcondMeas :=
    periodicHypercubicEvenSpecialUnitaryGroundStatePairHaar_condExp_color_preserves_color
      H N c d
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N d y :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      hzMeas hzInt

  let hcLe :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
      H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

  have hL2Cond :
      (condExpL2 ℝ ℝ hcLe
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N d y) :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)[
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N d y :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) |
          periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)] := by
    simpa [hcLe] using
      (Lp.memLp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N d y)).condExpL2_ae_eq_condExp
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))

  have hcMeas :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d)]
        ((condExpL2 ℝ ℝ hcLe
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N d y) :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    exact hcondMeas.congr hL2Cond.symm

  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d) ≤
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
    ⟨periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
      H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d)⟩

  let q :
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
    ⟨
      (condExpL2 ℝ ℝ hcLe
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N d y) :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N),
      mem_lpMeas_iff_aestronglyMeasurable.mpr hcMeas
    ⟩

  refine ⟨
    (condExpL2 ℝ ℝ hcLe
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N d y) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N), ?_⟩

  have hq :
      (condExpL2 ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d))
        (q :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
        lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d))
          2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q

  have hCoe := congrArg
    (fun u : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm d))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =>
      (u :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N))
    hq

  simpa [q, hcLe,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection]
    using hCoe
end

end MathlibAnalytic
end MGAP4D
