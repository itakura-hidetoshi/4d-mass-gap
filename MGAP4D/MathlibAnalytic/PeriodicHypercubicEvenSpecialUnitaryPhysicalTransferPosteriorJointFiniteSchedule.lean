import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointCondExpIdentification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasureEquivalence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorHeatBathProjectionSweepL2
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# Literal posterior finite schedules on the genuine joint L2 carrier

The one-step identity from PR #5210 does not by itself justify substituting
an a.e.-equal intermediate observable into another fiber integral. We prove
that missing congruence using the existing mutual absolute continuity with
pair Haar, the measure-preserving context/target split, and Fubini for null
sets. The canonical target kernel is absolutely continuous with target Haar
for almost every retained context.

Consequently the literal posterior integrals preserve joint a.e. equality.
Their chronological finite iteration agrees a.e. with the iteration of the
canonical means. For bounded strongly measurable initial observables, the
canonical intermediates stay in that same bounded core. Their L2 classes
are therefore exactly the EXISTING ordered CondExpL2 projection sweep.

The final L2 vector is constructed from the literal posterior schedule, not
chosen as a representative of the projection product. Empty schedules,
repeated links, and arbitrary update order are included. No commutation
between distinct projections, new law, new Hilbert carrier, cutoff, or
comparison constant is assumed. General a.e. statements use totalized
Bochner integrals; only bounded-core statements assert L2 membership.

This is finite-schedule identification, not a quantitative oscillation tail,
physical-transfer/reconstruction commutation, or an identification of the
posterior sweep with Euclidean time. The strict-interval no-go is unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStatePosteriorJoint

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Joint" => Cfg × Cfg
local notation "μH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta

/-- Joint a.e. equality descends to canonical fiber integrals. No integrability
or measurability premise on the two real functions is needed. -/
theorem canonicalMean_congr_ae (target : Link)
    {F G : Joint → ℝ} (hFG : F =ᵐ[μJ] G) :
    GroundStateCanonicalMean.canonicalMean H N hN beta hbeta target F =ᵐ[μJ]
      GroundStateCanonicalMean.canonicalMean H N hN beta hbeta target G := by
  classical
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar GaugeT)
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar GaugeT)
  let μCtx := Measure.prod μH μOff
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  let outer :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N target
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target
  have hcoord : MeasurePreserving coord (μCtx.prod μTarget) (Measure.prod μH μH) := by
    simpa [coord, μCtx, μOff, μTarget] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetHaar_measurePreserving
        H N target)
  have hReverse : Measure.prod μH μH ≪ μJ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
      H N hN beta hbeta
  have hHaar : F =ᵐ[Measure.prod μH μH] G := hFG.filter_mono hReverse.ae_le
  have hSplit := hcoord.quasiMeasurePreserving.ae hHaar
  have hFibers := Measure.ae_ae_of_ae_prod hSplit
  have hKernel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_ae_eq_normalizedFiber
      H N hN beta hbeta target
  have hMeans : ∀ᵐ ctx ∂μCtx,
      (∫ tc, F (coord (ctx, tc)) ∂κ ctx) =
        ∫ tc, G (coord (ctx, tc)) ∂κ ctx := by
    filter_upwards [hFibers, hKernel] with ctx hfg hk
    have hκac : κ ctx ≪ μTarget := by
      rw [hk]
      exact withDensity_absolutelyContinuous _ _
    exact integral_congr_ae (hfg.filter_mono hκac.ae_le)
  have hOuter : Measure.QuasiMeasurePreserving outer (Measure.prod μH μH) μCtx := by
    change Measure.QuasiMeasurePreserving (Prod.fst ∘ coord.symm)
      (Measure.prod μH μH) μCtx
    exact (Measure.quasiMeasurePreserving_fst (μ := μCtx) (ν := μTarget)).comp
      hcoord.symm.quasiMeasurePreserving
  have hForward : μJ ≪ Measure.prod μH μH := withDensity_absolutelyContinuous _ _
  exact (hOuter.ae hMeans).filter_mono hForward.ae_le

/-- The literal posterior formula is independent, joint-almost everywhere,
of changes of the observable on a joint null set. -/
theorem posteriorMean_congr_ae (target : Link)
    {F G : Joint → ℝ} (hFG : F =ᵐ[μJ] G) :
    posteriorMean H N hN beta hbeta target F =ᵐ[μJ]
      posteriorMean H N hN beta hbeta target G := by
  filter_upwards [canonicalMean_joint_ae_eq_posteriorMean H N hN beta hbeta target,
    canonicalMean_congr_ae H N hN beta hbeta target hFG] with z hz hc
  exact (hz F).symm.trans (hc.trans (hz G))

/-- Chronological finite iteration of literal posterior integrals. The head
link acts first, with no restriction on repetitions or update order. -/
def posteriorSchedule (order : List Link) (F : Joint → ℝ) : Joint → ℝ :=
  order.foldl (fun G target => posteriorMean H N hN beta hbeta target G) F

/-- Bounded measurable intermediates for the same chronological schedule. -/
def canonicalSchedule (order : List Link) (F : Joint → ℝ) : Joint → ℝ :=
  order.foldl
    (fun G target => GroundStateCanonicalMean.canonicalMean H N hN beta hbeta target G) F

/-- A finite literal posterior schedule respects joint a.e. equality. -/
theorem posteriorSchedule_congr_ae (order : List Link)
    {F G : Joint → ℝ} (hFG : F =ᵐ[μJ] G) :
    posteriorSchedule H N hN beta hbeta order F =ᵐ[μJ]
      posteriorSchedule H N hN beta hbeta order G := by
  induction order generalizing F G with
  | nil => exact hFG
  | cons target order ih =>
      exact ih (posteriorMean_congr_ae H N hN beta hbeta target hFG)

/-- Canonical representatives can be substituted at every intermediate step,
not just at the initial observable. This statement applies to all real F. -/
theorem posteriorSchedule_ae_eq_canonicalSchedule (order : List Link) (F : Joint → ℝ) :
    posteriorSchedule H N hN beta hbeta order F =ᵐ[μJ]
      canonicalSchedule H N hN beta hbeta order F := by
  induction order generalizing F with
  | nil => exact Filter.EventuallyEq.rfl
  | cons target order ih =>
      have hStep : posteriorMean H N hN beta hbeta target F =ᵐ[μJ]
          GroundStateCanonicalMean.canonicalMean H N hN beta hbeta target F :=
        (canonicalMean_joint_ae_eq_posteriorMean H N hN beta hbeta target).mono
          fun z hz => (hz F).symm
      exact (posteriorSchedule_congr_ae H N hN beta hbeta order hStep).trans (ih _)

/-- The canonical schedule preserves strong measurability. -/
theorem canonicalSchedule_stronglyMeasurable (order : List Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable (canonicalSchedule H N hN beta hbeta order F) := by
  induction order generalizing F with
  | nil => exact hF
  | cons target order ih =>
      exact ih _ (GroundStateCanonicalMean.canonicalMean_stronglyMeasurable
        H N hN beta hbeta target F hF)

/-- The same pointwise bound holds at every canonical intermediate step. -/
theorem canonicalSchedule_norm_le (order : List Link)
    (F : Joint → ℝ) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (z : Joint) :
    ‖canonicalSchedule H N hN beta hbeta order F z‖ ≤ bound := by
  induction order generalizing F with
  | nil => exact hbound z
  | cons target order ih =>
      exact ih _ (GroundStateCanonicalMean.canonicalMean_norm_le
        H N hN beta hbeta target F bound hbound)

/-- The canonical bounded-core iteration is exactly the pre-existing ordered
sweep of genuine joint CondExpL2 maps. Distinct targets need not commute. -/
theorem canonicalScheduleL2_eq_projectionSchedule (order : List Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta (canonicalSchedule H N hN beta hbeta order F)
      (canonicalSchedule_stronglyMeasurable H N hN beta hbeta order F hF) bound
      (canonicalSchedule_norm_le H N hN beta hbeta order F bound hbound) =
    realHilbertProjectionSweep PJoint order
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound) := by
  induction order generalizing F with
  | nil => rfl
  | cons target order ih =>
      let G := GroundStateCanonicalMean.canonicalMean H N hN beta hbeta target F
      have hG : StronglyMeasurable G :=
        GroundStateCanonicalMean.canonicalMean_stronglyMeasurable
          H N hN beta hbeta target F hF
      have hGb : ∀ z, ‖G z‖ ≤ bound :=
        GroundStateCanonicalMean.canonicalMean_norm_le
          H N hN beta hbeta target F bound hbound
      exact (ih G hG hGb).trans
        (congrArg (fun f : JL2 => realHilbertProjectionSweep PJoint order f)
          (GroundStateCanonicalMean.canonicalMeanL2_eq_condExpL2
            H N hN beta hbeta target F hF bound hbound))

/-- The actual ordered projection sweep has the literal posterior finite
schedule as an a.e. representative on the bounded strongly measurable core. -/
theorem projectionSchedule_coeFn_eq_posteriorSchedule (order : List Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z => realHilbertProjectionSweep PJoint order
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound) z) =ᵐ[μJ]
      posteriorSchedule H N hN beta hbeta order F := by
  have hCanonical :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta (canonicalSchedule H N hN beta hbeta order F)
      (canonicalSchedule_stronglyMeasurable H N hN beta hbeta order F hF) bound
      (canonicalSchedule_norm_le H N hN beta hbeta order F bound hbound)
  rw [canonicalScheduleL2_eq_projectionSchedule H N hN beta hbeta order F hF bound hbound]
    at hCanonical
  exact hCanonical.trans
    (posteriorSchedule_ae_eq_canonicalSchedule H N hN beta hbeta order F).symm

/-- The literal finite posterior schedule belongs to the existing joint L2
space, without assuming measurable representatives for its intermediate steps. -/
theorem posteriorSchedule_memLp_two (order : List Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    MemLp (posteriorSchedule H N hN beta hbeta order F) 2 μJ := by
  exact MemLp.ae_eq
    (projectionSchedule_coeFn_eq_posteriorSchedule H N hN beta hbeta order F hF bound hbound)
    (Lp.memLp (realHilbertProjectionSweep PJoint order
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound)))

/-- The joint L2 class constructed from the literal finite posterior schedule. -/
def posteriorScheduleL2 (order : List Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) : JL2 :=
  (posteriorSchedule_memLp_two H N hN beta hbeta order F hF bound hbound).toLp
    (posteriorSchedule H N hN beta hbeta order F)

/-- Exact literal-posterior/projection-sweep identification in the original
joint Hilbert carrier, with no extra operator compatibility hypothesis. -/
theorem posteriorScheduleL2_eq_projectionSchedule (order : List Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    posteriorScheduleL2 H N hN beta hbeta order F hF bound hbound =
      realHilbertProjectionSweep PJoint order
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound) := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp
    (posteriorSchedule_memLp_two H N hN beta hbeta order F hF bound hbound)).trans
    (projectionSchedule_coeFn_eq_posteriorSchedule
      H N hN beta hbeta order F hF bound hbound).symm

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
