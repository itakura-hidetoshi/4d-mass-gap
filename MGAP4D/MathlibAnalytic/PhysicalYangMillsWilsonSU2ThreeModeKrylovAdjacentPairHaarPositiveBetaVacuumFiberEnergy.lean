import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarRightLinkRetainedAEDescent
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumZeroIffRetainedWilson
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Tactic

/-!
# P4-F3: genuine positive-beta posterior vacuum-fiber energy is strictly positive

The latest PR #5301 proves that the CANONICAL CONTINUOUS representative
of the ORIGINAL positive-beta SU(2) Wilson joint normalized weight is
not measurable under the sigma algebra retaining the entire left
boundary and every right-boundary link except the explicit target.

The original joint probability law and original pair-Haar law are
mutually absolutely continuous; the original Wilson density is
strictly positive Haar-almost everywhere. Therefore a retained
measurable representative of the ORIGINAL inverse-square-root
Wilson density under the ORIGINAL joint law would make the original
Wilson density retained measurable under pair Haar, and also its
canonical continuous representative via the proved pair-Haar a.e.
equality. This contradicts #5301.

We then apply the ORIGINAL CondExpL2 residual positivity criterion
from #5286. No new posterior, replacement law, independence
assumption, Dobrushin coefficient, or unproved uniform bound is used.
This is strictly positive at each FIXED finite H and beta>0. It is
not a beta/volume-uniform quantitative bound and not a continuum
Yang--Mills mass-gap proof.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Pure mathlib measurability descent: an a.e. positive real
density is measurable whenever its reciprocal square-root is.
No uniform positive lower bound is required. -/
theorem real_aestronglyMeasurable_of_inv_sqrt_retained
    {α : Type*} {m : MeasurableSpace α} [m₀ : MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 < w x)
    (hinv : AEStronglyMeasurable[m]
      (fun x => (1 : ℝ) / Real.sqrt (w x)) μ) :
    AEStronglyMeasurable[m] w μ := by
  have hinvInv : AEStronglyMeasurable[m]
      (fun x : α => (1 : ℝ) / ((1 : ℝ) / Real.sqrt (w x))) μ :=
    (aestronglyMeasurable_const :
      AEStronglyMeasurable[m] (fun _ : α => (1 : ℝ)) μ).div₀ hinv
  have hsquare : AEStronglyMeasurable[m]
      (fun x : α => ((1 : ℝ) / ((1 : ℝ) / Real.sqrt (w x))) ^ 2) μ :=
    hinvInv.pow 2
  have hsame :
      (fun x : α => ((1 : ℝ) / ((1 : ℝ) / Real.sqrt (w x))) ^ 2) =ᵐ[μ]
        w := by
    filter_upwards [hpos] with x hx
    simpa only [one_div, inv_inv] using (Real.sq_sqrt hx.le)
  exact hsquare.congr hsame

local instance p4F3TopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4F3CompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4F3SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4F3MeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4F3BorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4F3SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Under the ORIGINAL positive-beta Wilson ground-state JOINT law,
the ORIGINAL inverse-square-root density is not retained-measurable
at the one concrete right link used in the strict SU(2) crossing.
This transports an a.e. statement; it does not pretend that arbitrary
representatives of the L² vacuum agree pointwise. -/
theorem originalWilsonInverseSqrt_not_retained_originalJoint_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ¬ AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H 2 (originalWilsonExplicitSpatialTargetLink H)]
        (fun z => (1 : ℝ) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H 2 (by norm_num) beta (le_of_lt hbeta) z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H 2 (by norm_num) beta (le_of_lt hbeta)) := by
  classical
  let μ := (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H 2 (by norm_num) beta (le_of_lt hbeta)
  let w := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    H 2 (by norm_num) beta (le_of_lt hbeta)
  let m := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
    H 2 (originalWilsonExplicitSpatialTargetLink H)
  intro hinvJoint
  have hHaarAC : μ ≪ ν := by
    simpa [μ, ν, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
        H 2 (by norm_num) beta (le_of_lt hbeta))
  have hinvHaar : AEStronglyMeasurable[m]
      (fun z => (1 : ℝ) / Real.sqrt (w z)) μ := by
    change AEStronglyMeasurable[m]
      (fun z => (1 : ℝ) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
          H 2 (by norm_num) beta (le_of_lt hbeta) z) μ
    exact hinvJoint.mono_ac hHaarAC
  have hwPos : ∀ᵐ z ∂μ, 0 < w z := by
    simpa [μ, w, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
        H 2 (by norm_num) beta (le_of_lt hbeta))
  have hwRet : AEStronglyMeasurable[m] w μ :=
    real_aestronglyMeasurable_of_inv_sqrt_retained (m := m) hwPos hinvHaar
  have hContinuousAE :
      originalWilsonContinuousPhysicalJointWeight H beta (le_of_lt hbeta) =ᵐ[μ]
        w := by
    simpa [μ, w, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (originalWilsonContinuousPhysicalJointWeight_ae_eq_original
        H beta (le_of_lt hbeta))
  have hContRet : AEStronglyMeasurable[m]
      (originalWilsonContinuousPhysicalJointWeight H beta (le_of_lt hbeta)) μ :=
    hwRet.congr hContinuousAE.symm
  exact
    (originalWilsonContinuousPhysicalJoint_not_retained_pairHaar H beta hbeta)
      hContRet

/-- The ORIGINAL true positive-beta posterior vacuum-fiber loss is
STRICTLY POSITIVE, for every fixed finite even-periodic spatial
extent H and every beta>0.  It is the original actual CondExpL2
projection on all left and all off-target right links, summed over
the full set of physical spatial links. -/
theorem originalGroundStateJointTransportedPairHaarOne_fullResidual_pos_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 <
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖originalGroundStateJointTransportedPairHaarOne H 2
            (by decide) beta (le_of_lt hbeta) -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H 2 (by decide) beta (le_of_lt hbeta) e
            (originalGroundStateJointTransportedPairHaarOne H 2
              (by decide) beta (le_of_lt hbeta))‖ ^ 2) := by
  exact
    originalGroundStateJointTransportedPairHaarOne_fullResidual_pos_of_WilsonNotRetained
      H 2 (by decide) beta (le_of_lt hbeta)
      (originalWilsonExplicitSpatialTargetLink H)
      (originalWilsonInverseSqrt_not_retained_originalJoint_SU2 H beta hbeta)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
