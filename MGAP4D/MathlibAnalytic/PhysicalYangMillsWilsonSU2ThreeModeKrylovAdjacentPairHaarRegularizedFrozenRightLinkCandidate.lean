import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaVacuumFiberEnergy
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumWilsonDensityHaarWitness
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-!
# P4-Q1: explicit regularized frozen-right-link Wilson vacuum witnesses

The genuine positive-beta posterior vacuum is the original
U_beta(1) = 1 / sqrt(W_beta) under the original ground-state JOINT law.
The original retained sigma-algebra keeps ALL left links and ALL
right links except the selected link e.

For every finite H, nonnegative beta, positive regulator delta and
right link e, construct the explicit physical-density candidate

  g_(e,delta)(A,B)
    = 1 / sqrt(delta + |W_(beta,c)(A, update B e 1)|).

This uses the SAME canonical continuous representative of the original
physical joint density as PRs #5296--#5302 and the literal update of
ONE RIGHT spatial SU(2) link. It is not an alternative physical law.

We prove pointwise uniform-in-configuration boundedness at any fixed
delta>0, measurability under the ACTUAL retained sigma-algebra,
membership in the ACTUAL ground-state joint L², and the ORIGINAL sharp
conditional-expectation best-approximation bound. The exact same
explicit witness controls the original frozen-beta-zero receiver drift.

The RHS errors are genuine original-joint L² norms. Their sum is
NOT claimed to be independent of volume or regulator; positivity of
the vacuum loss from #5302 does not imply an upper bound.
No Dobrushin or continuum mass-gap assertion is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4Q1TopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q1CompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q1SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q1MeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q1BorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q1SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Regularized inverse-square-root of the actual continuous Wilson
joint density after replacing only the selected RIGHT link by the
SU(2) identity. Absolute value is a pointwise stability convention;
the original continuous Wilson density is strictly positive. -/
noncomputable def originalWilsonRegularizedFrozenRightLinkVacuumFunction
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (delta : ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  (1 : ℝ) / Real.sqrt
    (delta + |originalWilsonContinuousPhysicalJointWeight H beta hbeta
      (z.1, Function.update z.2 e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))|)

/-- Literal one-link freezing makes the explicit regularized physical
vacuum candidate measurable in the EXISTING sigma-algebra retaining
every left and every non-target right coordinate. -/
theorem originalWilsonRegularizedFrozenRightLinkVacuumFunction_measurable_retained
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (delta : ℝ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H 2 e]
      (originalWilsonRegularizedFrozenRightLinkVacuumFunction H beta hbeta delta e) := by
  classical
  let G := Matrix.specialUnitaryGroup (Fin 2) ℂ
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let m := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H 2 e
  have hleft : Measurable[m] (Prod.fst : X × X → X) := by
    exact measurable_iff_comap_le.mpr le_sup_left
  have hoff : Measurable[m]
      (fun z : X × X =>
        periodicHypercubicEvenSpatialSliceOffTargetRestriction e z.2) := by
    exact measurable_iff_comap_le.mpr le_sup_right
  have hright : Measurable[m]
      (fun z : X × X => Function.update z.2 e (1 : G)) := by
    refine measurable_pi_lambda _ ?_
    intro k
    by_cases hk : k = e
    · have hfreeze :
          (fun z : X × X => (Function.update z.2 e (1 : G)) k) =
            (fun _ : X × X => (1 : G)) := by
        funext z
        subst k
        simp
      rw [hfreeze]
      exact measurable_const
    · let i : PeriodicHypercubicEvenSpatialSliceOffTargetLink H e := ⟨k, hk⟩
      have hkmeas : Measurable[m] (fun z : X × X => z.2 k) := by
        simpa [i, periodicHypercubicEvenSpatialSliceOffTargetRestriction] using
          (measurable_pi_apply i).comp hoff
      have hfreeze :
          (fun z : X × X => (Function.update z.2 e (1 : G)) k) =
            (fun z : X × X => z.2 k) := by
        funext z
        simp [hk]
      rw [hfreeze]
      exact hkmeas
  haveI hXSecondCountable : SecondCountableTopology X := by
    dsimp [X]
    infer_instance
  haveI hXBorel : BorelSpace X := by
    dsimp [X]
    infer_instance
  haveI hXXBorel : BorelSpace (X × X) := inferInstance
  have hWambient : @Measurable (X × X) ℝ
      (Prod.instMeasurableSpace) inferInstance
      (originalWilsonContinuousPhysicalJointWeight H beta hbeta) :=
    (originalWilsonContinuousPhysicalJointWeight_continuous
      H beta hbeta).measurable
  have hW : Measurable[m]
      (fun z : X × X =>
        originalWilsonContinuousPhysicalJointWeight H beta hbeta
          (z.1, Function.update z.2 e (1 : G))) := by
    exact hWambient.comp (hleft.prodMk hright)
  have hsqrt : Measurable[m]
      (fun z : X × X =>
        Real.sqrt (delta +
          |originalWilsonContinuousPhysicalJointWeight H beta hbeta
            (z.1, Function.update z.2 e (1 : G))|)) := by
    exact Real.continuous_sqrt.measurable.comp (measurable_const.add hW.abs)
  change Measurable[m]
    (fun z : X × X =>
      (1 : ℝ) / Real.sqrt (delta +
        |originalWilsonContinuousPhysicalJointWeight H beta hbeta
          (z.1, Function.update z.2 e (1 : G))|))
  exact measurable_const.div hsqrt

/-- The regulator gives a genuine pointwise L²-majorant with no
assumption about a volume-uniform lower bound for the Wilson vacuum. -/
theorem originalWilsonRegularizedFrozenRightLinkVacuumFunction_norm_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (delta : ℝ) (hdelta : 0 < delta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ‖originalWilsonRegularizedFrozenRightLinkVacuumFunction
        H beta hbeta delta e z‖ ≤ 1 / Real.sqrt delta := by
  classical
  let W : ℝ :=
    originalWilsonContinuousPhysicalJointWeight H beta hbeta
      (z.1, Function.update z.2 e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  have hroot : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hrad : delta ≤ delta + |W| := by
    have := abs_nonneg W
    linarith
  have hrootle : Real.sqrt delta ≤ Real.sqrt (delta + |W|) :=
    Real.sqrt_le_sqrt hrad
  have hden : 0 < Real.sqrt (delta + |W|) :=
    lt_of_lt_of_le hroot hrootle
  have hbound : (1 : ℝ) / Real.sqrt (delta + |W|) ≤ 1 / Real.sqrt delta :=
    one_div_le_one_div_of_le hroot hrootle
  calc
    ‖originalWilsonRegularizedFrozenRightLinkVacuumFunction
        H beta hbeta delta e z‖ =
        (1 : ℝ) / Real.sqrt (delta + |W|) := by
      change ‖(1 : ℝ) / Real.sqrt (delta + |W|)‖ =
        (1 : ℝ) / Real.sqrt (delta + |W|)
      simp only [Real.norm_eq_abs, abs_div, abs_one, abs_of_pos hden]
    _ ≤ 1 / Real.sqrt delta := hbound

/-- An ACTUAL original-joint L² vector made from a bounded, retained-
measurable physical Wilson density. No conditional-expectation output
is used in its construction. -/
noncomputable def originalWilsonRegularizedFrozenRightLinkVacuumL2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (delta : ℝ) (hdelta : 0 < delta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H 2 (Nat.zero_lt_succ 1) beta hbeta := by
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H 2 (Nat.zero_lt_succ 1) beta hbeta
  let f := originalWilsonRegularizedFrozenRightLinkVacuumFunction H beta hbeta delta e
  letI : IsProbabilityMeasure ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H 2 (Nat.zero_lt_succ 1) beta hbeta
  have hret :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H 2 e]
        f ν :=
    (originalWilsonRegularizedFrozenRightLinkVacuumFunction_measurable_retained
      H beta hbeta delta e).aestronglyMeasurable
  have hfull : AEStronglyMeasurable f ν :=
    hret.mono
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
        H 2 e)
  have hbound : ∀ᵐ z ∂ν, ‖f z‖ ≤ 1 / Real.sqrt delta :=
    Filter.Eventually.of_forall fun z =>
      originalWilsonRegularizedFrozenRightLinkVacuumFunction_norm_le
        H beta hbeta delta hdelta e z
  exact (MemLp.of_bound hfull (1 / Real.sqrt delta) hbound).toLp f

/-- The constructed genuine joint L² candidate actually retains
the original one-right-link sigma algebra. -/
theorem originalWilsonRegularizedFrozenRightLinkVacuumL2_retained
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (delta : ℝ) (hdelta : 0 < delta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H 2 e]
      (fun z => originalWilsonRegularizedFrozenRightLinkVacuumL2
        H beta hbeta delta hdelta e z)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H 2 (Nat.zero_lt_succ 1) beta hbeta) := by
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H 2 (Nat.zero_lt_succ 1) beta hbeta
  let f := originalWilsonRegularizedFrozenRightLinkVacuumFunction H beta hbeta delta e
  letI : IsProbabilityMeasure ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H 2 (Nat.zero_lt_succ 1) beta hbeta
  have hret :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H 2 e]
        f ν :=
    (originalWilsonRegularizedFrozenRightLinkVacuumFunction_measurable_retained
      H beta hbeta delta e).aestronglyMeasurable
  have hfull : AEStronglyMeasurable f ν :=
    hret.mono
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
        H 2 e)
  have hbound : ∀ᵐ z ∂ν, ‖f z‖ ≤ 1 / Real.sqrt delta :=
    Filter.Eventually.of_forall fun z =>
      originalWilsonRegularizedFrozenRightLinkVacuumFunction_norm_le
        H beta hbeta delta hdelta e z
  have hmem : MemLp f 2 ν := MemLp.of_bound hfull (1 / Real.sqrt delta) hbound
  have hrep : (fun z => (hmem.toLp f) z) =ᵐ[ν] f :=
    MemLp.coeFn_toLp hmem
  change AEStronglyMeasurable[
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H 2 e]
    (fun z => (hmem.toLp f) z) ν
  exact hret.congr hrep.symm

/-- Explicit right-link-local ORIGINAL Wilson candidate bound.
There is no spatial-link-cardinality multiplier outside the actual
sum of candidate errors. Controlling that sum uniformly in H
remains an independent quantitative task. -/
theorem originalGroundStateJointVacuumResidual_le_regularizedFrozenCandidates
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (delta : ℝ) (hdelta : 0 < delta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H 2
            (Nat.zero_lt_succ 1) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H 2 (Nat.zero_lt_succ 1) beta hbeta e
          (originalGroundStateJointTransportedPairHaarOne H 2
            (Nat.zero_lt_succ 1) beta hbeta)‖ ^ 2) ≤
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H 2
            (Nat.zero_lt_succ 1) beta hbeta -
        originalWilsonRegularizedFrozenRightLinkVacuumL2
          H beta hbeta delta hdelta e‖ ^ 2 := by
  exact originalGroundStateJointTransportedPairHaarOne_fullResidual_le_candidates
    H 2 (Nat.zero_lt_succ 1) beta hbeta
    (fun e => originalWilsonRegularizedFrozenRightLinkVacuumL2
      H beta hbeta delta hdelta e)
    (originalWilsonRegularizedFrozenRightLinkVacuumL2_retained
      H beta hbeta delta hdelta)

/-- The pre-existing FROZEN-beta-zero physical receiver projection
drift can be controlled by the same concrete retained physical
Wilson candidates. This does not bound the independent genuine
positive-beta orthogonal receiver term (P4-Q2). -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_frozenDrift_le_regularizedFrozenCandidates
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (delta : ℝ) (hdelta : 0 < delta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H 2
          (Nat.zero_lt_succ 1) 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H 2
            (Nat.zero_lt_succ 1) 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H 2
          (Nat.zero_lt_succ 1) beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H 2
            (Nat.zero_lt_succ 1) 0 (by norm_num) f)‖ ^ 2) ≤
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) f) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖originalGroundStateJointTransportedPairHaarOne H 2
            (Nat.zero_lt_succ 1) beta hbeta -
          originalWilsonRegularizedFrozenRightLinkVacuumL2
            H beta hbeta delta hdelta e‖ ^ 2) := by
  exact normalizedPhysicalOneSlabPairHaarReceiver_beta_fullProjectionDrift_le_jointCandidates
    H 2 (Nat.zero_lt_succ 1) beta hbeta f
    (fun e => originalWilsonRegularizedFrozenRightLinkVacuumL2
      H beta hbeta delta hdelta e)
    (originalWilsonRegularizedFrozenRightLinkVacuumL2_retained
      H beta hbeta delta hdelta)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
