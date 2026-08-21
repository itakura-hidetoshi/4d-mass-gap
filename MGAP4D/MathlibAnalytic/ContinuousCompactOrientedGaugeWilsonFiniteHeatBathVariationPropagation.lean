import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredVariationFellerClosure
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathObservableAction
import Mathlib.Tactic

/-!
# Finite current heat-bath Feller and centered-variation propagation

The current one-link conditional expectation is a Feller operator on bounded
continuous observables, and the sharp one-link Dobrushin variation update is
closed again into a centered variation profile.  This file iterates that closed
step along an arbitrary finite ordered list of physical links.

The observable recursion follows the same order as the already-defined actual
finite heat-bath kernel: if `target :: targets` is the update list, the state
kernel applies `target` first, while the induced observable operator is

`P_(target :: targets) O = P_target (P_targets O)`.

We prove that the recursively closed bounded-continuous observable agrees
pointwise with the actual finite-kernel integral from the current stationarity
layer.  We then iterate the centered variation profile with the corresponding
recursive sharp updated-variation function.

This remains finite-volume heat-bath/Dobrushin algebra.  The update list is not
identified with Euclidean time.  No covariance decay, continuum clustering,
positive physical mass, OS Hamiltonian gap, or uniform continuum Dobrushin
threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Bounded-continuous observable action of a finite ordered current one-link
heat-bath update list.  The tail observable is formed first and the head
conditional expectation is applied outside it, exactly as required by kernel
composition. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.finiteSingleLinkHeatBathContinuousBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    List C.base.geometry.Edge →
      BoundedContinuousFunction C.base.Configuration ℝ →
        BoundedContinuousFunction C.base.Configuration ℝ
  | [], O => O
  | target :: targets, O =>
      C.singleLinkConditionalExpectationContinuousBCF target
        (C.finiteSingleLinkHeatBathContinuousBCF targets O)

@[simp] theorem continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_nil
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.finiteSingleLinkHeatBathContinuousBCF [] O = O := by
  rfl

@[simp] theorem continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_cons
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.finiteSingleLinkHeatBathContinuousBCF (target :: targets) O =
      C.singleLinkConditionalExpectationContinuousBCF target
        (C.finiteSingleLinkHeatBathContinuousBCF targets O) := by
  rfl

/-- The recursively closed Feller observable is pointwise exactly the existing
actual finite heat-bath-kernel observable action. -/
theorem continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_eq_expectationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.finiteSingleLinkHeatBathContinuousBCF targets O A =
      C.finiteSingleLinkHeatBathExpectationBCF targets O A := by
  induction targets generalizing A with
  | nil =>
      simp
  | cons target targets ih =>
      rw [continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_cons]
      rw [continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_apply]
      rw [← continuous_compact_oriented_integral_singleLinkHeatBathKernel_BCF
        C target A (C.finiteSingleLinkHeatBathContinuousBCF targets O)]
      rw [continuous_compact_oriented_finiteSingleLinkHeatBathExpectationBCF_cons]
      apply integral_congr_ae
      filter_upwards [] with B
      exact ih B

/-- In particular, the actual finite heat-bath-kernel observable action is
continuous in the initial physical-link configuration. -/
theorem continuous_compact_oriented_finiteSingleLinkHeatBathExpectationBCF_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous (fun A : C.base.Configuration =>
      C.finiteSingleLinkHeatBathExpectationBCF targets O A) := by
  have hEq :
      (fun A : C.base.Configuration =>
        C.finiteSingleLinkHeatBathExpectationBCF targets O A) =
      fun A : C.base.Configuration =>
        C.finiteSingleLinkHeatBathContinuousBCF targets O A := by
    funext A
    exact
      (continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_eq_expectationBCF
        C targets O A).symm
  rw [hEq]
  exact (C.finiteSingleLinkHeatBathContinuousBCF targets O).continuous

/-- Pure recursive linkwise variation function generated by the existing sharp
one-link Dobrushin update along a finite ordered target list.  As for the
observable recursion, the tail profile is propagated first and the head update
is applied outside it. -/
noncomputable def continuousCompactOrientedGaugeWilsonFiniteUpdatedVariation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ) :
    List C.base.geometry.Edge → C.base.geometry.Edge → ℝ
  | [], source => variation source
  | target :: targets, source =>
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D
        (continuousCompactOrientedGaugeWilsonFiniteUpdatedVariation
          D variation targets)
        target source

@[simp] theorem continuous_compact_oriented_finiteUpdatedVariation_nil
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (source : C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonFiniteUpdatedVariation
      D variation [] source = variation source := by
  rfl

@[simp] theorem continuous_compact_oriented_finiteUpdatedVariation_cons
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (source : C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonFiniteUpdatedVariation
        D variation (target :: targets) source =
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D
        (continuousCompactOrientedGaugeWilsonFiniteUpdatedVariation
          D variation targets)
        target source := by
  rfl

/-- The closed one-link centered profile has exactly the already-proved sharp
updated variation function; compact recentering introduces no loss. -/
@[simp] theorem continuous_compact_oriented_conditionalExpectationCenteredVariationProfile_variation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target source : C.base.geometry.Edge) :
    (P.conditionalExpectationCenteredVariationProfile D target).variation source =
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D P.variation target source := by
  rfl

/-- Iterate the closed centered-variation/Feller step through an arbitrary
finite ordered list of current physical-link heat-bath updates. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.finiteHeatBathCenteredVariationProfile
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    (targets : List C.base.geometry.Edge) →
      ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C
        (C.finiteSingleLinkHeatBathContinuousBCF targets O)
  | [] => P
  | target :: targets =>
      (P.finiteHeatBathCenteredVariationProfile D targets).conditionalExpectationCenteredVariationProfile D target

@[simp] theorem continuous_compact_oriented_finiteHeatBathCenteredVariationProfile_variation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (targets : List C.base.geometry.Edge)
    (source : C.base.geometry.Edge) :
    (P.finiteHeatBathCenteredVariationProfile D targets).variation source =
      continuousCompactOrientedGaugeWilsonFiniteUpdatedVariation
        D P.variation targets source := by
  induction targets generalizing source with
  | nil =>
      rfl
  | cons target targets ih =>
      rw [continuous_compact_oriented_finiteUpdatedVariation_cons]
      rw [continuous_compact_oriented_conditionalExpectationCenteredVariationProfile_variation]
      unfold continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
      by_cases h : source = target
      · simp [h]
      · simp only [h, if_false]
        rw [ih source, ih target]

end

end MathlibAnalytic
end MGAP4D
