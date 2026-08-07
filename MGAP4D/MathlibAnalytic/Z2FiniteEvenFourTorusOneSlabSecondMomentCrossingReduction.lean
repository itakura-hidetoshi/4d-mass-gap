import MGAP4D.MathlibAnalytic.FiniteUniformSlabSecondMomentDoubleCentering
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabKernelSecondVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalLinkCrossingAverage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Boundary-independent uniform temporal-link crossing mean, anchored at the
identity boundary pair. -/
noncomputable def finiteEvenFourTorusZ2TemporalCrossingMean
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) : ℝ :=
  (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
    ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H 0 energyIdentity energyNontrivial U 1 1

/-- Every boundary pair has exactly the same uniform crossing mean. -/
theorem finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq_crossingMean
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
            H 0 energyIdentity energyNontrivial U A B) =
      finiteEvenFourTorusZ2TemporalCrossingMean
        H energyIdentity energyNontrivial := by
  unfold finiteEvenFourTorusZ2TemporalCrossingMean
  exact
    finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq
      H 0 energyIdentity energyNontrivial A B 1 1

/-- Uniform temporal-link second moment of the crossing action alone. -/
noncomputable def finiteEvenFourTorusZ2TemporalCrossingSecondMoment
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteUniformCrossingSecondMoment
    (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
      fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
        finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
          H 0 energyIdentity energyNontrivial U A B)
    A B

/-- The interaction kernel left after removing one-boundary additive terms from
the raw slab-action second moment.  It is kept in the generic exact form here;
the next theorem identifies the spatial part as `(1/2) S(A) S(B)`. -/
noncomputable def finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteUniformSlabSecondMomentInteraction
    (fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
      (1 / 2 : ℝ) *
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial A)
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration H =>
      (1 / 2 : ℝ) *
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial B)
    (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
      fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
        finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
          H 0 energyIdentity energyNontrivial U A B)
    A B

/-- Pointwise identification of the surviving spatial rank-one term. -/
theorem finiteEvenFourTorusZ2OneSlabSecondMomentInteraction_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
        H energyIdentity energyNontrivial A B =
      finiteEvenFourTorusZ2TemporalCrossingSecondMoment
          H energyIdentity energyNontrivial A B +
        (1 / 2 : ℝ) *
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial A *
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial B := by
  unfold finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
    finiteEvenFourTorusZ2TemporalCrossingSecondMoment
    finiteUniformSlabSecondMomentInteraction
  ring

/-- The actual raw beta-zero one-slab kernel second variation is exactly the
generic uniform slab second moment. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_eq_uniformSlabSecondMoment
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
        H energyIdentity energyNontrivial A B =
      finiteUniformSlabSecondMoment
        (fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
          (1 / 2 : ℝ) *
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial A)
        (fun B : FiniteEvenFourTorusZ2SliceConfiguration H =>
          (1 / 2 : ℝ) *
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial B)
        (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
          fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
            finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
              H 0 energyIdentity energyNontrivial U A B)
        A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
    finiteUniformSlabSecondMoment
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
  rfl

/-- Exact double-centered raw second-moment reduction:

`Q K₂ Q = Q (M₂_cross + (1/2) S ⊗ S) Q`.

All spatial-square terms and all terms involving only the boundary-independent
first crossing mean disappear under double centering. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_doubleCentered_eq_interaction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
            H energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) =
      finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
            H energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) := by
  have hGeneric :=
    finiteUniformAverageComplement_comp_finiteUniformSlabSecondMoment_eq_interaction
      (α := FiniteEvenFourTorusZ2SliceConfiguration H)
      (γ := FiniteEvenFourTorusZ2TemporalLinkField H)
      (fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
        (1 / 2 : ℝ) *
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial A)
      (fun B : FiniteEvenFourTorusZ2SliceConfiguration H =>
        (1 / 2 : ℝ) *
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial B)
      (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
        fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
          finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
            H 0 energyIdentity energyNontrivial U A B)
      (finiteEvenFourTorusZ2TemporalCrossingMean
        H energyIdentity energyNontrivial)
      (finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq_crossingMean
        H energyIdentity energyNontrivial)
  simpa only [
    ← finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_eq_uniformSlabSecondMoment]
    using hGeneric

/-- Audit-visible actual finite-Z₂ crossing-reduction receipt. -/
structure Z2FiniteEvenFourTorusOneSlabSecondMomentCrossingReductionPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) where
  crossingMeanIndependent :
    ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
              H 0 energyIdentity energyNontrivial U A B) =
        finiteEvenFourTorusZ2TemporalCrossingMean
          H energyIdentity energyNontrivial
  rawSecondMomentReduction :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
            H energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) =
      finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
            H energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap)

/-- Construct the actual finite-Z₂ crossing-reduction receipt. -/
noncomputable def z2FiniteEvenFourTorusOneSlabSecondMomentCrossingReductionPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Z2FiniteEvenFourTorusOneSlabSecondMomentCrossingReductionPackage
      H energyIdentity energyNontrivial where
  crossingMeanIndependent :=
    finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq_crossingMean
      H energyIdentity energyNontrivial
  rawSecondMomentReduction :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_doubleCentered_eq_interaction
      H energyIdentity energyNontrivial

end

end MathlibAnalytic
end MGAP4D
