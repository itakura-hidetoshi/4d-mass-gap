import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingCoordinateMismatch
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobParallelCouplingStability
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorPerronSmoothedMixtureCouplingHammingCostSplit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Expected disagreement at one spatial link under a pair of normalized
residual-gauge Perron-smoothed posterior component couplings. -/
noncomputable def
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
    C β hβ hβCutoff H left right g h).expectedFiniteProductCoordinateMismatch
      source

/-- Expected disagreement at one output link under the exact-marginal actual
geometric one-slab Perron Doob mixture coupling. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCouplingData
    C β hβ hβCutoff H left right).expectedFiniteProductCoordinateMismatch
      source

/-- One-coordinate mismatch of the actual geometric Doob mixture is
nonnegative. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_nonneg
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
      C β hβ hβCutoff H left right source := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCouplingData
      C β hβ hβCutoff H left right).expectedFiniteProductCoordinateMismatch_nonneg
        source

/-- One-coordinate mismatch is bounded by one independently of the number of
spatial links. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_one
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤ 1 := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCouplingData
      C β hβ hβCutoff H left right).expectedFiniteProductCoordinateMismatch_le_one
        source

/-- Same-index coordinate estimates and the latent residual-gauge index
mismatch control a coordinate of the full geometric Doob mixture.  The
unequal-index contribution costs only one at a fixed coordinate. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_diagonal_add_indexDisagreement
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (diagonalBound :
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H → ℝ)
    (hDiagonal :
      ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch
            C β hβ hβCutoff H left right g g source ≤ diagonalBound g) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤
      (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g * diagonalBound g) +
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).disagreementMass := by
  let indexCoupling :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right
  let componentCoupling :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
      C β hβ hβCutoff H left right
  have hDiagonal' :
      ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (componentCoupling g g).expectedCost
            (fun X Y => finiteProductMismatchIndicator X Y source) ≤
          diagonalBound g := by
    intro g
    simpa [componentCoupling,
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch,
      FiniteRealCouplingData.expectedFiniteProductCoordinateMismatch]
      using hDiagonal g
  have hOffDiagonal :
      ∀ g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        g ≠ h →
          (componentCoupling g h).expectedCost
              (fun X Y => finiteProductMismatchIndicator X Y source) ≤ 1 := by
    intro g h _hNe
    exact
      (componentCoupling g h).expectedFiniteProductCoordinateMismatch_le_one
        source
  have h :=
    finiteRealProbabilityMixtureCoupling_expectedCost_le_diagonal_add_disagreement
      indexCoupling componentCoupling
      (fun X Y => finiteProductMismatchIndicator X Y source)
      diagonalBound 1 hDiagonal' hOffDiagonal
  simpa [indexCoupling, componentCoupling,
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch,
    FiniteRealCouplingData.expectedFiniteProductCoordinateMismatch] using h

/-- The residual-gauge obstruction term is exactly one half of the unhalved
`L¹` distance between the two latent index laws. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_diagonal_add_halfIndexL1
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (diagonalBound :
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H → ℝ)
    (hDiagonal :
      ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch
            C β hβ hβCutoff H left right g g source ≤ diagonalBound g) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤
      (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g * diagonalBound g) +
        (2 : ℝ)⁻¹ *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H left).l1Distance
            (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
              C β hβ hβCutoff H right) := by
  rw [←
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_disagreementMass_eq_half_mul_l1Distance
      C β hβ hβCutoff H left right]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_diagonal_add_indexDisagreement
      C β hβ hβCutoff H left right source diagonalBound hDiagonal

/-- Local influence data for the exact actual geometric Doob mixture coupling.
The high-temperature cutoff proof is part of the type.  Positivity and both
Doob marginals are not assumptions: they are generated from the integrated
mixture coupling. -/
structure Z2UnfixedGaugeDoobMixtureVolumeInfluenceData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (hβCutoff : β ≤ C.couplingCutoff) where
  influence :
    FiniteEvenFourTorusSpatialLink H →
      FiniteEvenFourTorusSpatialLink H → ℝ
  influence_nonneg :
    ∀ target source : FiniteEvenFourTorusSpatialLink H,
      0 ≤ influence target source
  mixtureMismatch_le :
    ∀ (target source : FiniteEvenFourTorusSpatialLink H)
      (left right : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff left right target →
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
            C β hβ hβCutoff H left right source ≤
          influence target source
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  columnSum_le_coefficient :
    ∀ source : FiniteEvenFourTorusSpatialLink H,
      (∑ target : FiniteEvenFourTorusSpatialLink H,
        influence target source) ≤ coefficient
  coefficient_lt_one : coefficient < 1

namespace Z2UnfixedGaugeDoobMixtureVolumeInfluenceData

variable
  {H : ℕ}
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}
  {C : Z2PerronPosteriorActualHighTemperatureContinuationData
    energyIdentity energyNontrivial hEnergy}
  {hβCutoff : β ≤ C.couplingCutoff}

/-- Convert actual-mixture coordinate influence data into the existing
model-facing coordinate-coupling package for the full geometric Perron Doob
kernel. -/
noncomputable def toDoobParallelVolumeCouplingData
    (D : Z2UnfixedGaugeDoobMixtureVolumeInfluenceData
      H β energyIdentity energyNontrivial hβ hEnergy C hβCutoff) :
    Z2UnfixedGaugeDoobParallelVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy :=
  { influence := D.influence
    influence_nonneg := D.influence_nonneg
    coupling := fun _target left right X Y =>
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling
        C β hβ hβCutoff H left right X Y
    coupling_nonneg := by
      intro target left right X Y _hAgree
      exact
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_nonneg
          C β hβ hβCutoff H left right X Y
    left_marginal := by
      intro target left right X _hAgree
      exact
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_leftMarginal
          C β hβ hβCutoff H left right X
    right_marginal := by
      intro target left right Y _hAgree
      exact
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_rightMarginal
          C β hβ hβCutoff H left right Y
    mismatchExpectation_le := by
      intro target source left right hAgree
      change
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
            C β hβ hβCutoff H left right source ≤
          D.influence target source
      exact D.mixtureMismatch_le target source left right hAgree
    coefficient := D.coefficient
    coefficient_nonneg := D.coefficient_nonneg
    columnSum_le_coefficient := D.columnSum_le_coefficient
    coefficient_lt_one := D.coefficient_lt_one }

@[simp] theorem toDoobParallelVolumeCouplingData_coefficient
    (D : Z2UnfixedGaugeDoobMixtureVolumeInfluenceData
      H β energyIdentity energyNontrivial hβ hEnergy C hβCutoff) :
    D.toDoobParallelVolumeCouplingData.coefficient = D.coefficient :=
  rfl

end Z2UnfixedGaugeDoobMixtureVolumeInfluenceData

end

end MathlibAnalytic
end MGAP4D
