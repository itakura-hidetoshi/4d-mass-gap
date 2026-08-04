import MGAP4D.MathlibAnalytic.FiniteKernelDiagonalSandwich
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialHalfWeightBounds
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalCrossingRawNormalization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalGaugeOneSlabTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Diagonal multiplication by the actual spatial Wilson half-weight on one
finite spatial-slice Hilbert space. -/
noncomputable def finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ) :
    FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteBoundaryMultiplicationOperator
    (finiteEvenFourTorusZ2SpatialHalfWeight
      H β energyIdentity energyNontrivial)

@[simp] theorem finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
        H β energyIdentity energyNontrivial f A =
      finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial A * f A :=
  rfl

/-- The spatial half-weight multiplication operator is injective because every
finite Wilson half-weight is strictly positive. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator_injective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ) :
    Function.Injective
      (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
        H β energyIdentity energyNontrivial) := by
  apply finiteBoundaryMultiplicationOperator_injective
  intro A
  exact ne_of_gt
    (finiteEvenFourTorusZ2SpatialHalfWeight_pos
      H β energyIdentity energyNontrivial A)

/-- Exact operator factorization of the full temporal-gauge one-slab raw
transfer as `M_a K_cross M_a`. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_eq_spatialSandwich
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy =
      (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
        H β energyIdentity energyNontrivial).comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
            H β energyIdentity energyNontrivial hβ hEnergy).kernel).comp
          (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial)) := by
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
  exact finiteGramKernelOperator_sandwich_eq
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2SpatialHalfWeight
      H β energyIdentity energyNontrivial)

/-- The full raw one-slab quadratic form is exactly the raw crossing quadratic
form evaluated on the spatially weighted boundary vector. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_quadratic_eq_weightedCrossing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f) f =
      inner ℝ
        (finiteKernelOperator
          (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
            H β energyIdentity energyNontrivial hβ hEnergy).kernel
          (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial f))
        (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
          H β energyIdentity energyNontrivial f) := by
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
  exact finiteGramKernelOperator_sandwich_quadratic
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2SpatialHalfWeight
      H β energyIdentity energyNontrivial) f

/-- Combining the exact raw crossing scale with the diagonal sandwich gives a
scalar times the stochastic crossing transfer between the same two spatial
half-weight multipliers. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_eq_crossingScale_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial •
        ((finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
          H β energyIdentity energyNontrivial).comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
              H β energyIdentity energyNontrivial)).comp
            (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
              H β energyIdentity energyNontrivial))) := by
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_eq_spatialSandwich,
    finiteEvenFourTorusZ2TemporalGaugeCrossingOperator_eq_scale_smul_normalized]
  ext f A
  simp [ContinuousLinearMap.comp_apply]
  ring

/-- Exact scalar-weighted stochastic crossing representation of the full raw
quadratic form. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_quadratic_eq_crossingScale_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f) f =
      finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial *
        inner ℝ
          (finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
              H β energyIdentity energyNontrivial)
            (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
              H β energyIdentity energyNontrivial f))
          (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial f) := by
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_quadratic_eq_weightedCrossing,
    finiteEvenFourTorusZ2TemporalGaugeCrossingOperator_eq_scale_smul_normalized,
    ContinuousLinearMap.smul_apply, real_inner_smul_left]

/-- The crossing Poincare estimate applies exactly to the spatially weighted
vector whenever that weighted vector has zero finite mass. -/
theorem finiteEvenFourTorusZ2SpatialWeightedCrossing_poincare
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (hmass : finiteFunctionMass
      (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
        H β energyIdentity energyNontrivial f) = 0) :
    z2WilsonTemporalCrossingCoercivity
          β energyIdentity energyNontrivial *
        ‖finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
          H β energyIdentity energyNontrivial f‖ ^ 2 ≤
      inner ℝ
        (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial f -
          finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
              H β energyIdentity energyNontrivial)
            (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
              H β energyIdentity energyNontrivial f))
        (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
          H β energyIdentity energyNontrivial f) :=
  finiteEvenFourTorusZ2NormalizedTemporalCrossing_poincare
    H β energyIdentity energyNontrivial hβ hEnergy
      (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
        H β energyIdentity energyNontrivial f) hmass

end

end MathlibAnalytic
end MGAP4D
