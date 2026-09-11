import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedActualLocalMixedActionRows
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronLocalRatio
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSandwichEquation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The positive scalar left after dividing the normalized crossing scale by
the raw Perron eigenvalue in the exact sandwich equation. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalScale
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : ℝ :=
  finiteEvenFourTorusZ2TemporalCrossingScale
      H β energyIdentity energyNontrivial /
    finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
      H β energyIdentity energyNontrivial hβ hEnergy

/-- The sandwich local scale is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalScale_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalScale
      H β energyIdentity energyNontrivial hβ hEnergy := by
  exact div_pos
    (finiteEvenFourTorusZ2TemporalCrossingScale_pos
      H β energyIdentity energyNontrivial)
    (finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale_pos
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The explicit local factor extracted from the Perron ground: a common
positive scalar times the spatial Wilson half-weight. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalScale
      H β energyIdentity energyNontrivial hβ hEnergy *
    finiteEvenFourTorusZ2SpatialHalfWeight
      H β energyIdentity energyNontrivial B

/-- The extracted Perron local factor is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
      H β energyIdentity energyNontrivial hβ hEnergy B := by
  exact mul_pos
    (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalScale_pos
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2SpatialHalfWeight_pos
      H β energyIdentity energyNontrivial B)

/-- The only potentially nonlocal Perron factor after one exact sandwich
unfolding: the normalized product crossing kernel applied to the spatially
weighted positive ground. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteKernelOperator
      (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
        H β energyIdentity energyNontrivial)
      (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
        H β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy)) B

/-- Pointwise exact factorization of the Perron ground into the explicit local
half-weight factor and the crossing-smoothed residual. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_eq_localFactor_mul_smoothedResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy B =
      finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
          H β energyIdentity energyNontrivial hβ hEnergy B *
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
          H β energyIdentity energyNontrivial hβ hEnergy B := by
  have hSandwich :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_crossingSandwich_apply
      H β energyIdentity energyNontrivial hβ hEnergy B
  have hRawNe :
      finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 :=
    ne_of_gt
      (finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale_pos
        H β energyIdentity energyNontrivial hβ hEnergy)
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalScale
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
  calc
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy B =
      (finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ hEnergy)⁻¹ *
        (finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
            H β energyIdentity energyNontrivial hβ hEnergy B) := by
      field_simp [hRawNe]
    _ =
      (finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ hEnergy)⁻¹ *
        (finiteEvenFourTorusZ2TemporalCrossingScale
            H β energyIdentity energyNontrivial *
          (finiteEvenFourTorusZ2SpatialHalfWeight
              H β energyIdentity energyNontrivial B *
            finiteKernelOperator
              (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
                H β energyIdentity energyNontrivial)
              (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
                H β energyIdentity energyNontrivial
                (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
                  H β energyIdentity energyNontrivial hβ hEnergy)) B)) := by
      rw [hSandwich]
    _ =
      (finiteEvenFourTorusZ2TemporalCrossingScale
            H β energyIdentity energyNontrivial /
          finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
            H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial B) *
        finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
            H β energyIdentity energyNontrivial)
          (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
              H β energyIdentity energyNontrivial hβ hEnergy)) B := by
      rw [div_eq_mul_inv]
      ring

/-- Function-level exact factorization of the Perron ground as a pointwise
product. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_eq_localFactor_product_smoothedResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration H =>
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy B) =
      finitePositiveWeightProduct
        (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
          H β energyIdentity energyNontrivial hβ hEnergy) := by
  funext B
  exact
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_eq_localFactor_mul_smoothedResidual
      H β energyIdentity energyNontrivial hβ hEnergy B

/-- The crossing-smoothed residual is strictly positive, obtained without a
new kernel assumption from the positive Perron ground and the positive local
factor in the exact factorization. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
      H β energyIdentity energyNontrivial hβ hEnergy B := by
  have hProduct :
      0 < finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
          H β energyIdentity energyNontrivial hβ hEnergy B *
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
          H β energyIdentity energyNontrivial hβ hEnergy B := by
    rw [←
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_eq_localFactor_mul_smoothedResidual]
    exact
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ hEnergy B
  have hLocalNonneg :
      0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
        H β energyIdentity energyNontrivial hβ hEnergy B :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor_pos
        H β energyIdentity energyNontrivial hβ hEnergy B)
  by_contra hNot
  have hResidualNonpos :
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
        H β energyIdentity energyNontrivial hβ hEnergy B ≤ 0 :=
    le_of_not_gt hNot
  have hProductNonpos :=
    mul_nonpos_of_nonneg_of_nonpos hLocalNonneg hResidualNonpos
  linarith

/-- Perron-ground four-point cross-ratio bounds split into an explicit local
half-weight factor and the crossing-smoothed residual.  No nonlocal estimate
is hidden in this theorem. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_crossRatio_of_local_and_smoothedResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (localRatio residualRatio : ℝ)
    (hLocalRatio : 0 ≤ localRatio)
    (hResidualRatio : 0 ≤ residualRatio)
    (hLocal :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
          H β energyIdentity energyNontrivial hβ hEnergy)
        A C target localRatio)
    (hResidual :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
          H β energyIdentity energyNontrivial hβ hEnergy)
        A C target residualRatio) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (fun B : FiniteEvenFourTorusZ2SliceConfiguration H =>
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy B)
      A C target (localRatio * residualRatio) := by
  rw [
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_eq_localFactor_product_smoothedResidual]
  exact
    finitePositiveWeightProduct_singleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
        H β energyIdentity energyNontrivial hβ hEnergy)
      (fun B => le_of_lt
        (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor_pos
          H β energyIdentity energyNontrivial hβ hEnergy B))
      (fun B => le_of_lt
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_pos
          H β energyIdentity energyNontrivial hβ hEnergy B))
      A C target localRatio residualRatio hLocalRatio hResidualRatio
      hLocal hResidual

end

end MathlibAnalytic
end MGAP4D
