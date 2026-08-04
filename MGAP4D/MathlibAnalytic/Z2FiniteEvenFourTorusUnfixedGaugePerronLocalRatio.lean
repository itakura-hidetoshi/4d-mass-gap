import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialIncidenceBound
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSandwichEquation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The explicit all-volume one-link likelihood-ratio majorant for the actual
positive Perron ground: one local spatial Wilson half-weight factor and one
normalized temporal crossing factor. -/
def z2UnfixedGaugePerronSingleLinkRatio
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  Real.exp (6 * β * (energyNontrivial - energyIdentity)) *
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)

/-- The Perron one-link ratio is strictly positive at strict coupling. -/
theorem z2UnfixedGaugePerronSingleLinkRatio_pos
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 < z2UnfixedGaugePerronSingleLinkRatio
      β energyIdentity energyNontrivial := by
  unfold z2UnfixedGaugePerronSingleLinkRatio
  exact mul_pos (Real.exp_pos _)
    (finiteZ2CrossingLikelihoodRatio_pos
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))

/-- Spatial half-weight times the actual positive Perron ground is
pointwise nonnegative. -/
theorem finiteEvenFourTorusZ2SpatialWeightedPositiveGround_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteBoundaryPointwiseNonnegative
      (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
        H β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy)) := by
  intro A
  rw [finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator_apply]
  exact mul_nonneg
    (le_of_lt
      (finiteEvenFourTorusZ2SpatialHalfWeight_pos
        H β energyIdentity energyNontrivial A))
    (le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ hEnergy A))

/-- The normalized crossing smoother applied to the spatially weighted Perron
ground is pointwise nonnegative. -/
theorem finiteEvenFourTorusZ2CrossingSpatialWeightedPositiveGround_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤
      finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
            H β energyIdentity energyNontrivial)
          (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
              H β energyIdentity energyNontrivial hβ.le hEnergy.le)) B := by
  rw [finiteKernelOperator_apply]
  apply Finset.sum_nonneg
  intro A _hA
  exact mul_nonneg
    (by
      unfold finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
      exact finiteZ2GaugeNormalizedProductKernel_nonneg
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy).le
        (FiniteEvenFourTorusSpatialLink H) A B)
    (finiteEvenFourTorusZ2SpatialWeightedPositiveGround_nonneg
      H β energyIdentity energyNontrivial hβ.le hEnergy.le A)

/-- The product crossing smoother changes by at most the sharp dimension-free
one-coordinate likelihood ratio when the observed boundary configuration is
updated at one spatial link. -/
theorem finiteEvenFourTorusZ2CrossingSpatialWeightedPositiveGround_le_ratio_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
            H β energyIdentity energyNontrivial)
          (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
              H β energyIdentity energyNontrivial hβ.le hEnergy.le)) B ≤
      finiteZ2CrossingLikelihoodRatio
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial) *
        finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
            H β energyIdentity energyNontrivial)
          (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
              H β energyIdentity energyNontrivial hβ.le hEnergy.le))
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  simpa [finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel] using
    finiteZ2GaugeNormalizedProductKernel_operator_le_likelihoodRatio_mul_replace
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
      (FiniteEvenFourTorusSpatialLink H)
      (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
        H β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ.le hEnergy.le))
      (finiteEvenFourTorusZ2SpatialWeightedPositiveGround_nonneg
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      B e g

/-- The exact Perron sandwich equation, the all-volume twelve-plaquette spatial
incidence bound, and the dimension-free crossing likelihood ratio give an
explicit all-volume one-link ratio for the actual positive Perron ground. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_le_singleLinkRatio_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ.le hEnergy.le B ≤
      z2UnfixedGaugePerronSingleLinkRatio
          β energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  let E := Real.exp (6 * β * (energyNontrivial - energyIdentity))
  let R := finiteZ2CrossingLikelihoodRatio
    (z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)
  let p := finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  let a := finiteEvenFourTorusZ2SpatialHalfWeight
    H β energyIdentity energyNontrivial
  let f := finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
    H β energyIdentity energyNontrivial p
  let P := finiteKernelOperator
    (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
      H β energyIdentity energyNontrivial)
  let B' := finiteZ2GaugeReplaceCoordinate B e g
  have ha : a B ≤ E * a B' := by
    simpa [a, E, B'] using
      finiteEvenFourTorusZ2SpatialHalfWeight_le_exp_twelve_mul_replace
        H β energyIdentity energyNontrivial hβ.le hEnergy.le B e g
  have hP : P f B ≤ R * P f B' := by
    simpa [P, f, R, B', p] using
      finiteEvenFourTorusZ2CrossingSpatialWeightedPositiveGround_le_ratio_mul_replace
        H β energyIdentity energyNontrivial hβ hEnergy B e g
  have hPB0 : 0 ≤ P f B := by
    simpa [P, f, p] using
      finiteEvenFourTorusZ2CrossingSpatialWeightedPositiveGround_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy B
  have haB'0 : 0 ≤ a B' :=
    le_of_lt
      (finiteEvenFourTorusZ2SpatialHalfWeight_pos
        H β energyIdentity energyNontrivial B')
  have hE0 : 0 ≤ E := le_of_lt (Real.exp_pos _)
  have hProduct :
      a B * P f B ≤ (E * R) * (a B' * P f B') := by
    calc
      a B * P f B ≤ (E * a B') * P f B :=
        mul_le_mul_of_nonneg_right ha hPB0
      _ ≤ (E * a B') * (R * P f B') :=
        mul_le_mul_of_nonneg_left hP (mul_nonneg hE0 haB'0)
      _ = (E * R) * (a B' * P f B') := by ring
  have hscale0 :
      0 ≤ finiteEvenFourTorusZ2TemporalCrossingScale
        H β energyIdentity energyNontrivial :=
    le_of_lt
      (finiteEvenFourTorusZ2TemporalCrossingScale_pos
        H β energyIdentity energyNontrivial)
  have hScaled :
      finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial * (a B * P f B) ≤
        (E * R) *
          (finiteEvenFourTorusZ2TemporalCrossingScale
            H β energyIdentity energyNontrivial * (a B' * P f B')) := by
    calc
      finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial * (a B * P f B) ≤
        finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial *
            ((E * R) * (a B' * P f B')) :=
        mul_le_mul_of_nonneg_left hProduct hscale0
      _ = (E * R) *
          (finiteEvenFourTorusZ2TemporalCrossingScale
            H β energyIdentity energyNontrivial * (a B' * P f B')) := by
        ring
  have hEqB :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_crossingSandwich_apply
      H β energyIdentity energyNontrivial hβ.le hEnergy.le B
  have hEqB' :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_crossingSandwich_apply
      H β energyIdentity energyNontrivial hβ.le hEnergy.le B'
  change
    finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial * (a B * P f B) =
      finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ.le hEnergy.le * p B at hEqB
  change
    finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial * (a B' * P f B') =
      finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ.le hEnergy.le * p B' at hEqB'
  rw [hEqB, hEqB'] at hScaled
  have hρ :
      0 < finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
        H β energyIdentity energyNontrivial hβ.le hEnergy.le :=
    finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale_pos
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  apply (mul_le_mul_left hρ).mp
  calc
    finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ.le hEnergy.le * p B ≤
      (E * R) *
        (finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ.le hEnergy.le * p B') := hScaled
    _ = finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ.le hEnergy.le *
        ((E * R) * p B') := by ring
    _ = finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ.le hEnergy.le *
        (z2UnfixedGaugePerronSingleLinkRatio
          β energyIdentity energyNontrivial * p B') := by
      rfl

end

end MathlibAnalytic
end MGAP4D
