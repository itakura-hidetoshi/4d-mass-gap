import MGAP4D.MathlibAnalytic.FiniteProductDoobParallelVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobSpectralCentering
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A proof-relevant all-volume direct parallel variation package for the
actual Perron Doob operators.  The common rate is required to lie between the
bare temporal-crossing rate and one, while every finite-volume variation
coefficient is bounded by that same rate. -/
structure Z2UnfixedGaugeDoobParallelUniformVariationCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  rate : ℝ
  crossingRate_le_rate :
    z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial ≤ rate
  rate_lt_one : rate < 1
  variationCertificate : ∀ H : ℕ,
    FiniteProductDoobParallelVariationCertificate
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  coefficient_le_rate : ∀ H : ℕ,
    (variationCertificate H).variationData.coefficient ≤ rate

namespace Z2UnfixedGaugeDoobParallelUniformVariationCertificate

variable
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}

/-- The degradation of the direct parallel Doob rate relative to the bare
one-coordinate temporal-crossing rate. -/
def degradation
    (C : Z2UnfixedGaugeDoobParallelUniformVariationCertificate
      β energyIdentity energyNontrivial hβ hEnergy) : ℝ :=
  C.rate -
    z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial

/-- The direct parallel variation package yields the actual all-volume
weighted Doob Rayleigh estimate at the common rate. -/
theorem weightedDoobRayleigh
    (C : Z2UnfixedGaugeDoobParallelUniformVariationCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (hMean :
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedMean f = 0) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedDoobQuadratic f ≤
      C.rate *
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedNormSq f := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  have hDirect :=
    finiteProductDoob_centered_parallel_rayleigh_le
      D (C.variationCertificate H) f hMean
  have hNorm : 0 ≤ D.weightedNormSq f := by
    rw [FiniteKernelGroundStateDoobData.weightedNormSq_eq_norm_sq]
    exact sq_nonneg _
  calc
    D.weightedDoobQuadratic f ≤
        (C.variationCertificate H).variationData.coefficient *
          D.weightedNormSq f := hDirect
    _ ≤ C.rate * D.weightedNormSq f :=
      mul_le_mul_of_nonneg_right (C.coefficient_le_rate H) hNorm

/-- The degradation is nonnegative because the common Doob rate is no better
than the bare crossing reference chosen by the existing sandwich package. -/
theorem degradation_nonneg
    (C : Z2UnfixedGaugeDoobParallelUniformVariationCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    0 ≤ C.degradation := by
  unfold degradation
  linarith [C.crossingRate_le_rate]

/-- A common direct parallel rate below one automatically places the
degradation strictly below the existing crossing-coercivity window. -/
theorem degradation_lt_crossingCoercivity
    (C : Z2UnfixedGaugeDoobParallelUniformVariationCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    C.degradation < z2WilsonTemporalCrossingCoercivity
      β energyIdentity energyNontrivial := by
  unfold degradation z2WilsonTemporalCrossingCoercivity
  linarith [C.rate_lt_one]

/-- Convert the direct parallel variation package into the existing
proof-relevant weighted-Doob stability interface. -/
noncomputable def toWeightedDoobUniformStabilityCertificate
    (C : Z2UnfixedGaugeDoobParallelUniformVariationCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeWeightedDoobUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  { degradation := C.degradation
    degradation_nonneg := C.degradation_nonneg
    degradation_lt_crossingCoercivity :=
      C.degradation_lt_crossingCoercivity
    weightedDoobRayleigh := by
      intro H f hMean
      have h := C.weightedDoobRayleigh H f hMean
      convert h using 1
      unfold degradation
      ring }

/-- Exact terminal conversion into the actual spatial-sandwich stability
certificate.  No random-scan/local-variance comparison is used. -/
noncomputable def toSpatialSandwichCertificate
    (C : Z2UnfixedGaugeDoobParallelUniformVariationCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  C.toWeightedDoobUniformStabilityCertificate.toSpatialSandwichCertificate

end Z2UnfixedGaugeDoobParallelUniformVariationCertificate

end

end MathlibAnalytic
end MGAP4D
