import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinApproximateTensorization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSingleLinkConditional
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobSpectralCentering
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Total actual Perron one-link conditional variance, integrated against the
reversible density `p²` and summed over all spatial links. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronTotalSingleLinkVariance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) : ℝ :=
  finitePositiveWeightTotalSingleSiteVariance
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy)
    (fun A => f A)

/-- The actual Doob weighted mean is exactly the generic first moment against
its Perron density. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_weightedMean_eq_positiveWeightSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ hEnergy).weightedMean f =
      finitePositiveWeightSum
        (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
          H β energyIdentity energyNontrivial hβ hEnergy)
        (fun A => f A) := by
  rfl

/-- The actual Doob weighted norm is exactly the generic self-pairing against
its Perron density. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_weightedNormSq_eq_positiveWeightPairing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ hEnergy).weightedNormSq f =
      finitePositiveWeightPairing
        (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
          H β energyIdentity energyNontrivial hβ hEnergy)
        (fun A => f A) (fun A => f A) := by
  rfl

/-- The actual Perron-density specialization of generic Dobrushin approximate
tensorization. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerron_approximateTensorization
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (D : FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
        H β energyIdentity energyNontrivial hβ hEnergy))
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (hMean :
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).weightedMean f = 0) :
    finitePositiveWeightDobrushinHeatBathGap D *
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).weightedNormSq f ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronTotalSingleLinkVariance
        H β energyIdentity energyNontrivial hβ hEnergy f := by
  have hCard :
      0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
    Fintype.card_pos
  have hGeneric :=
    finitePositiveWeightDobrushin_approximateTensorization
      (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
        H β energyIdentity energyNontrivial hβ hEnergy)
      D hCard (fun A => f A) (by
        simpa [finiteEvenFourTorusZ2UnfixedGauge_weightedMean_eq_positiveWeightSum]
          using hMean)
  simpa [finiteEvenFourTorusZ2UnfixedGaugePerronTotalSingleLinkVariance,
    finiteEvenFourTorusZ2UnfixedGauge_weightedNormSq_eq_positiveWeightPairing]
    using hGeneric

/-- Proof-relevant all-volume input for the remaining two model-specific
inequalities: a uniform Dobrushin margin for the actual Perron density and a
uniform comparison of its one-link variance sum with the actual Doob joint
Dirichlet form. -/
structure Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  margin : ℝ
  margin_pos : 0 < margin
  comparisonConstant : ℝ
  comparisonConstant_pos : 0 < comparisonConstant
  dobrushinData : ∀ H : ℕ,
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  margin_le_dobrushinGap : ∀ H : ℕ,
    margin ≤ finitePositiveWeightDobrushinHeatBathGap (dobrushinData H)
  totalSingleLinkVariance_le_doobDirichlet :
    ∀ (H : ℕ) (f : FiniteEvenFourTorusZ2SliceHilbert H),
      finiteEvenFourTorusZ2UnfixedGaugePerronTotalSingleLinkVariance
          H β energyIdentity energyNontrivial hβ.le hEnergy.le f ≤
        comparisonConstant *
          ((finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
              H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedNormSq f -
            (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
              H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedDoobQuadratic f)

namespace Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate

variable
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}

/-- Uniform Rayleigh rate produced by approximate tensorization followed by
Doob Dirichlet comparison. -/
def rayleighRate
    (C : Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate
      β energyIdentity energyNontrivial hβ hEnergy) : ℝ :=
  1 - C.margin / C.comparisonConstant

/-- The two model-specific comparison inequalities imply the actual all-volume
weighted Doob Rayleigh estimate. -/
theorem weightedDoobRayleigh
    (C : Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (hMean :
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedMean f = 0) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedDoobQuadratic f ≤
      C.rayleighRate *
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedNormSq f := by
  let N :=
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedNormSq f
  let Q :=
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedDoobQuadratic f
  let V :=
    finiteEvenFourTorusZ2UnfixedGaugePerronTotalSingleLinkVariance
      H β energyIdentity energyNontrivial hβ.le hEnergy.le f
  have hN : 0 ≤ N := by
    dsimp [N]
    rw [FiniteKernelGroundStateDoobData.weightedNormSq_eq_norm_sq]
    exact sq_nonneg _
  have hTensor :=
    finiteEvenFourTorusZ2UnfixedGaugePerron_approximateTensorization
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      (C.dobrushinData H) f hMean
  have hMarginTensor : C.margin * N ≤ V := by
    calc
      C.margin * N ≤
          finitePositiveWeightDobrushinHeatBathGap (C.dobrushinData H) * N :=
        mul_le_mul_of_nonneg_right (C.margin_le_dobrushinGap H) hN
      _ ≤ V := by
        simpa [N, V] using hTensor
  have hCompare : V ≤ C.comparisonConstant * (N - Q) := by
    simpa [N, Q, V] using C.totalSingleLinkVariance_le_doobDirichlet H f
  have hCombined :
      C.comparisonConstant * Q ≤
        (C.comparisonConstant - C.margin) * N := by
    nlinarith
  calc
    Q ≤ ((C.comparisonConstant - C.margin) * N) /
        C.comparisonConstant :=
      (le_div_iff₀ C.comparisonConstant_pos).2 hCombined
    _ = C.rayleighRate * N := by
      unfold rayleighRate
      field_simp [ne_of_gt C.comparisonConstant_pos]
      ring

/-- The produced Rayleigh rate is strictly below one. -/
theorem rayleighRate_lt_one
    (C : Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    C.rayleighRate < 1 := by
  unfold rayleighRate
  have hRatio : 0 < C.margin / C.comparisonConstant :=
    div_pos C.margin_pos C.comparisonConstant_pos
  linarith

/-- The exact degradation relative to the temporal-crossing reference rate. -/
def degradation
    (C : Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate
      β energyIdentity energyNontrivial hβ hEnergy) : ℝ :=
  C.rayleighRate -
    z2WilsonTemporalCrossingRate β energyIdentity energyNontrivial

/-- Once the explicit produced rate lies in the existing spatial-sandwich
window, the full weighted-Doob stability certificate is constructed. -/
noncomputable def toWeightedDoobUniformStabilityCertificate
    (C : Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (hDegradationNonneg : 0 ≤ C.degradation)
    (hDegradationLt :
      C.degradation < z2WilsonTemporalCrossingCoercivity
        β energyIdentity energyNontrivial) :
    Z2UnfixedGaugeWeightedDoobUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  { degradation := C.degradation
    degradation_nonneg := hDegradationNonneg
    degradation_lt_crossingCoercivity := hDegradationLt
    weightedDoobRayleigh := by
      intro H f hMean
      have h := C.weightedDoobRayleigh H f hMean
      simpa [degradation] using h }

/-- Exact terminal conversion into the existing actual spatial-sandwich
stability certificate. -/
noncomputable def toSpatialSandwichCertificate
    (C : Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (hDegradationNonneg : 0 ≤ C.degradation)
    (hDegradationLt :
      C.degradation < z2WilsonTemporalCrossingCoercivity
        β energyIdentity energyNontrivial) :
    Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  (C.toWeightedDoobUniformStabilityCertificate
    hDegradationNonneg hDegradationLt).toSpatialSandwichCertificate

end Z2UnfixedGaugePerronDobrushinDoobComparisonCertificate

end

end MathlibAnalytic
end MGAP4D
