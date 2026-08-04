import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabSandwichFactorization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingUniformCenteredPoincareCompletePackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- A volume-independent quantitative stability estimate for inserting the
spatial Wilson half-weight sandwich into the uniform temporal-crossing
backbone.  The single remaining analytic number `degradation` must be strictly
smaller than the explicit crossing coercivity. -/
structure Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  degradation : ℝ
  degradation_nonneg : 0 ≤ degradation
  degradation_lt_crossingCoercivity :
    degradation < z2WilsonTemporalCrossingCoercivity
      β energyIdentity energyNontrivial
  fullCenteredRayleigh :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0 →
        inner ℝ
            (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
              H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x ≤
          (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial + degradation) * ‖x‖ ^ 2

namespace Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (S : Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- The stable full-transfer contraction rate is the crossing rate plus the
uniform spatial-sandwich degradation. -/
def fullRate : ℝ :=
  z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial + S.degradation

/-- The full rate remains strictly positive. -/
theorem fullRate_pos : 0 < S.fullRate := by
  unfold fullRate
  exact add_pos_of_pos_of_nonneg
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy)
    S.degradation_nonneg

/-- The strict stability margin keeps the full rate below one. -/
theorem fullRate_lt_one : S.fullRate < 1 := by
  unfold fullRate
  have hdeg := S.degradation_lt_crossingCoercivity
  unfold z2WilsonTemporalCrossingCoercivity at hdeg
  linarith

/-- The corresponding full-transfer coercivity is the crossing coercivity
minus the spatial-sandwich degradation. -/
def fullCoercivity : ℝ :=
  z2WilsonTemporalCrossingCoercivity
      β energyIdentity energyNontrivial - S.degradation

/-- The full coercivity remains strictly positive exactly because the
sandwich degradation is below the crossing coercivity. -/
theorem fullCoercivity_pos : 0 < S.fullCoercivity := by
  unfold fullCoercivity
  exact sub_pos.mpr S.degradation_lt_crossingCoercivity

/-- The full coercivity remains below one. -/
theorem fullCoercivity_lt_one : S.fullCoercivity < 1 := by
  unfold fullCoercivity
  have hk := z2WilsonTemporalCrossingCoercivity_lt_one hβ hEnergy
  linarith [S.degradation_nonneg]

/-- Exact duality between the stable full rate and coercivity. -/
theorem fullRate_eq_one_sub_fullCoercivity :
    S.fullRate = 1 - S.fullCoercivity := by
  unfold fullRate fullCoercivity z2WilsonTemporalCrossingCoercivity
  ring

/-- The spatial stability estimate directly supplies the repository's actual
full-transfer uniform centered Rayleigh certificate. -/
noncomputable def toUniformCenteredRayleighCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := S.fullRate
  rate_pos := S.fullRate_pos
  rate_lt_one := S.fullRate_lt_one
  centeredRayleigh := by
    intro H x hx
    exact S.fullCenteredRayleigh H x hx

/-- The generated actual centered Poincare certificate has exactly the
remaining coercivity `crossingCoercivity - degradation`. -/
noncomputable def toUniformCenteredPoincareCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  S.toUniformCenteredRayleighCertificate.toCenteredPoincareCertificate

@[simp] theorem toUniformCenteredRayleighCertificate_rate :
    S.toUniformCenteredRayleighCertificate.rate = S.fullRate :=
  rfl

@[simp] theorem toUniformCenteredPoincareCertificate_coercivity :
    S.toUniformCenteredPoincareCertificate.coercivity = S.fullCoercivity := by
  change 1 - S.fullRate = S.fullCoercivity
  rw [S.fullRate_eq_one_sub_fullCoercivity]
  ring

/-- The stability certificate therefore generates the complete actual
full-transfer uniform-gap package already established by the spectral layer. -/
noncomputable def toUniformCenteredPoincareCompletePackage :
    Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  finiteEvenFourTorusZ2UnfixedGaugeStrictCouplingUniformCenteredPoincareCompletePackage
    β energyIdentity energyNontrivial hβ hEnergy
      S.toUniformCenteredPoincareCertificate

@[simp] theorem
    toUniformCenteredPoincareCompletePackage_centeredPoincare_coercivity :
    S.toUniformCenteredPoincareCompletePackage.centeredPoincare.coercivity =
      S.fullCoercivity := by
  unfold toUniformCenteredPoincareCompletePackage
  rw [finiteEvenFourTorusZ2UnfixedGaugeStrictCouplingUniformCenteredPoincareCompletePackage_coercivity_eq]
  exact S.toUniformCenteredPoincareCertificate_coercivity

@[simp] theorem
    toUniformCenteredPoincareCompletePackage_centeredRayleigh_rate :
    S.toUniformCenteredPoincareCompletePackage.centeredRayleigh.rate =
      S.fullRate := by
  calc
    S.toUniformCenteredPoincareCompletePackage.centeredRayleigh.rate =
        1 - S.toUniformCenteredPoincareCompletePackage.centeredPoincare.coercivity :=
      S.toUniformCenteredPoincareCompletePackage.rate_eq_one_sub_coercivity
    _ = 1 - S.fullCoercivity := by
      rw [S.toUniformCenteredPoincareCompletePackage_centeredPoincare_coercivity]
    _ = S.fullRate := S.fullRate_eq_one_sub_fullCoercivity.symm

end Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate

/-- Complete receipt for the exact spatial sandwich factorization, its global
finite-volume envelopes, and a supplied local uniform stability estimate that
closes the actual full-transfer gap. -/
structure Z2FiniteEvenFourTorusSpatialSandwichStabilityCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  stability :
    Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy
  uniformFullTransfer :
    Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy
  uniformFullTransfer_rate_eq :
    uniformFullTransfer.centeredRayleigh.rate = stability.fullRate
  uniformFullTransfer_coercivity_eq :
    uniformFullTransfer.centeredPoincare.coercivity = stability.fullCoercivity
  uniformFullTransfer_coercivity_pos :
    0 < uniformFullTransfer.centeredPoincare.coercivity
  rawSpatialSandwich :
    ∀ H : ℕ,
      finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le =
        (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
          H β energyIdentity energyNontrivial).comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
              H β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel).comp
            (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
              H β energyIdentity energyNontrivial))
  halfWeightEnvelopes :
    ∀ (H : ℕ) (A : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2SpatialHalfWeightLowerBound
          H β energyNontrivial ≤
        finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial A ∧
      finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial A ≤
        finiteEvenFourTorusZ2SpatialHalfWeightUpperBound
          H β energyIdentity
  globalOscillationFormula :
    ∀ H : ℕ,
      finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio
          H β energyIdentity energyNontrivial =
        Real.exp
          ((β / 2) * finiteEvenFourTorusSpatialPlaquetteCountReal H *
            (energyNontrivial - energyIdentity))

/-- Construct the complete spatial-sandwich stability package from the single
remaining local uniform degradation certificate. -/
noncomputable def finiteEvenFourTorusZ2SpatialSandwichStabilityCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (S : Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2FiniteEvenFourTorusSpatialSandwichStabilityCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  { stability := S
    uniformFullTransfer := S.toUniformCenteredPoincareCompletePackage
    uniformFullTransfer_rate_eq :=
      S.toUniformCenteredPoincareCompletePackage_centeredRayleigh_rate
    uniformFullTransfer_coercivity_eq :=
      S.toUniformCenteredPoincareCompletePackage_centeredPoincare_coercivity
    uniformFullTransfer_coercivity_pos := by
      rw [S.toUniformCenteredPoincareCompletePackage_centeredPoincare_coercivity]
      exact S.fullCoercivity_pos
    rawSpatialSandwich := fun H =>
      finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_eq_spatialSandwich
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    halfWeightEnvelopes := fun H A =>
      ⟨finiteEvenFourTorusZ2SpatialHalfWeightLowerBound_le
          H β energyIdentity energyNontrivial hβ.le hEnergy.le A,
        finiteEvenFourTorusZ2SpatialHalfWeight_le_UpperBound
          H β energyIdentity energyNontrivial hβ.le hEnergy.le A⟩
    globalOscillationFormula := fun H =>
      finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio_eq_exp
        H β energyIdentity energyNontrivial }

end

end MathlibAnalytic
end MGAP4D
