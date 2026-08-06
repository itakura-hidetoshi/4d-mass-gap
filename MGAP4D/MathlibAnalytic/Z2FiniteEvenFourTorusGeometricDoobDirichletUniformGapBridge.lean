import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelGroundStateDoobJointMeasure
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundStateDoobTransform
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialSandwichStabilityCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- The exact reversible Dirichlet form of the actual finite-volume geometric
Perron--Doob one-slab chain.  It is written directly as the two-layer joint
expectation of the squared observable increment. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGeometricDoobDirichletForm
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) : ℝ :=
  let D := finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy
  (2 : ℝ)⁻¹ *
    ∑ y : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
        D.jointWeight x y * (f x - f y) ^ 2

/-- The geometric Doob Dirichlet form is exactly `weighted norm squared`
minus the reversible Doob quadratic form. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGeometricDoobDirichletForm_eq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeGeometricDoobDirichletForm
        H β energyIdentity energyNontrivial hβ hEnergy f =
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).weightedNormSq f -
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).weightedDoobQuadratic f := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy
  change
    (2 : ℝ)⁻¹ *
        ∑ y : FiniteEvenFourTorusZ2SliceConfiguration H,
          ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
            D.jointWeight x y * (f x - f y) ^ 2 =
      D.weightedNormSq f - D.weightedDoobQuadratic f
  exact (D.weightedNormSq_sub_weightedDoobQuadratic_eq_jointDifference f).symm

/-- The exact geometric two-layer joint weight has both marginals equal to the
square of the chosen positive Perron ground. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGeometricDoobJointMarginals
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (∀ y : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).jointWeight x y =
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy y) ^ 2) ∧
    (∀ x : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ y : FiniteEvenFourTorusZ2SliceConfiguration H,
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).jointWeight x y =
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy x) ^ 2) := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy
  exact ⟨D.jointWeight_rightMarginal, D.jointWeight_leftMarginal⟩

/-- A proof-relevant, volume-independent Poincare estimate for the actual
geometric Perron--Doob chain.  The centering condition is the repository's
canonical ground-coordinate condition after exact division by the Perron
ground; no random-scan or heat-bath time is introduced. -/
structure Z2UnfixedGaugeGeometricDoobUniformPoincareCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  coercivity : ℝ
  coercivity_pos : 0 < coercivity
  coercivity_lt_one : coercivity < 1
  centeredPoincare :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0 →
        coercivity *
            (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
              H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedNormSq
              ((finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
                H β energyIdentity energyNontrivial hβ.le hEnergy.le).unweight x.1) ≤
          finiteEvenFourTorusZ2UnfixedGaugeGeometricDoobDirichletForm
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            ((finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
              H β energyIdentity energyNontrivial hβ.le hEnergy.le).unweight x.1)

namespace Z2UnfixedGaugeGeometricDoobUniformPoincareCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2UnfixedGaugeGeometricDoobUniformPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- The full geometric one-slab Rayleigh rate generated by the Doob Poincare
constant. -/
def rate : ℝ := 1 - C.coercivity

/-- The generated geometric rate is positive. -/
theorem rate_pos : 0 < C.rate := by
  unfold rate
  linarith [C.coercivity_lt_one]

/-- The generated geometric rate is strictly below one. -/
theorem rate_lt_one : C.rate < 1 := by
  unfold rate
  linarith [C.coercivity_pos]

/-- The exact Doob Dirichlet estimate gives the actual full geometric
one-slab centered Rayleigh estimate, with rate `1 - coercivity`. -/
theorem fullCenteredRayleigh
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (hx : finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
      H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0) :
    inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x ≤
      C.rate * ‖x‖ ^ 2 := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  let f := D.unweight x.1
  have hPoincare := C.centeredPoincare H x hx
  rw [finiteEvenFourTorusZ2UnfixedGaugeGeometricDoobDirichletForm_eq]
    at hPoincare
  change
    C.coercivity * D.weightedNormSq f ≤
      D.weightedNormSq f - D.weightedDoobQuadratic f at hPoincare
  rw [D.weightedDoobQuadratic_eq_transfer_inner,
    D.weightedNormSq_eq_norm_sq, D.weightedVector_unweight] at hPoincare
  change
    C.coercivity * ‖x.1‖ ^ 2 ≤
      ‖x.1‖ ^ 2 -
        inner ℝ
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
            H β energyIdentity energyNontrivial hβ.le hEnergy.le x.1) x.1
    at hPoincare
  change inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le x.1) x.1 ≤
    C.rate * ‖x.1‖ ^ 2
  unfold rate
  nlinarith

/-- A nonnegative degradation relative to the explicit crossing-only rate.
If the Doob Poincare rate is already sharper, the degradation is exactly zero. -/
def degradation : ℝ :=
  max 0
    (C.rate - z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)

/-- The selected degradation is nonnegative. -/
theorem degradation_nonneg : 0 ≤ C.degradation := by
  unfold degradation
  exact le_max_left _ _

/-- The actual Doob rate is bounded by crossing rate plus the selected
nonnegative degradation. -/
theorem rate_le_crossingRate_add_degradation :
    C.rate ≤
      z2WilsonTemporalCrossingRate β energyIdentity energyNontrivial +
        C.degradation := by
  unfold degradation
  have hMax :
      C.rate - z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial ≤
        max 0
          (C.rate - z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial) :=
    le_max_right _ _
  linarith

/-- Strict positivity of the Doob Poincare constant keeps the selected
spatial degradation strictly below the crossing coercivity. -/
theorem degradation_lt_crossingCoercivity :
    C.degradation <
      z2WilsonTemporalCrossingCoercivity
        β energyIdentity energyNontrivial := by
  unfold degradation z2WilsonTemporalCrossingCoercivity
  rw [max_lt_iff]
  constructor
  · linarith [z2WilsonTemporalCrossingRate_lt_one hβ hEnergy]
  · linarith [C.rate_lt_one]

/-- The exact geometric Doob Poincare certificate constructs the repository's
spatial-sandwich stability certificate without changing the full-transfer
rate, physical assumptions, or time interpretation. -/
noncomputable def toSpatialSandwichUniformStabilityCertificate :
    Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  degradation := C.degradation
  degradation_nonneg := C.degradation_nonneg
  degradation_lt_crossingCoercivity :=
    C.degradation_lt_crossingCoercivity
  fullCenteredRayleigh := by
    intro H x hx
    exact (C.fullCenteredRayleigh H x hx).trans
      (mul_le_mul_of_nonneg_right
        C.rate_le_crossingRate_add_degradation (sq_nonneg ‖x‖))

/-- Consequently the certificate constructs the complete actual full-transfer
uniform centered Poincare and spectral-gap package. -/
noncomputable def toSpatialSandwichStabilityCompletePackage :
    Z2FiniteEvenFourTorusSpatialSandwichStabilityCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  finiteEvenFourTorusZ2SpatialSandwichStabilityCompletePackage
    β energyIdentity energyNontrivial hβ hEnergy
    C.toSpatialSandwichUniformStabilityCertificate

/-- The resulting full-transfer coercivity is strictly positive. -/
theorem fullTransfer_coercivity_pos :
    0 <
      C.toSpatialSandwichStabilityCompletePackage.uniformFullTransfer
        .centeredPoincare.coercivity := by
  exact
    C.toSpatialSandwichStabilityCompletePackage
      .uniformFullTransfer_coercivity_pos

/-- The exact common positive full-transfer energy floor generated by the
Doob Poincare estimate. -/
noncomputable def fullTransferEnergyFloor : ℝ :=
  C.toSpatialSandwichStabilityCompletePackage.uniformFullTransfer
    .uniformGapPackage.uniformGap

/-- The generated full-transfer energy floor is strictly positive. -/
theorem fullTransferEnergyFloor_pos : 0 < C.fullTransferEnergyFloor := by
  exact
    C.toSpatialSandwichStabilityCompletePackage.uniformFullTransfer
      .uniformGap_pos

end Z2UnfixedGaugeGeometricDoobUniformPoincareCertificate

/-- Terminal constructor: one actual volume-independent geometric Doob
Dirichlet--Poincare estimate closes the full finite-volume geometric `Z₂`
one-slab uniform gap throughout the same strict-coupling regime. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirichletUniformGapBridge
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (C : Z2UnfixedGaugeGeometricDoobUniformPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2FiniteEvenFourTorusSpatialSandwichStabilityCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  C.toSpatialSandwichStabilityCompletePackage

end

end MathlibAnalytic
end MGAP4D
