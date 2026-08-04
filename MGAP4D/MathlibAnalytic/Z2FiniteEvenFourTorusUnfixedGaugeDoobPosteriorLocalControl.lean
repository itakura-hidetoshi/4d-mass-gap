import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelGroundStateDoobJointMeasure
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronLocalRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Replacing one coordinate and then restoring its original value returns the
original finite `Z₂` configuration. -/
theorem finiteZ2GaugeReplaceCoordinate_restore
    {ι : Type}
    [DecidableEq ι]
    (B : ι → Z2Gauge)
    (e : ι)
    (g : Z2Gauge) :
    finiteZ2GaugeReplaceCoordinate
        (finiteZ2GaugeReplaceCoordinate B e g) e (B e) = B := by
  funext i
  by_cases hie : i = e
  · subst i
    simp
  · simp [finiteZ2GaugeReplaceCoordinate, hie]

/-- Exact actual Perron-Doob posterior formula.  Operator-norm normalization
cancels, leaving the raw one-slab kernel weighted by the actual positive Perron
ground and normalized by its column mass. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_eq_posterior
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B =
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H β energyIdentity energyNontrivial hβ hEnergy A B *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy A) /
        (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H β energyIdentity energyNontrivial hβ hEnergy X B *
            finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
              H β energyIdentity energyNontrivial hβ hEnergy X) := by
  simpa [finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel,
    FiniteKernelGroundStateDoobData.groundWeightedColumnMass] using
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ hEnergy).doobKernel_eq_groundPosterior A B

/-- Actual symmetric two-boundary joint weight whose conditional transition is
the Perron Doob kernel. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).jointWeight A B

/-- The actual two-boundary joint weight is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight
      H β energyIdentity energyNontrivial hβ hEnergy A B :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).jointWeight_nonneg A B

/-- The actual two-boundary joint weight is symmetric. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight_symmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight
        H β energyIdentity energyNontrivial hβ hEnergy A B =
      finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight
        H β energyIdentity energyNontrivial hβ hEnergy B A :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).jointWeight_symmetric A B

/-- Both joint marginals are the actual reversible Perron density `p²`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight_rightMarginal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight
          H β energyIdentity energyNontrivial hβ hEnergy A B =
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy B) ^ 2 :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).jointWeight_rightMarginal B

/-- Exact actual two-layer Dirichlet-form identity. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_weightedDirichlet_eq_jointDifference
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).weightedNormSq f -
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).weightedDoobQuadratic f =
      (2 : ℝ)⁻¹ *
        ∑ B : FiniteEvenFourTorusZ2SliceConfiguration H,
          ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeDoobJointWeight
                H β energyIdentity energyNontrivial hβ hEnergy A B *
              (f A - f B) ^ 2 :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).
      weightedNormSq_sub_weightedDoobQuadratic_eq_jointDifference f

/-- The previously proved Perron local ratio also holds in the reverse
direction after restoring the original link value. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_replace_le_singleLinkRatio_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (finiteZ2GaugeReplaceCoordinate B e g) ≤
      z2UnfixedGaugePerronSingleLinkRatio
          β energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ.le hEnergy.le B := by
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_le_singleLinkRatio_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteZ2GaugeReplaceCoordinate B e g) e (B e)
  simpa [finiteZ2GaugeReplaceCoordinate_restore] using h

/-- Reversible Perron density of the actual Doob chain. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronDensity
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ hEnergy B) ^ 2

/-- The reversible density has the explicit squared local ratio. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronDensity_le_sqRatio_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugePerronDensity
        H β energyIdentity energyNontrivial hβ.le hEnergy.le B ≤
      (z2UnfixedGaugePerronSingleLinkRatio
          β energyIdentity energyNontrivial) ^ 2 *
        finiteEvenFourTorusZ2UnfixedGaugePerronDensity
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  let R := z2UnfixedGaugePerronSingleLinkRatio
    β energyIdentity energyNontrivial
  let p := finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  let B' := finiteZ2GaugeReplaceCoordinate B e g
  have hLocal : p B ≤ R * p B' := by
    simpa [p, R, B'] using
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_le_singleLinkRatio_mul_replace
        H β energyIdentity energyNontrivial hβ hEnergy B e g
  have hp0 : 0 ≤ p B :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le B)
  have hp'0 : 0 ≤ p B' :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le B')
  have hR0 : 0 ≤ R :=
    le_of_lt (z2UnfixedGaugePerronSingleLinkRatio_pos hβ hEnergy)
  have hdiff : 0 ≤ R * p B' - p B := sub_nonneg.mpr hLocal
  have hsum : 0 ≤ R * p B' + p B :=
    add_nonneg (mul_nonneg hR0 hp'0) hp0
  have hsq : (p B) ^ 2 ≤ R ^ 2 * (p B') ^ 2 := by
    have hprod := mul_nonneg hdiff hsum
    nlinarith
  simpa [finiteEvenFourTorusZ2UnfixedGaugePerronDensity, p, R, B'] using hsq

/-- The squared reversible-density ratio is two-sided. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronDensity_replace_le_sqRatio_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugePerronDensity
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (finiteZ2GaugeReplaceCoordinate B e g) ≤
      (z2UnfixedGaugePerronSingleLinkRatio
          β energyIdentity energyNontrivial) ^ 2 *
        finiteEvenFourTorusZ2UnfixedGaugePerronDensity
          H β energyIdentity energyNontrivial hβ.le hEnergy.le B := by
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugePerronDensity_le_sqRatio_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteZ2GaugeReplaceCoordinate B e g) e (B e)
  simpa [finiteZ2GaugeReplaceCoordinate_restore] using h

/-- Spatial half-weight times Perron ground, the message entering the crossing
smoother in the exact fixed-point equation. -/
def finiteEvenFourTorusZ2UnfixedGaugeSpatialPerronMessage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2SpatialHalfWeight
      H β energyIdentity energyNontrivial B *
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ hEnergy B

/-- Explicit one-link ratio for the actual spatial Perron message. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeSpatialPerronMessage_le_localRatio_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeSpatialPerronMessage
        H β energyIdentity energyNontrivial hβ.le hEnergy.le B ≤
      (Real.exp (6 * β * (energyNontrivial - energyIdentity)) *
        z2UnfixedGaugePerronSingleLinkRatio
          β energyIdentity energyNontrivial) *
        finiteEvenFourTorusZ2UnfixedGaugeSpatialPerronMessage
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  let E := Real.exp (6 * β * (energyNontrivial - energyIdentity))
  let R := z2UnfixedGaugePerronSingleLinkRatio
    β energyIdentity energyNontrivial
  let a := finiteEvenFourTorusZ2SpatialHalfWeight
    H β energyIdentity energyNontrivial
  let p := finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  let B' := finiteZ2GaugeReplaceCoordinate B e g
  have ha : a B ≤ E * a B' := by
    simpa [a, E, B'] using
      finiteEvenFourTorusZ2SpatialHalfWeight_le_exp_twelve_mul_replace
        H β energyIdentity energyNontrivial hβ.le hEnergy.le B e g
  have hp : p B ≤ R * p B' := by
    simpa [p, R, B'] using
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_le_singleLinkRatio_mul_replace
        H β energyIdentity energyNontrivial hβ hEnergy B e g
  have hp0 : 0 ≤ p B :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le B)
  have ha'0 : 0 ≤ a B' :=
    le_of_lt
      (finiteEvenFourTorusZ2SpatialHalfWeight_pos
        H β energyIdentity energyNontrivial B')
  have hE0 : 0 ≤ E := le_of_lt (Real.exp_pos _)
  calc
    a B * p B ≤ (E * a B') * p B :=
      mul_le_mul_of_nonneg_right ha hp0
    _ ≤ (E * a B') * (R * p B') :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hE0 ha'0)
    _ = (E * R) * (a B' * p B') := by ring

end

end MathlibAnalytic
end MGAP4D
