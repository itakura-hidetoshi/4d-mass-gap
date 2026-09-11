import MGAP4D.MathlibAnalytic.FiniteDimensionalGroundCoordinatesOrthogonality
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundStateDoobTransform
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialSandwichStabilityCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- The chosen ambient positive Perron ground, regarded as a vector in the
residual-Gauss-invariant slice Hilbert space. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeInvariantPositiveGround
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  ⟨finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2UnfixedGauge_fixedVector_mem_invariant
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
        H β energyIdentity energyNontrivial hβ hEnergy)⟩

/-- The chosen invariant Perron ground is fixed by the compressed actual
one-slab transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantPositiveGround_fixed
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy) =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy := by
  apply Subtype.ext
  exact finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
    H β energyIdentity energyNontrivial hβ hEnergy

/-- The repository's canonical zero-ground-coordinate condition is exactly
strong enough to imply orthogonality to the chosen positive Perron ground. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_inner_positiveGround_eq_zero_of_groundCoordinates_eq_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (hx : finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
      H β energyIdentity energyNontrivial hβ hEnergy x = 0) :
    inner ℝ x.1
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy) = 0 := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy
  have hxD : D.groundCoordinates x = 0 := by
    simpa [D, finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates] using hx
  have hpD :
      D.operator
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantPositiveGround
            H β energyIdentity energyNontrivial hβ hEnergy) =
        finiteEvenFourTorusZ2UnfixedGaugeInvariantPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy := by
    simpa [D, finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using
      finiteEvenFourTorusZ2UnfixedGaugeInvariantPositiveGround_fixed
        H β energyIdentity energyNontrivial hβ hEnergy
  have hOrth :=
    D.inner_fixed_eq_zero_of_groundCoordinates_eq_zero
      x
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy)
      hxD hpD
  exact hOrth

/-- A weighted mean-zero Rayleigh bound for the actual Perron Doob chain now
produces the exact `fullCenteredRayleigh` statement required by the spatial
sandwich stability certificate. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_fullCenteredRayleigh_of_weightedDoob
    (β energyIdentity energyNontrivial rate : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (hDoob : ∀ (H : ℕ) (f : FiniteEvenFourTorusZ2SliceHilbert H),
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedMean f = 0 →
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
            H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedDoobQuadratic f ≤
          rate *
            (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
              H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedNormSq f)
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (hx : finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
      H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0) :
    inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x ≤
      rate * ‖x‖ ^ 2 := by
  apply finiteEvenFourTorusZ2UnfixedGaugeInvariant_transfer_rayleigh_le_of_weightedDoob
    H β energyIdentity energyNontrivial rate hβ.le hEnergy.le (hDoob H) x
  exact
    finiteEvenFourTorusZ2UnfixedGauge_inner_positiveGround_eq_zero_of_groundCoordinates_eq_zero
      H β energyIdentity energyNontrivial hβ.le hEnergy.le x hx

/-- A proof-relevant all-volume weighted Doob estimate with degradation below
the crossing coercivity constructs the existing actual full-transfer spatial
sandwich stability certificate.  This is the exact operator bridge; the
remaining model-specific work is to derive `weightedDoobRayleigh` from local
high-temperature Wilson incidence estimates. -/
structure Z2UnfixedGaugeWeightedDoobUniformStabilityCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  degradation : ℝ
  degradation_nonneg : 0 ≤ degradation
  degradation_lt_crossingCoercivity :
    degradation < z2WilsonTemporalCrossingCoercivity
      β energyIdentity energyNontrivial
  weightedDoobRayleigh :
    ∀ (H : ℕ) (f : FiniteEvenFourTorusZ2SliceHilbert H),
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedMean f = 0 →
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
            H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedDoobQuadratic f ≤
          (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial + degradation) *
            (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
              H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedNormSq f

/-- Exact conversion of the reversible weighted-Doob estimate into the actual
spatial-sandwich full-transfer certificate. -/
noncomputable def
    Z2UnfixedGaugeWeightedDoobUniformStabilityCertificate.toSpatialSandwichCertificate
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (D : Z2UnfixedGaugeWeightedDoobUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  { degradation := D.degradation
    degradation_nonneg := D.degradation_nonneg
    degradation_lt_crossingCoercivity :=
      D.degradation_lt_crossingCoercivity
    fullCenteredRayleigh := fun H x hx =>
      finiteEvenFourTorusZ2UnfixedGauge_fullCenteredRayleigh_of_weightedDoob
        β energyIdentity energyNontrivial
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial + D.degradation)
        hβ hEnergy D.weightedDoobRayleigh H x hx }

end

end MathlibAnalytic
end MGAP4D
