import MGAP4D.MathlibAnalytic.FiniteGroupOrbitProbabilityL2Realization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusAllVolumeGaugeOrbitWitness
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobGroundLiftedStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Actual quotient of finite even-four-torus spatial boundary configurations
by residual slice gauge transformations. -/
abbrev FiniteEvenFourTorusZ2ResidualGaugeOrbit
    (H : ℕ) : Type :=
  FiniteGroupOrbitQuotient
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)

/-- Pushforward of the uniform finite boundary-configuration law to actual
residual gauge orbits. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
    (H : ℕ) :
    FiniteStrictProbabilityL2Data
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :=
  finiteGroupOrbitProbabilityL2Data
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)

/-- Square-root-density Hilbert carrier on the actual residual gauge-orbit
probability space. -/
abbrev FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
    (H : ℕ) : Type :=
  FiniteProbabilityL2Carrier
    (FiniteEvenFourTorusZ2ResidualGaugeOrbit H)

/-- The orbit weight is exactly the pushforward of uniform counting
probability on finite boundary configurations. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data_weight_eq_pushforward
    (H : ℕ)
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight q =
      ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
        if q =
            finiteGroupOrbitClass
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
              (FiniteEvenFourTorusZ2SliceConfiguration H) A then
          (Fintype.card
            (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
        else 0 :=
  finiteGroupOrbitProbabilityL2Data_weight_eq_pushforward
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H) q

/-- Canonical residual gauge orbit of the identity spatial slice. -/
def finiteEvenFourTorusZ2IdentityGaugeOrbit
    (H : ℕ) : FiniteEvenFourTorusZ2ResidualGaugeOrbit H :=
  finiteGroupOrbitClass
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2IdentitySlice H)

/-- Canonical residual gauge orbit of the all-volume one-link excitation. -/
def finiteEvenFourTorusZ2ExcitationGaugeOrbit
    (H : ℕ) : FiniteEvenFourTorusZ2ResidualGaugeOrbit H :=
  finiteGroupOrbitClass
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2SingleLinkExcitation H
      (finiteEvenFourTorusZ2AllVolumeWitnessLink H))

/-- The actual residual gauge-orbit quotient is nontrivial at every finite
side parameter. -/
theorem finiteEvenFourTorusZ2IdentityGaugeOrbit_ne_excitationGaugeOrbit
    (H : ℕ) :
    finiteEvenFourTorusZ2IdentityGaugeOrbit H ≠
      finiteEvenFourTorusZ2ExcitationGaugeOrbit H := by
  intro hOrbit
  rcases
      (finiteGroupOrbitClass_eq_iff
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2IdentitySlice H)
        (finiteEvenFourTorusZ2SingleLinkExcitation H
          (finiteEvenFourTorusZ2AllVolumeWitnessLink H))).mp hOrbit with
    ⟨g, hg⟩
  exact
    finiteEvenFourTorusZ2AllVolumeWitness_not_gauge_related H g hg

noncomputable instance finiteEvenFourTorusZ2ResidualGaugeOrbitNontrivial
    (H : ℕ) : Nontrivial (FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :=
  ⟨⟨finiteEvenFourTorusZ2IdentityGaugeOrbit H,
    finiteEvenFourTorusZ2ExcitationGaugeOrbit H,
    finiteEvenFourTorusZ2IdentityGaugeOrbit_ne_excitationGaugeOrbit H⟩⟩

/-- Canonical isometric identification of the actual Gauss-invariant finite
boundary Hilbert carrier with the actual residual gauge-orbit probability
`L²` carrier. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
    (H : ℕ) :
    RealHilbertLinearIsometricIdentification
      (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
      (FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :=
  finiteGroupInvariantOrbitProbabilityL2Identification
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)

@[simp] theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification_forward_apply
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f q =
      Real.sqrt
          (finiteGroupOrbitMass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) q) *
        f.1
          (finiteGroupOrbitRepresentative
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) q) :=
  rfl

@[simp] theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification_inverse_apply
    (H : ℕ)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).inverse y).1 A =
      y
          (finiteGroupOrbitClass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) A) /
        Real.sqrt
          (finiteGroupOrbitMass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteGroupOrbitClass
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
              (FiniteEvenFourTorusZ2SliceConfiguration H) A)) :=
  rfl

/-- Actual finite geometric Doob ground-lifted defect transported to the
configuration gauge-orbit probability `L²` carrier. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).transportOperator
    (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Exact actual-carrier to gauge-orbit-probability intertwining. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_intertwines
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f) =
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy f) :=
  (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).
    transportOperator_apply_forward
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy) f

/-- The transported gauge-orbit quadratic form is exactly the actual finite
Gauss-invariant quadratic form. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_inner
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    inner ℝ
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy y) y =
      inner ℝ
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).inverse y))
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).inverse y) := by
  let I := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H
  let A := finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
    H β energyIdentity energyNontrivial hβ hEnergy
  change inner ℝ (I.forward (A (I.inverse y))) y =
    inner ℝ (A (I.inverse y)) (I.inverse y)
  rw [← I.forward_inverse y]
  exact I.forward_inner _ _

/-- Symmetry of the actual defect on the configuration gauge-orbit carrier. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).
    transportOperator_isSymmetric
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_isSymmetric
        H β energyIdentity energyNontrivial hβ hEnergy)

/-- The exact finite-volume coercivity constant `1/2` holds on every vector of
the actual configuration gauge-orbit probability `L²` carrier. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_half_coercive
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤
      inner ℝ
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le y) y :=
  (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).
    transportOperator_quadratic_lower_bound
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      (1 / 2 : ℝ)
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_half_coercive
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
      y

/-- Audit-visible actual finite `Z₂` configuration gauge-orbit probability
realization and defect conjugacy package. -/
structure Z2FiniteEvenFourTorusGaugeOrbitProbabilityL2RealizationPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) where
  probability :
    FiniteStrictProbabilityL2Data
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
  probability_eq_pushforward :
    probability = finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H
  identityOrbit_ne_excitationOrbit :
    finiteEvenFourTorusZ2IdentityGaugeOrbit H ≠
      finiteEvenFourTorusZ2ExcitationGaugeOrbit H
  identification :
    RealHilbertLinearIsometricIdentification
      (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
      (FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H)
  identification_eq_canonical :
    identification =
      finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H
  orbitDefect :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  orbitDefect_eq_transport :
    orbitDefect =
      identification.transportOperator
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  exactIntertwining :
    ∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      orbitDefect (identification.forward f) =
        identification.forward
          (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
            H β energyIdentity energyNontrivial hβ.le hEnergy.le f)
  symmetric : orbitDefect.toLinearMap.IsSymmetric
  halfCoercive :
    ∀ y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H,
      (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤ inner ℝ (orbitDefect y) y

/-- Construct the complete actual gauge-orbit probability realization
package. -/
noncomputable def z2FiniteEvenFourTorusGaugeOrbitProbabilityL2RealizationPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    Z2FiniteEvenFourTorusGaugeOrbitProbabilityL2RealizationPackage
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H where
  probability := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H
  probability_eq_pushforward := rfl
  identityOrbit_ne_excitationOrbit :=
    finiteEvenFourTorusZ2IdentityGaugeOrbit_ne_excitationGaugeOrbit H
  identification :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H
  identification_eq_canonical := rfl
  orbitDefect :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  orbitDefect_eq_transport := rfl
  exactIntertwining :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_intertwines
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  symmetric :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_isSymmetric
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  halfCoercive :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_half_coercive
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H

end

end MathlibAnalytic
end MGAP4D