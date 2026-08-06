import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2OrthonormalCoordinates
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobGroundLiftedStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- The constant-one boundary vector is an actual Gauss-invariant state.  It
provides a concrete witness that every finite `Z₂` Gauss-invariant carrier is
nontrivial. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantConstantOne
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  ⟨WithLp.toLp 2
      (fun _A : FiniteEvenFourTorusZ2SliceConfiguration H => (1 : ℝ)),
    by
      intro _g _A
      rfl⟩

/-- The constant-one Gauss-invariant state is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantConstantOne_ne_zero
    (H : ℕ) :
    finiteEvenFourTorusZ2GaugeInvariantConstantOne H ≠ 0 := by
  intro hzero
  have hvalue := congrArg
    (fun f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H =>
      f.1 (finiteEvenFourTorusZ2IdentitySlice H)) hzero
  norm_num [finiteEvenFourTorusZ2GaugeInvariantConstantOne] at hvalue

/-- Every actual finite Gauss-invariant carrier has positive spectral
dimension. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
      H β energyIdentity energyNontrivial hβ hEnergy := by
  letI : Nontrivial
      (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :=
    ⟨⟨finiteEvenFourTorusZ2GaugeInvariantConstantOne H,
      0,
      finiteEvenFourTorusZ2GaugeInvariantConstantOne_ne_zero H⟩⟩
  change 0 < Module.finrank ℝ
    (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
  exact Module.finrank_pos

/-- Uniform strict probability on the canonical actual transfer spectral
indices.  This is a genuine probability because the Gauss-invariant carrier
has positive dimension. -/
noncomputable def finiteEvenFourTorusZ2SpectralProbabilityL2Data
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteStrictProbabilityL2Data
      (Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
        H β energyIdentity energyNontrivial hβ hEnergy)) := by
  letI : Nonempty
      (Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
        H β energyIdentity energyNontrivial hβ hEnergy)) :=
    ⟨⟨0,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension_pos
        H β energyIdentity energyNontrivial hβ hEnergy⟩⟩
  exact finiteUniformProbabilityL2Data _

/-- Concrete finite probability `L²` square-root coordinate carrier for the
actual Gauss-invariant transfer. -/
abbrev FiniteEvenFourTorusZ2SpectralProbabilityL2
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2SpectralProbabilityL2Data
    H β energyIdentity energyNontrivial hβ hEnergy).Carrier

/-- Canonical isometric identification of the actual finite Gauss-invariant
Hilbert carrier with its uniform spectral probability `L²` coordinates. -/
noncomputable def finiteEvenFourTorusZ2SpectralProbabilityL2Identification
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    RealHilbertLinearIsometricIdentification
      (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
      (FiniteEvenFourTorusZ2SpectralProbabilityL2
        H β energyIdentity energyNontrivial hβ hEnergy) :=
  orthonormalBasisProbabilityL2Identification
    (finiteEvenFourTorusZ2SpectralProbabilityL2Data
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenbasis
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The actual ground-lifted defect in explicit finite probability coordinates:
pointwise multiplication by the canonical lifted-defect coefficient. -/
noncomputable def finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2SpectralProbabilityL2
        H β energyIdentity energyNontrivial hβ hEnergy →L[ℝ]
      FiniteEvenFourTorusZ2SpectralProbabilityL2
        H β energyIdentity energyNontrivial hβ hEnergy :=
  finiteProbabilityCoordinateMultiplicationOperator
    (finiteEvenFourTorusZ2SpectralProbabilityL2Data
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefectCoefficient

@[simp] theorem finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2SpectralProbabilityL2
      H β energyIdentity energyNontrivial hβ hEnergy)
    (i : Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
      H β energyIdentity energyNontrivial hβ hEnergy)) :
    finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy x i =
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefectCoefficient i *
        x i :=
  rfl

/-- The actual finite ground-lifted defect is exactly conjugate to the explicit
pointwise spectral probability operator. -/
theorem finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_eq_transport
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2SpectralProbabilityL2Identification
      H β energyIdentity energyNontrivial hβ hEnergy).transportOperator
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy) =
      finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy := by
  change
    (orthonormalBasisProbabilityL2Identification
      (finiteEvenFourTorusZ2SpectralProbabilityL2Data
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).eigenbasis).transportOperator
        ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefect) =
      finiteProbabilityCoordinateMultiplicationOperator
        (finiteEvenFourTorusZ2SpectralProbabilityL2Data
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefectCoefficient
  exact
    orthonormalBasisProbabilityL2Identification_transport_diagonal
      (finiteEvenFourTorusZ2SpectralProbabilityL2Data
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).eigenbasis
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefectCoefficient

/-- Exact actual-carrier to spectral-probability intertwining. -/
theorem finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_intertwines
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2SpectralProbabilityL2Identification
          H β energyIdentity energyNontrivial hβ hEnergy).forward x) =
      (finiteEvenFourTorusZ2SpectralProbabilityL2Identification
        H β energyIdentity energyNontrivial hβ hEnergy).forward
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy x) := by
  rw [← finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_eq_transport]
  exact
    (finiteEvenFourTorusZ2SpectralProbabilityL2Identification
      H β energyIdentity energyNontrivial hβ hEnergy).transportOperator_apply_forward
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy) x

/-- Exact diagonal quadratic-form formula in the finite probability carrier. -/
theorem finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_inner
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2SpectralProbabilityL2
      H β energyIdentity energyNontrivial hβ hEnergy) :
    inner ℝ
        (finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy x) x =
      ∑ i : Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
          H β energyIdentity energyNontrivial hβ hEnergy),
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefectCoefficient i *
          (x i) ^ 2 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  change
    x i *
        ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefectCoefficient i *
          x i) =
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefectCoefficient i *
        x i ^ 2
  ring

/-- Symmetry of the explicit finite probability coordinate defect. -/
theorem finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric := by
  rw [← finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_eq_transport]
  exact
    (finiteEvenFourTorusZ2SpectralProbabilityL2Identification
      H β energyIdentity energyNontrivial hβ hEnergy).transportOperator_isSymmetric
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_isSymmetric
          H β energyIdentity energyNontrivial hβ hEnergy)

/-- The exact actual finite-volume coercivity `1/2` holds on every vector of
the explicit spectral probability `L²` carrier. -/
theorem finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_half_coercive
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2SpectralProbabilityL2
      H β energyIdentity energyNontrivial hβ.le hEnergy.le) :
    (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤
      inner ℝ
        (finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x := by
  rw [← finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_eq_transport]
  exact
    (finiteEvenFourTorusZ2SpectralProbabilityL2Identification
      H β energyIdentity energyNontrivial hβ.le hEnergy.le).transportOperator_quadratic_lower_bound
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
        (1 / 2 : ℝ)
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_half_coercive
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
        x

/-- Audit-visible complete realization of the actual finite `Z₂`
ground-lifted defect on a strict finite probability `L²` carrier. -/
structure Z2FiniteEvenFourTorusSpectralProbabilityL2RealizationPackage
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
      (Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
        H β energyIdentity energyNontrivial hβ.le hEnergy.le))
  probability_eq_uniform :
    probability =
      finiteEvenFourTorusZ2SpectralProbabilityL2Data
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
  identification :
    RealHilbertLinearIsometricIdentification
      (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
      probability.Carrier
  coordinateDefect :
    probability.Carrier →L[ℝ] probability.Carrier
  exactIntertwining :
    ∀ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      coordinateDefect (identification.forward x) =
        identification.forward
          (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
            H β energyIdentity energyNontrivial hβ.le hEnergy.le x)
  symmetric : coordinateDefect.toLinearMap.IsSymmetric
  halfCoercive :
    ∀ x : probability.Carrier,
      (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤
        inner ℝ (coordinateDefect x) x

/-- Construct the complete actual finite-probability realization receipt. -/
noncomputable def z2FiniteEvenFourTorusSpectralProbabilityL2RealizationPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    Z2FiniteEvenFourTorusSpectralProbabilityL2RealizationPackage
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H where
  probability :=
    finiteEvenFourTorusZ2SpectralProbabilityL2Data
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  probability_eq_uniform := rfl
  identification :=
    finiteEvenFourTorusZ2SpectralProbabilityL2Identification
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  coordinateDefect :=
    finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  exactIntertwining :=
    finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_intertwines
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  symmetric :=
    finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_isSymmetric
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  halfCoercive :=
    finiteEvenFourTorusZ2SpectralProbabilityGroundLiftedDefect_half_coercive
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H

end

end MathlibAnalytic
end MGAP4D
