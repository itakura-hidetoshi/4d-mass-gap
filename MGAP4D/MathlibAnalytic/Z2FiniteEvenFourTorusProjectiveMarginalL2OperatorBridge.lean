import MGAP4D.MathlibAnalytic.RealHilbertLinearIsometricOperatorTransport
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitL2CompatibleOperatorExtension
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobGroundLiftedStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProduct

noncomputable section

/-- The actual finite Gauss-invariant `Z₂` transfer carrier is a proper
model-specific Hilbert subspace, while an arbitrary projective finite marginal
is a full measure-theoretic `L²` space.  This structure records the genuinely
missing finite-model identification and the exact realization of the actual
finite ground-lifted defect inside one compatible marginal operator system.

No canonical identification between finite `Z₂` and a compact `SU(N)`
Euclidean marginal is asserted here. -/
structure Z2FiniteEvenFourTorusProjectiveMarginalL2BridgeInput
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) where
  marginalIndex : ℕ → Finset EuclideanFourSpace
  carrierIdentification :
    ∀ H : ℕ,
      RealHilbertLinearIsometricIdentification
        (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
        (Lp ℝ 2 (F.finiteMarginal (marginalIndex H)))
  operatorSystem :
    EuclideanYangMillsProjectiveLimitL2OperatorSystem F L
  localOperator_eq_transportedGroundLiftedDefect :
    ∀ H : ℕ,
      operatorSystem.localOperator (marginalIndex H) =
        (carrierIdentification H).transportOperator
          (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
            H β energyIdentity energyNontrivial hβ.le hEnergy.le)

namespace Z2FiniteEvenFourTorusProjectiveMarginalL2BridgeInput

variable
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    {β : ℝ}
    {hβ : 0 < β}
    {hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (I : Z2FiniteEvenFourTorusProjectiveMarginalL2BridgeInput
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff F L)

/-- The actual finite ground-lifted defect transported canonically to the
selected finite marginal `L²` carrier. -/
noncomputable def transportedMarginalGroundLiftedDefect
    (H : ℕ) :
    Lp ℝ 2 (F.finiteMarginal (I.marginalIndex H)) →L[ℝ]
      Lp ℝ 2 (F.finiteMarginal (I.marginalIndex H)) :=
  (I.carrierIdentification H).transportOperator
    (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ.le hEnergy.le)

/-- The selected local operator of the compatible projective system is exactly
the transported actual finite `Z₂` ground-lifted defect. -/
theorem localOperator_eq_transportedMarginalGroundLiftedDefect
    (H : ℕ) :
    I.operatorSystem.localOperator (I.marginalIndex H) =
      I.transportedMarginalGroundLiftedDefect H :=
  I.localOperator_eq_transportedGroundLiftedDefect H

/-- Exact actual-carrier to finite-marginal intertwining. -/
theorem localOperator_intertwines_actualGroundLiftedDefect
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    I.operatorSystem.localOperator (I.marginalIndex H)
        ((I.carrierIdentification H).forward x) =
      (I.carrierIdentification H).forward
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x) := by
  rw [I.localOperator_eq_transportedMarginalGroundLiftedDefect H]
  exact
    (I.carrierIdentification H).transportOperator_apply_forward
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) x

/-- Symmetry of the actual finite defect survives on the selected marginal
`L²` carrier. -/
theorem localOperator_isSymmetric
    (H : ℕ) :
    (I.operatorSystem.localOperator
      (I.marginalIndex H)).toLinearMap.IsSymmetric := by
  rw [I.localOperator_eq_transportedMarginalGroundLiftedDefect H]
  exact
    (I.carrierIdentification H).transportOperator_isSymmetric
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_isSymmetric
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)

/-- The exact actual finite-volume coercivity `1/2` survives unchanged on the
selected finite marginal `L²` carrier. -/
theorem localOperator_half_coercive
    (H : ℕ)
    (f : Lp ℝ 2 (F.finiteMarginal (I.marginalIndex H))) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
      inner ℝ
        (I.operatorSystem.localOperator (I.marginalIndex H) f) f := by
  rw [I.localOperator_eq_transportedMarginalGroundLiftedDefect H]
  exact
    (I.carrierIdentification H).transportOperator_quadratic_lower_bound
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      (1 / 2 : ℝ)
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_half_coercive
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
      f

/-- Canonical embedding of the actual finite `Z₂` Hilbert carrier into the
common continuum projective-limit `L²` carrier, obtained by composing the
explicit finite identification with the canonical marginal pullback. -/
noncomputable def continuumEmbed
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (L.finiteMarginalL2Pullback
      (I.marginalIndex H)).toContinuousLinearMap.comp
    (I.carrierIdentification H).forward.toContinuousLinearMap

@[simp] theorem continuumEmbed_apply
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    I.continuumEmbed H x =
      L.finiteMarginalL2Pullback (I.marginalIndex H)
        ((I.carrierIdentification H).forward x) :=
  rfl

/-- The actual-to-continuum embedding is isometric. -/
@[simp] theorem continuumEmbed_norm
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖I.continuumEmbed H x‖ = ‖x‖ := by
  rw [I.continuumEmbed_apply,
    L.finiteMarginalL2Pullback_norm,
    (I.carrierIdentification H).forward.norm_map]

/-- The actual-to-continuum embedding preserves the real inner product. -/
@[simp] theorem continuumEmbed_inner
    (H : ℕ)
    (x y : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    inner ℝ (I.continuumEmbed H x) (I.continuumEmbed H y) =
      inner ℝ x y := by
  rw [I.continuumEmbed_apply, I.continuumEmbed_apply,
    L.finiteMarginalL2Pullback_inner,
    (I.carrierIdentification H).forward_inner]

/-- Exact actual finite `Z₂` to continuum intertwining.  The continuum
operator produced by the compatible marginal system acts on every embedded
actual carrier exactly as the actual ground-lifted defect. -/
theorem continuumOperator_intertwines_actualGroundLiftedDefect
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    L.finiteMarginalL2ContinuumOperator I.operatorSystem
        (I.continuumEmbed H x) =
      I.continuumEmbed H
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x) := by
  rw [I.continuumEmbed_apply, I.continuumEmbed_apply]
  rw [L.finiteMarginalL2ContinuumOperator_intertwines
    I.operatorSystem (I.marginalIndex H)
    ((I.carrierIdentification H).forward x)]
  rw [I.localOperator_intertwines_actualGroundLiftedDefect H x]

/-- The continuum quadratic form on every embedded actual finite carrier is
exactly the actual finite ground-lifted-defect quadratic form. -/
theorem continuumOperator_inner_embed_eq_actual
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    inner ℝ
        (L.finiteMarginalL2ContinuumOperator I.operatorSystem
          (I.continuumEmbed H x))
        (I.continuumEmbed H x) =
      inner ℝ
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x := by
  rw [I.continuumOperator_intertwines_actualGroundLiftedDefect H x]
  exact I.continuumEmbed_inner H _ _

/-- The exact finite coercivity `1/2` therefore holds on every actual finite
carrier after canonical embedding into the common continuum `L²` space. -/
theorem continuumOperator_half_coercive_on_actual_image
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (1 / 2 : ℝ) * ‖I.continuumEmbed H x‖ ^ 2 ≤
      inner ℝ
        (L.finiteMarginalL2ContinuumOperator I.operatorSystem
          (I.continuumEmbed H x))
        (I.continuumEmbed H x) := by
  rw [I.continuumEmbed_norm,
    I.continuumOperator_inner_embed_eq_actual]
  exact
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_half_coercive
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H x

end Z2FiniteEvenFourTorusProjectiveMarginalL2BridgeInput

/-- Audit-visible receipt for the complete conditional bridge from the actual
finite even-four-torus `Z₂` ground-lifted defect to selected finite projective
marginals and then to the common continuum projective-limit `L²` carrier. -/
structure Z2FiniteEvenFourTorusProjectiveMarginalL2OperatorBridgePackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) where
  input :
    Z2FiniteEvenFourTorusProjectiveMarginalL2BridgeInput
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff F L
  continuumEmbed :
    ∀ H : ℕ,
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
        Lp ℝ 2 L.continuumMeasure
  continuumEmbedNorm :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      ‖continuumEmbed H x‖ = ‖x‖
  selectedMarginalSymmetric :
    ∀ H : ℕ,
      (input.operatorSystem.localOperator
        (input.marginalIndex H)).toLinearMap.IsSymmetric
  selectedMarginalHalfCoercive :
    ∀ (H : ℕ)
      (f : Lp ℝ 2
        (F.finiteMarginal (input.marginalIndex H))),
      (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
        inner ℝ
          (input.operatorSystem.localOperator
            (input.marginalIndex H) f) f
  continuumIntertwining :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      L.finiteMarginalL2ContinuumOperator input.operatorSystem
          (continuumEmbed H x) =
        continuumEmbed H
          (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
            H β energyIdentity energyNontrivial hβ.le hEnergy.le x)
  continuumHalfCoerciveOnActualImage :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      (1 / 2 : ℝ) * ‖continuumEmbed H x‖ ^ 2 ≤
        inner ℝ
          (L.finiteMarginalL2ContinuumOperator input.operatorSystem
            (continuumEmbed H x))
          (continuumEmbed H x)

/-- Construct the complete bridge receipt from the explicit finite carrier
identifications and compatible marginal operator realization. -/
noncomputable def z2FiniteEvenFourTorusProjectiveMarginalL2OperatorBridgePackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (I : Z2FiniteEvenFourTorusProjectiveMarginalL2BridgeInput
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff F L) :
    Z2FiniteEvenFourTorusProjectiveMarginalL2OperatorBridgePackage
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff F L where
  input := I
  continuumEmbed := I.continuumEmbed
  continuumEmbedNorm := I.continuumEmbed_norm
  selectedMarginalSymmetric := I.localOperator_isSymmetric
  selectedMarginalHalfCoercive := I.localOperator_half_coercive
  continuumIntertwining :=
    I.continuumOperator_intertwines_actualGroundLiftedDefect
  continuumHalfCoerciveOnActualImage :=
    I.continuumOperator_half_coercive_on_actual_image

end

end MathlibAnalytic
end MGAP4D
