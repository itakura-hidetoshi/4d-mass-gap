import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricPositiveContractionGroundLiftedDefect
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectUniformGap
import MGAP4D.MathlibAnalytic.RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
open scoped InnerProduct

noncomputable section

/-- The full-space ground-lifted defect attached to the actual finite-volume
geometric Perron--Doob transfer.  It is the identity on the transfer ground
sector and agrees modewise with `I - T_H` on every non-ground mode. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefect

/-- The actual finite-volume ground-lifted defect is symmetric. -/
theorem finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric := by
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy).groundLiftedDefect_isSymmetric

/-- The direct geometric Doob response theorem gives an all-vector common
quadratic lower bound `1/2` after lifting the ground sector. -/
theorem finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_half_coercive
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤
      inner ℝ
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  have hExcited : ∀ i : D.ExcitedSpectralIndex,
      D.eigenvalue i.1 ≤ 1 - (1 / 2 : ℝ) := by
    intro i
    have h :=
      (finiteEvenFourTorusZ2GeometricDoobDirectUniformSpectralCap
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff).excitedEigenvalue_le_rate
        H i
    norm_num at h ⊢
    exact h
  exact
    D.groundLiftedDefect_quadratic_lower_bound_of_excited_cap
      (1 / 2 : ℝ) (by norm_num) hExcited x

/-- Model-facing convergence data for transporting the completed finite `Z₂`
geometric gap to a common real Hilbert carrier.

Only approximation, isometric embedding, and strong convergence data remain as
inputs.  The local operator, its symmetry, and its exact common coercivity
`1/2` are generated from the actual finite-volume geometric Doob theorem. -/
structure Z2GeometricDoobGroundLiftedStrongLimitInput
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (l : Filter ℕ) where
  approximate : ∀ H : ℕ,
    E →L[ℝ] FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H
  embed : ∀ H : ℕ,
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ] E
  embed_norm : ∀ (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
    ‖embed H x‖ = ‖x‖
  embed_inner : ∀ (H : ℕ)
    (x y : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
    inner ℝ (embed H x) (embed H y) = inner ℝ x y
  limitOperator : E →L[ℝ] E
  approximate_tendsto : ∀ f : E,
    Tendsto (fun H => embed H (approximate H f)) l (𝓝 f)
  evolved_tendsto : ∀ f : E,
    Tendsto
      (fun H =>
        embed H
          (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            (approximate H f)))
      l
      (𝓝 (limitOperator f))

namespace Z2GeometricDoobGroundLiftedStrongLimitInput

variable
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    {β : ℝ}
    {hβ : 0 < β}
    {hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ℕ}
    (I : Z2GeometricDoobGroundLiftedStrongLimitInput
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff E l)

/-- The model-facing convergence input canonically generates the repository's
varying-Hilbert uniform-coercive strong-limit data, with exact gap `1/2`. -/
noncomputable def toAsymptoticallyEmbeddedStrongLimitData :
    RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
      ℕ (fun H => FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) E l where
  localOperator := fun H =>
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  approximate := I.approximate
  embed := I.embed
  embed_norm := I.embed_norm
  embed_inner := I.embed_inner
  limitOperator := I.limitOperator
  gap := 1 / 2
  gap_pos := by norm_num
  local_gap := by
    intro H x
    exact finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_half_coercive
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H x
  local_symmetric := by
    intro H
    exact finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_isSymmetric
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  approximate_tendsto := I.approximate_tendsto
  evolved_tendsto := I.evolved_tendsto

@[simp] theorem toAsymptoticallyEmbeddedStrongLimitData_gap :
    I.toAsymptoticallyEmbeddedStrongLimitData.gap = (1 / 2 : ℝ) :=
  rfl

/-- The exact finite-volume coercivity survives on the supplied common carrier. -/
theorem limit_half_coercive
    [Filter.NeBot l]
    (f : E) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤ inner ℝ (I.limitOperator f) f := by
  exact realHilbert_asymptoticallyEmbedded_limit_gap
    I.toAsymptoticallyEmbeddedStrongLimitData f

/-- The common-carrier limit operator is symmetric. -/
theorem limit_isSymmetric
    [Filter.NeBot l] :
    I.limitOperator.toLinearMap.IsSymmetric := by
  exact realHilbert_asymptoticallyEmbedded_limit_symmetric
    I.toAsymptoticallyEmbeddedStrongLimitData

/-- On a complete common carrier, the limiting real spectrum remains above
`1/2`. -/
theorem limit_spectrum_subset_Ici_half
    [CompleteSpace E]
    [Filter.NeBot l] :
    spectrum ℝ I.limitOperator ⊆ Set.Ici (1 / 2 : ℝ) := by
  exact realHilbert_asymptoticallyEmbedded_limit_spectrum_subset_Ici
    I.toAsymptoticallyEmbeddedStrongLimitData

/-- Every real parameter below the exact inherited gap belongs to the limit
resolvent set, with the canonical reciprocal-distance norm bound. -/
theorem limit_resolvent_package
    [CompleteSpace E]
    [Filter.NeBot l]
    {lambda : ℝ}
    (hlambda : lambda < I.toAsymptoticallyEmbeddedStrongLimitData.gap) :
    lambda ∈ resolventSet ℝ I.limitOperator ∧
      ‖I.toAsymptoticallyEmbeddedStrongLimitData.toLimitStrongLimitData.limitResolvent
          hlambda‖ ≤
        (I.toAsymptoticallyEmbeddedStrongLimitData.gap - lambda)⁻¹ := by
  exact realHilbert_asymptoticallyEmbedded_limit_resolvent_package
    I.toAsymptoticallyEmbeddedStrongLimitData hlambda

end Z2GeometricDoobGroundLiftedStrongLimitInput

end

end MathlibAnalytic
end MGAP4D
