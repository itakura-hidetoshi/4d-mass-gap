import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobGroundLiftedStrongLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
open scoped InnerProduct

noncomputable section

/-- Complete theorem-generated strong-limit receipt for the actual finite
high-temperature `Z₂` geometric Perron--Doob gap.

The only model-facing member is `input`, which supplies approximation maps,
isometric embeddings, and their strong convergence to a common bounded limit
operator.  Every finite-volume coercivity and symmetry field, and every stated
limit consequence, is generated from the direct geometric Doob theorem with
exact inherited gap `1/2`. -/
structure Z2GeometricDoobGroundLiftedStrongLimitCompletePackage
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
    [CompleteSpace E]
    (l : Filter ℕ)
    [Filter.NeBot l] where
  input : Z2GeometricDoobGroundLiftedStrongLimitInput
    energyIdentity energyNontrivial hEnergy β hβ hβCutoff E l
  limit_half_coercive : ∀ f : E,
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤ inner ℝ (input.limitOperator f) f
  limit_symmetric : input.limitOperator.toLinearMap.IsSymmetric
  limit_spectrum_subset :
    spectrum ℝ input.limitOperator ⊆ Set.Ici (1 / 2 : ℝ)
  limit_resolvent_package :
    ∀ {lambda : ℝ}
      (hlambda : lambda < input.toAsymptoticallyEmbeddedStrongLimitData.gap),
      lambda ∈ resolventSet ℝ input.limitOperator ∧
        ‖input.toAsymptoticallyEmbeddedStrongLimitData.toLimitStrongLimitData.limitResolvent
            hlambda‖ ≤
          (input.toAsymptoticallyEmbeddedStrongLimitData.gap - lambda)⁻¹

/-- Construct the complete common-carrier limit package from only the supplied
approximation, embedding, and convergence data. -/
noncomputable def
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedStrongLimitCompletePackage
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
    [CompleteSpace E]
    (l : Filter ℕ)
    [Filter.NeBot l]
    (I : Z2GeometricDoobGroundLiftedStrongLimitInput
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff E l) :
    Z2GeometricDoobGroundLiftedStrongLimitCompletePackage
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff E l where
  input := I
  limit_half_coercive := I.limit_half_coercive
  limit_symmetric := I.limit_isSymmetric
  limit_spectrum_subset := I.limit_spectrum_subset_Ici_half
  limit_resolvent_package := I.limit_resolvent_package

namespace Z2GeometricDoobGroundLiftedStrongLimitCompletePackage

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
    [CompleteSpace E]
    {l : Filter ℕ}
    [Filter.NeBot l]
    (P : Z2GeometricDoobGroundLiftedStrongLimitCompletePackage
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff E l)

/-- The common coercive constant carried by the generated varying-space data is
exactly one half. -/
@[simp] theorem strongLimit_gap_eq_half :
    P.input.toAsymptoticallyEmbeddedStrongLimitData.gap = (1 / 2 : ℝ) :=
  rfl

/-- Zero belongs to the real resolvent set of the common-carrier limit. -/
theorem zero_mem_limit_resolventSet :
    (0 : ℝ) ∈ resolventSet ℝ P.input.limitOperator := by
  have hzero :
      (0 : ℝ) < P.input.toAsymptoticallyEmbeddedStrongLimitData.gap := by
    norm_num
  exact (P.limit_resolvent_package hzero).1

/-- The canonical inverse at zero has operator norm at most two. -/
theorem zero_limitResolvent_norm_le_two :
    ‖P.input.toAsymptoticallyEmbeddedStrongLimitData.toLimitStrongLimitData.limitResolvent
        (show (0 : ℝ) <
          P.input.toAsymptoticallyEmbeddedStrongLimitData.gap by norm_num)‖ ≤
      (2 : ℝ) := by
  have h := P.limit_resolvent_package
    (show (0 : ℝ) <
      P.input.toAsymptoticallyEmbeddedStrongLimitData.gap by norm_num)
  norm_num at h ⊢
  exact h.2

end Z2GeometricDoobGroundLiftedStrongLimitCompletePackage

end

end MathlibAnalytic
end MGAP4D
