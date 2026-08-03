import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabNontriviality

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Exact formal claim boundary of the finite temporal-link averaged unfixed
`Z₂` one-slab transfer package.  It records the equality with finite residual
gauge averaging of the temporal-gauge kernel, the two exact raw-operator
factorizations through the Gauss projector, symmetric positive contraction and
natural-time semigroup structure on both the ambient boundary Hilbert space and
the Gauss-invariant subspace, and explicit nonidentity on the side-two
plaquette-separated orbit sector.

Compact `SU(2)` Haar integration, Hamiltonian logarithms, transfer spectral
gaps, finite-volume uniform gaps, continuum limits, Wightman/OS final
identification, and physical Yang--Mills mass-gap claims remain outside this
layer. -/
def finiteEvenFourTorusZ2UnfixedGaugeOneSlabClaimBoundary : Prop :=
  (∀ H : ℕ,
    ∀ β energyIdentity energyNontrivial : ℝ,
    ∀ hβ : 0 ≤ β,
    ∀ hEnergy : energyIdentity ≤ energyNontrivial,
      (∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            H β energyIdentity energyNontrivial hβ hEnergy A B =
          finiteGroupRightAveragedKernel
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
              H β energyIdentity energyNontrivial hβ hEnergy).kernel A B) ∧
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy =
        (finiteEvenFourTorusZ2GaussProjector H).comp
          (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy)) ∧
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy =
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy).comp
          (finiteEvenFourTorusZ2GaussProjector H)) ∧
      ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric) ∧
      (∀ f : FiniteEvenFourTorusZ2SliceHilbert H,
        0 ≤ inner ℝ
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f) f) ∧
      (∀ f : FiniteEvenFourTorusZ2SliceHilbert H,
        ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖) ∧
      (∀ m n : ℕ,
        finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
          (finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy m).comp
          (finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy n)) ∧
      ((finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric) ∧
      (∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
        0 ≤ inner ℝ
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f) f) ∧
      (∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
        ‖finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖) ∧
      (∀ m n : ℕ,
        finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy m).comp
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy n))) ∧
  (∀ β energyIdentity energyNontrivial : ℝ,
    ∀ hβ : 0 ≤ β,
    ∀ hEnergy : energyIdentity ≤ energyNontrivial,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy ≠ 1)

/-- The finite temporal-link sum closes the actual unfixed-gauge one-slab
transfer layer without asserting any downstream compact-group, Hamiltonian,
spectral-gap, continuum, or physical mass-gap theorem. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabClaimBoundary_ready :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabClaimBoundary := by
  constructor
  · intro H β energyIdentity energyNontrivial hβ hEnergy
    exact ⟨
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_eq_Gauss_comp_temporal
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_eq_temporal_comp_Gauss
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_isSymmetric
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_quadratic_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_norm_apply_le
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup_add
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_isSymmetric
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_quadratic_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_apply_le
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup_add
        H β energyIdentity energyNontrivial hβ hEnergy⟩
  · exact finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_ne_identity

end

end MathlibAnalytic
end MGAP4D
