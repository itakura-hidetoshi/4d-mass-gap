import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaussProjectedOneSlabNontriviality

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exact formal claim boundary of the Gauss-projected temporal-gauge one-slab
package.  The first component records the general finite-volume compressed
transfer structure; the second records explicit nonidentity on a
plaquette-separated gauge-invariant sector.  Unfixed temporal-link averaging,
compact `SU(2)` Haar integration, Hamiltonian logarithms, uniform gaps,
continuum limits, and physical mass-gap claims remain outside this layer. -/
def finiteEvenFourTorusZ2GaussProjectedOneSlabClaimBoundary :
    Prop :=
  (∀ H : ℕ,
    ∀ β energyIdentity energyNontrivial : ℝ,
    ∀ hβ : 0 ≤ β,
    ∀ hEnergy : energyIdentity ≤ energyNontrivial,
      ((finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric) ∧
      (∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
        0 ≤ inner ℝ
          (finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f) f) ∧
      (∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
        ‖finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖) ∧
      (∀ m n : ℕ,
        finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
          (finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy m).comp
          (finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
            H β energyIdentity energyNontrivial hβ hEnergy n))) ∧
  (∀ β energyIdentity energyNontrivial : ℝ,
    ∀ hβ : 0 ≤ β,
    ∀ hEnergy : energyIdentity ≤ energyNontrivial,
      finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy ≠ 1)

/-- The present package reaches a nontrivial gauge-invariant finite boundary
transfer without asserting any downstream compact-group, Hamiltonian,
continuum, or physical mass-gap theorem. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabClaimBoundary_ready :
    finiteEvenFourTorusZ2GaussProjectedOneSlabClaimBoundary := by
  constructor
  · intro H β energyIdentity energyNontrivial hβ hEnergy
    exact ⟨
      finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_isSymmetric
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_quadratic_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_norm_apply_le
        H β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2GaussProjectedTransferSemigroup_add
        H β energyIdentity energyNontrivial hβ hEnergy⟩
  · exact finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_ne_identity

end

end MathlibAnalytic
end MGAP4D
