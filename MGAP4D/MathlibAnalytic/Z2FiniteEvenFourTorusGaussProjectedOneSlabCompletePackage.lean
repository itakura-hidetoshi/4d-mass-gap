import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaussProjectedOneSlabTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exact formal claim boundary of the Gauss-projected temporal-gauge one-slab
package.  The first component records what is constructed; the remaining
components explicitly keep unfixed temporal-link averaging, compact `SU(2)`
Haar integration, Hamiltonian logarithms, and continuum mass-gap claims
outside this layer. -/
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
          H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖)) ∧
  True

/-- The present package reaches the gauge-invariant finite boundary transfer
without asserting any downstream compact-group, Hamiltonian, continuum, or
physical mass-gap theorem. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabClaimBoundary_ready :
    finiteEvenFourTorusZ2GaussProjectedOneSlabClaimBoundary := by
  refine ⟨?_, trivial⟩
  intro H β energyIdentity energyNontrivial hβ hEnergy
  exact ⟨
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_isSymmetric
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_quadratic_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_norm_apply_le
      H β energyIdentity energyNontrivial hβ hEnergy⟩

end

end MathlibAnalytic
end MGAP4D
