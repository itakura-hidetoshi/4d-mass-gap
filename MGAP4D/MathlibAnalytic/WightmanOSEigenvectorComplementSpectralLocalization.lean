import MGAP4D.MathlibAnalytic.WightmanOSAmbientEigenprojectionCanonicalLift

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Spectral localization at eigenvectors for a partially-defined real-linear
operator and a projection-valued set function: an eigenvector has no spectral
component outside the singleton containing its eigenvalue. -/
def OrthogonalProjectionValuedSetFunction.HasEigenvectorComplementAnnihilationLaw
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (T : H →ₗ.[ℝ] H) : Prop :=
  ∀ {E : ℝ} (x : T.domain), T x = E • (x : H) →
    P.projection (({E} : Set ℝ)ᶜ) (x : H) = 0

/-- Complement spectral localization implies the singleton eigenprojection law
using only the PVM normalization and finite disjoint additivity laws. -/
theorem OrthogonalProjectionValuedSetFunction.hasEigenprojectionLaw_of_complement
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : OrthogonalProjectionValuedSetFunction H}
    {T : H →ₗ.[ℝ] H}
    (hComplement : P.HasEigenvectorComplementAnnihilationLaw T) :
    P.HasEigenprojectionLaw T := by
  intro E x hEigen
  have hDisjoint : Disjoint ({E} : Set ℝ) (({E} : Set ℝ)ᶜ) := by
    simp
  have hDecomp := P.disjoint_additive
    ({E} : Set ℝ) (({E} : Set ℝ)ᶜ) hDisjoint (x : H)
  rw [Set.union_compl_self, P.univ_apply,
    hComplement x hEigen, add_zero] at hDecomp
  exact hDecomp.symm

/-- The ambient Hamiltonian has no spectral component away from an eigenvalue on
an eigenvector. This is a spectral-localization compatibility boundary weaker
than directly assuming that the singleton projection fixes the vector. -/
def ExplicitWightmanOSAmbientEigenvectorComplementAnnihilationLaw
    (M : ExplicitWightmanOSReconstructedModel) : Prop :=
  M.spectralPVM.HasEigenvectorComplementAnnihilationLaw M.hamiltonian

/-- Ambient complement spectral localization gives ambient singleton
eigenprojection compatibility. -/
theorem explicit_wightman_os_ambient_eigenprojection_law_of_complement
    (M : ExplicitWightmanOSReconstructedModel)
    (hComplement :
      ExplicitWightmanOSAmbientEigenvectorComplementAnnihilationLaw M) :
    ExplicitWightmanOSAmbientEigenprojectionLaw M := by
  exact OrthogonalProjectionValuedSetFunction.hasEigenprojectionLaw_of_complement
    hComplement

/-- Ambient complement spectral localization therefore gives the canonical
vacuum-orthogonal singleton eigenprojection law. -/
theorem explicit_wightman_os_canonical_eigenprojection_law_of_ambient_complement
    (M : ExplicitWightmanOSReconstructedModel)
    (hComplement :
      ExplicitWightmanOSAmbientEigenvectorComplementAnnihilationLaw M) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  exact explicit_wightman_os_canonical_eigenprojection_law_of_ambient M
    (explicit_wightman_os_ambient_eigenprojection_law_of_complement M hComplement)

end

end MathlibAnalytic
end MGAP4D
