import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceAutomaticAnalyticTransferAssembly
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- A finite Euclidean symmetry of a Wilson lattice system, represented by a
permutation of link configurations preserving the Wilson action. -/
structure FiniteLatticeWilsonEuclideanSymmetryCertificate
    (L : FiniteLatticeWilsonSystem) where
  Transformation : Type
  configurationEquiv : Transformation → L.Configuration ≃ L.Configuration
  wilsonAction_invariant :
    ∀ (g : Transformation) (A : L.Configuration),
      L.wilsonAction (configurationEquiv g A) = L.wilsonAction A

/-- Action preservation implies preservation of every Wilson Boltzmann weight. -/
theorem finite_lattice_boltzmannWeight_euclideanInvariant
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteLatticeWilsonEuclideanSymmetryCertificate L)
    (g : E.Transformation) (A : L.Configuration) :
    L.boltzmannWeight (E.configurationEquiv g A) = L.boltzmannWeight A := by
  unfold FiniteLatticeWilsonSystem.boltzmannWeight
  rw [E.wilsonAction_invariant]

/-- Action-preserving configuration permutations preserve the normalized Wilson
Gibbs probability mass function pointwise. -/
theorem finite_lattice_gibbsPMF_euclideanInvariant
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteLatticeWilsonEuclideanSymmetryCertificate L)
    (g : E.Transformation) (A : L.Configuration) :
    L.gibbsPMF (E.configurationEquiv g A) = L.gibbsPMF A := by
  rw [finite_lattice_gibbsPMF_apply, finite_lattice_gibbsPMF_apply,
    finite_lattice_boltzmannWeight_euclideanInvariant E g A]

/-- Finite Wilson Gibbs expectation of a real observable. -/
def FiniteLatticeWilsonSystem.gibbsExpectation
    (L : FiniteLatticeWilsonSystem)
    (O : L.Configuration → ℝ) : ℝ :=
  ∑ A : L.Configuration, (L.gibbsPMF A).toReal * O A

/-- Expectation after applying an action-preserving Euclidean permutation to
the configuration argument of an observable. -/
def FiniteLatticeWilsonEuclideanSymmetryCertificate.transformedGibbsExpectation
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteLatticeWilsonEuclideanSymmetryCertificate L)
    (g : E.Transformation) (O : L.Configuration → ℝ) : ℝ :=
  L.gibbsExpectation (fun A => O (E.configurationEquiv g A))

/-- Every finite Wilson Gibbs expectation is invariant under an
action-preserving configuration permutation. -/
theorem finite_lattice_gibbsExpectation_euclideanInvariant
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteLatticeWilsonEuclideanSymmetryCertificate L)
    (g : E.Transformation) (O : L.Configuration → ℝ) :
    E.transformedGibbsExpectation g O = L.gibbsExpectation O := by
  classical
  unfold FiniteLatticeWilsonEuclideanSymmetryCertificate.transformedGibbsExpectation
    FiniteLatticeWilsonSystem.gibbsExpectation
  calc
    (∑ A : L.Configuration,
      (L.gibbsPMF A).toReal * O (E.configurationEquiv g A)) =
        ∑ A : L.Configuration,
          (L.gibbsPMF (E.configurationEquiv g A)).toReal *
            O (E.configurationEquiv g A) := by
              apply Finset.sum_congr rfl
              intro A _hA
              rw [finite_lattice_gibbsPMF_euclideanInvariant E g A]
    _ = ∑ A : L.Configuration, (L.gibbsPMF A).toReal * O A := by
      rw [Equiv.sum_comp (E.configurationEquiv g)]

end

end MathlibAnalytic
end MGAP4D
