import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticReflectionLimitTransfer
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitOSPropertyTransfer
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators ENNReal

noncomputable section

/-- Expectation of a real observable with respect to the normalized finite
Wilson Gibbs probability mass function. -/
noncomputable def FiniteLatticeWilsonSystem.gibbsExpectation
    (L : FiniteLatticeWilsonSystem)
    (O : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration, (L.gibbsPMF A).toReal * O A

/-- A finite Euclidean symmetry of a Wilson lattice system is a permutation of
link configurations preserving the Wilson action. -/
structure FiniteLatticeWilsonEuclideanSymmetryCertificate
    (L : FiniteLatticeWilsonSystem) where
  Transformation : Type
  configurationEquiv : Transformation → L.Configuration ≃ L.Configuration
  wilsonAction_invariant :
    ∀ (g : Transformation) (A : L.Configuration),
      L.wilsonAction (configurationEquiv g A) = L.wilsonAction A

/-- Action preservation implies preservation of the Boltzmann weight. -/
theorem finite_lattice_boltzmannWeight_euclideanInvariant
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteLatticeWilsonEuclideanSymmetryCertificate L)
    (g : E.Transformation) (A : L.Configuration) :
    L.boltzmannWeight (E.configurationEquiv g A) = L.boltzmannWeight A := by
  unfold FiniteLatticeWilsonSystem.boltzmannWeight
  rw [E.wilsonAction_invariant]

/-- Action-preserving configuration permutations preserve the normalized
Wilson Gibbs probability mass function pointwise. -/
theorem finite_lattice_gibbsPMF_euclideanInvariant
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteLatticeWilsonEuclideanSymmetryCertificate L)
    (g : E.Transformation) (A : L.Configuration) :
    L.gibbsPMF (E.configurationEquiv g A) = L.gibbsPMF A := by
  rw [finite_lattice_gibbsPMF_apply, finite_lattice_gibbsPMF_apply,
    finite_lattice_boltzmannWeight_euclideanInvariant E g A]

/-- Expectation after applying a finite Euclidean symmetry to the configuration
argument of an observable. -/
noncomputable def
    FiniteLatticeWilsonEuclideanSymmetryCertificate.transformedGibbsExpectation
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteLatticeWilsonEuclideanSymmetryCertificate L)
    (g : E.Transformation) (O : L.Configuration → ℝ) : ℝ :=
  L.gibbsExpectation (fun A => O (E.configurationEquiv g A))

/-- Finite Wilson Gibbs expectation is invariant under every action-preserving
configuration permutation. -/
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

/-- Sequential finite Wilson data whose actual Gibbs expectations converge to
continuum Euclidean expectations. -/
structure FiniteWilsonOSAutomaticEuclideanLimitData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  Transformation : Type
  scale : ℕ → W.index
  symmetry :
    ∀ n : ℕ,
      FiniteLatticeWilsonEuclideanSymmetryCertificate (W.system (scale n))
  finiteTransformation :
    (n : ℕ) → Transformation → (symmetry n).Transformation
  finiteObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  continuumReferenceExpectation : Observable → ℝ
  continuumTransformedExpectation : Transformation → Observable → ℝ
  referenceExpectationConverges :
    ∀ O : Observable,
      Tendsto
        (fun n : ℕ =>
          (W.system (scale n)).gibbsExpectation (finiteObservable n O))
        atTop (nhds (continuumReferenceExpectation O))
  transformedExpectationConverges :
    ∀ (g : Transformation) (O : Observable),
      Tendsto
        (fun n : ℕ =>
          (symmetry n).transformedGibbsExpectation
            (finiteTransformation n g) (finiteObservable n O))
        atTop (nhds (continuumTransformedExpectation g O))

/-- Adapter from actual finite Wilson expectations to the generic Euclidean
invariance limit record. -/
noncomputable def
    FiniteWilsonOSAutomaticEuclideanLimitData.toEuclideanInvarianceLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticEuclideanLimitData W) :
    EuclideanYangMillsEuclideanInvarianceLimitData :=
  { Observable := D.Observable
    Transformation := D.Transformation
    finiteReferenceExpectation := fun n O =>
      (W.system (D.scale n)).gibbsExpectation (D.finiteObservable n O)
    finiteTransformedExpectation := fun n g O =>
      (D.symmetry n).transformedGibbsExpectation
        (D.finiteTransformation n g) (D.finiteObservable n O)
    continuumReferenceExpectation := D.continuumReferenceExpectation
    continuumTransformedExpectation := D.continuumTransformedExpectation
    finiteEuclideanInvariant := fun n g O =>
      finite_lattice_gibbsExpectation_euclideanInvariant
        (D.symmetry n) (D.finiteTransformation n g) (D.finiteObservable n O)
    referenceExpectationConverges := D.referenceExpectationConverges
    transformedExpectationConverges := D.transformedExpectationConverges }

/-- Continuum Euclidean invariance obtained from finite Wilson symmetries and
pointwise convergence of the two expectation sequences. -/
theorem finite_wilson_os_automatic_euclidean_invariance_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticEuclideanLimitData W) :
    D.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant :=
  euclidean_yang_mills_euclidean_invariance_passes_to_limit
    D.toEuclideanInvarianceLimitData

end

end MathlibAnalytic
end MGAP4D
