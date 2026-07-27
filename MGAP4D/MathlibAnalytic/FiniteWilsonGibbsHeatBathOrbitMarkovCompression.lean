import MGAP4D.MathlibAnalytic.LinearSemigroupOrbitMarkovCompression
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHeatBathSpectralSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The theorem-generated finite-dimensional spectral semigroup is the identity
at time zero. -/
@[simp] theorem finiteDimensionalSymmetricHamiltonianSpectralSemigroup_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E)
    (hH : H.IsSymmetric)
    (dimension : ℕ)
    (hDimension : Module.finrank ℝ E = dimension)
    (x : E) :
    finiteDimensionalSymmetricHamiltonianSpectralSemigroup
        H hH dimension hDimension 0 x = x := by
  rw [finiteDimensionalSymmetricHamiltonianSpectralSemigroup,
    orthonormalDiagonalOperator_apply]
  conv_rhs =>
    rw [← (hH.eigenvectorBasis hDimension).sum_repr' x]
  simp

/-- The concrete finite Wilson Gibbs-Hilbert heat-bath semigroup is the identity
at time zero. -/
@[simp] theorem finite_lattice_gibbsHeatBathSpectralSemigroup_zero
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    L.gibbsHeatBathSpectralSemigroup 0 x = x := by
  simpa [FiniteLatticeWilsonSystem.gibbsHeatBathSpectralSemigroup] using
    (finiteDimensionalSymmetricHamiltonianSpectralSemigroup_zero
      L.gibbsHeatBathHamiltonianLinearMap
      (finite_lattice_gibbsHeatBathHamiltonianLinearMap_isSymmetric L)
      (Module.finrank ℝ L.GibbsHilbertSpace)
      rfl
      x)

/-- The concrete finite Wilson observable heat-bath semigroup is the identity at
time zero. -/
@[simp] theorem finite_lattice_gibbsObservableHeatBathSpectralSemigroup_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsObservableHeatBathSpectralSemigroup 0 f = f := by
  rw [finite_lattice_gibbsObservableHeatBathSpectralSemigroup_apply,
    finite_lattice_gibbsHeatBathSpectralSemigroup_zero,
    finite_lattice_gibbsHilbert_observe_embed]

/-- The canonical forward-orbit Markov compression of the concrete finite Wilson
Gibbs observable heat-bath semigroup. -/
noncomputable def
    FiniteLatticeWilsonSystem.gibbsObservableHeatBathOrbitMarkovCompression
    (L : FiniteLatticeWilsonSystem) :
    LinearMarkovCompression
      (L.Configuration → ℝ)
      (LinearSemigroupOrbitSpace (L.Configuration → ℝ))
      (fun t F => linearSemigroupOrbitTranslate t F)
      (fun t f => L.gibbsObservableHeatBathSpectralSemigroup t f) :=
  linearSemigroupOrbitMarkovCompression
    (fun t => L.gibbsObservableHeatBathSpectralSemigroup t)
    (finite_lattice_gibbsObservableHeatBathSpectralSemigroup_zero L)

@[simp] theorem
    finite_lattice_gibbsObservableHeatBathOrbitMarkovCompression_lift_apply
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (s : NNReal) :
    L.gibbsObservableHeatBathOrbitMarkovCompression.lift f s =
      L.gibbsObservableHeatBathSpectralSemigroup s f :=
  rfl

@[simp] theorem
    finite_lattice_gibbsObservableHeatBathOrbitMarkovCompression_condition_apply
    (L : FiniteLatticeWilsonSystem)
    (F : LinearSemigroupOrbitSpace (L.Configuration → ℝ)) :
    L.gibbsObservableHeatBathOrbitMarkovCompression.condition F = F 0 :=
  rfl

/-- Time-zero conditioning after a translated canonical orbit is exactly the
concrete finite Gibbs heat-bath evolution. -/
theorem
    finite_lattice_gibbsObservableHeatBathOrbitMarkovCompression_condition_translate_lift
    (L : FiniteLatticeWilsonSystem)
    (t : NNReal)
    (f : L.Configuration → ℝ) :
    L.gibbsObservableHeatBathOrbitMarkovCompression.condition
        (linearSemigroupOrbitTranslate t
          (L.gibbsObservableHeatBathOrbitMarkovCompression.lift f)) =
      L.gibbsObservableHeatBathSpectralSemigroup t f :=
  L.gibbsObservableHeatBathOrbitMarkovCompression.condition_translate_lift t f

end

end MathlibAnalytic
end MGAP4D
