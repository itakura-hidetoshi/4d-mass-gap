import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct InnerProductSpace

noncomputable section

universe u v

variable {V : Type u} {W : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- A nonzero eigenvector of the positive normal operator `A† A` lies in the
exact range of the adjoint synthesis `A†`.

The witness is explicit: if `A† (A y) = λ • y` with `λ ≠ 0`, then
`λ⁻¹ • A y` synthesizes exactly to `y`.  This is the modewise alternative to
assuming a global coercive lower bound or global surjectivity of `A†`. -/
theorem continuousLinearMap_adjoint_exists_preimage_of_nonzero_normal_eigenvector
    (A : V →L[ℝ] W) (y : V) (lambda : ℝ)
    (hlambda : lambda ≠ 0)
    (hy : (A†) (A y) = lambda • y) :
    ∃ u : W, (A†) u = y := by
  refine ⟨lambda⁻¹ • A y, ?_⟩
  simp [hy, hlambda]

/-- A solved normal equation `A† A v = y` also gives an exact synthesis
preimage, namely `A v`. -/
theorem continuousLinearMap_adjoint_exists_preimage_of_normal_equation
    (A : V →L[ℝ] W) (y v : V)
    (hv : (A†) (A v) = y) :
    ∃ u : W, (A†) u = y :=
  ⟨A v, hv⟩

end

end MathlibAnalytic
end MGAP4D
