import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A continuous finite real matrix family with everywhere nonzero determinant
has a continuous nonsingular inverse.  This is the finite-dimensional inverse
continuity layer used by the canonical Perron anchor construction. -/
theorem continuous_matrix_inv_of_det_ne_zero
    {X n : Type}
    [TopologicalSpace X]
    [Fintype n]
    [DecidableEq n]
    (A : X → Matrix n n ℝ)
    (hA : Continuous A)
    (hdet : ∀ x, (A x).det ≠ 0) :
    Continuous (fun x => (A x)⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact
    (continuousAt_matrix_inv (A x)
      (continuousAt_inv₀ (hdet x))).comp x hA.continuousAt

/-- Applying a continuous nonsingular inverse matrix family to a continuous
finite vector family remains continuous. -/
theorem continuous_matrix_inv_mulVec_of_det_ne_zero
    {X n : Type}
    [TopologicalSpace X]
    [Fintype n]
    [DecidableEq n]
    (A : X → Matrix n n ℝ)
    (v : X → n → ℝ)
    (hA : Continuous A)
    (hv : Continuous v)
    (hdet : ∀ x, (A x).det ≠ 0) :
    Continuous (fun x => Matrix.mulVec (A x)⁻¹ (v x)) :=
  (continuous_matrix_inv_of_det_ne_zero A hA hdet).matrix_mulVec hv

end

end MathlibAnalytic
end MGAP4D
