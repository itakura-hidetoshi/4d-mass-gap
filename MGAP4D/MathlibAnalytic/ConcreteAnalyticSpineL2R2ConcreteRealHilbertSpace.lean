import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The concrete real Hilbert space used as the first Mathlib-grounded R2
promotion surface.

This is the standard real `l2` Hilbert space of square-summable sequences over
`Nat`, implemented through Mathlib's `lp`/`PiLp` infrastructure. -/
abbrev ConcreteL2R2RealHilbertSpace : Type := lp (fun _ : Nat => Real) 2

/-- The concrete `l2` R2 real Hilbert space carries a normed additive commutative
group structure from Mathlib. -/
theorem concrete_l2_r2_real_hilbert_space_normed_add_comm_group :
    NormedAddCommGroup ConcreteL2R2RealHilbertSpace := by
  infer_instance

/-- The concrete `l2` R2 real Hilbert space carries a real inner product space
structure from Mathlib. -/
theorem concrete_l2_r2_real_hilbert_space_inner_product_space :
    InnerProductSpace Real ConcreteL2R2RealHilbertSpace := by
  infer_instance

/-- The concrete `l2` R2 real Hilbert space is complete by Mathlib. -/
theorem concrete_l2_r2_real_hilbert_space_complete :
    CompleteSpace ConcreteL2R2RealHilbertSpace := by
  infer_instance

/-- Bundled Mathlib-grounded readiness predicate for the concrete real Hilbert
space layer of the R2 promotion audit. -/
def concreteL2R2ConcreteRealHilbertSpaceReady : Prop :=
  Nonempty ConcreteL2R2RealHilbertSpace ∧
  NormedAddCommGroup ConcreteL2R2RealHilbertSpace ∧
  InnerProductSpace Real ConcreteL2R2RealHilbertSpace ∧
  CompleteSpace ConcreteL2R2RealHilbertSpace

/-- The first R2 physical spectral promotion checklist item is discharged by a
concrete Mathlib real Hilbert space.

This theorem only supplies the Hilbert-space substrate.  It does not assert a
densely defined unbounded operator, self-adjointness, PVM construction, an exact
`33/20` atom, positive spectral weight, or the physical Yang--Mills Hamiltonian. -/
theorem concrete_analytic_spine_l2_r2_concrete_real_hilbert_space_ready :
    concreteL2R2ConcreteRealHilbertSpaceReady := by
  exact ⟨
    inferInstance,
    concrete_l2_r2_real_hilbert_space_normed_add_comm_group,
    concrete_l2_r2_real_hilbert_space_inner_product_space,
    concrete_l2_r2_real_hilbert_space_complete⟩

end

end MathlibAnalytic
end MGAP4D
