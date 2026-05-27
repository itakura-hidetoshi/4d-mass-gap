import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The concrete real Hilbert space used as the first Mathlib-grounded R2
promotion surface. -/
abbrev ConcreteL2R2RealHilbertSpace : Type := lp (fun _ : Nat => Real) 2

/-- The concrete `l2` R2 real Hilbert space carries a normed additive commutative
group structure from Mathlib. -/
def concrete_l2_r2_real_hilbert_space_normed_add_comm_group :
    NormedAddCommGroup ConcreteL2R2RealHilbertSpace := by
  infer_instance

/-- The concrete `l2` R2 real Hilbert space carries a real inner product space
structure from Mathlib. -/
def concrete_l2_r2_real_hilbert_space_inner_product_space :
    InnerProductSpace Real ConcreteL2R2RealHilbertSpace := by
  infer_instance

/-- The concrete `l2` R2 real Hilbert space is complete by Mathlib. -/
def concrete_l2_r2_real_hilbert_space_complete :
    CompleteSpace ConcreteL2R2RealHilbertSpace := by
  infer_instance

/-- Bundled Mathlib-grounded readiness predicate for the concrete real Hilbert
space layer of the R2 promotion audit. -/
def concreteL2R2ConcreteRealHilbertSpaceReady : Prop :=
  Nonempty ConcreteL2R2RealHilbertSpace ∧
  Nonempty (NormedAddCommGroup ConcreteL2R2RealHilbertSpace) ∧
  Nonempty (InnerProductSpace Real ConcreteL2R2RealHilbertSpace) ∧
  Nonempty (CompleteSpace ConcreteL2R2RealHilbertSpace)

/-- The first R2 physical spectral promotion checklist item is discharged by a
concrete Mathlib real Hilbert space.

This theorem only supplies the Hilbert-space substrate. -/
theorem concrete_analytic_spine_l2_r2_concrete_real_hilbert_space_ready :
    concreteL2R2ConcreteRealHilbertSpaceReady := by
  exact ⟨
    inferInstance,
    ⟨concrete_l2_r2_real_hilbert_space_normed_add_comm_group⟩,
    ⟨concrete_l2_r2_real_hilbert_space_inner_product_space⟩,
    ⟨concrete_l2_r2_real_hilbert_space_complete⟩⟩

end

end MathlibAnalytic
end MGAP4D
