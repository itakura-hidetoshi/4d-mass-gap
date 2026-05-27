import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineRealHilbertDomain

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The concrete real Hilbert space used as the first Mathlib-grounded R2
promotion surface.

This reuses the already-built Mathlib-native real Hilbert substrate from the
from-scratch concrete analytic spine, avoiding a fragile direct dependency on an
`lp` namespace whose name varies across Mathlib versions. -/
abbrev ConcreteL2R2RealHilbertSpace : Type := ConcreteRealHilbertSpace

/-- The concrete R2 Hilbert substrate carries a normed additive commutative group
structure from Mathlib. -/
theorem concrete_l2_r2_real_hilbert_space_normed_add_comm_group :
    Nonempty (NormedAddCommGroup ConcreteL2R2RealHilbertSpace) := by
  exact concrete_real_hilbert_space_normed_add_comm_group

/-- The concrete R2 Hilbert substrate carries a real inner product space structure
from Mathlib. -/
theorem concrete_l2_r2_real_hilbert_space_inner_product_space :
    Nonempty (InnerProductSpace ℝ ConcreteL2R2RealHilbertSpace) := by
  exact concrete_real_hilbert_space_inner_product_space

/-- The concrete R2 Hilbert substrate is complete by Mathlib. -/
theorem concrete_l2_r2_real_hilbert_space_complete :
    CompleteSpace ConcreteL2R2RealHilbertSpace := by
  exact concrete_real_hilbert_space_complete

/-- Bundled Mathlib-grounded readiness predicate for the concrete real Hilbert
space layer of the R2 promotion audit. -/
def concreteL2R2ConcreteRealHilbertSpaceReady : Prop :=
  Nonempty ConcreteL2R2RealHilbertSpace ∧
  Nonempty (NormedAddCommGroup ConcreteL2R2RealHilbertSpace) ∧
  Nonempty (InnerProductSpace ℝ ConcreteL2R2RealHilbertSpace) ∧
  CompleteSpace ConcreteL2R2RealHilbertSpace

/-- The first R2 physical spectral promotion checklist item is discharged by a
concrete Mathlib real Hilbert space.

This theorem only supplies the Hilbert-space substrate. -/
theorem concrete_analytic_spine_l2_r2_concrete_real_hilbert_space_ready :
    concreteL2R2ConcreteRealHilbertSpaceReady := by
  exact ⟨
    ⟨(0 : ConcreteL2R2RealHilbertSpace)⟩,
    concrete_l2_r2_real_hilbert_space_normed_add_comm_group,
    concrete_l2_r2_real_hilbert_space_inner_product_space,
    concrete_l2_r2_real_hilbert_space_complete⟩

end

end MathlibAnalytic
end MGAP4D
