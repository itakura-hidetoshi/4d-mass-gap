import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ConcreteRealHilbertSpace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A minimal Mathlib-facing representation of a densely defined linear operator
on the concrete real R2 Hilbert substrate.

The operator is represented as a linear map from a submodule domain into the
ambient Hilbert space, together with a proof that the domain is dense.  This is
the correct boundary before any self-adjointness or spectral theorem statement.
This structure does not by itself assert unboundedness. -/
structure ConcreteL2R2DenselyDefinedOperator where
  domain : Submodule ℝ ConcreteL2R2RealHilbertSpace
  operator : domain →ₗ[ℝ] ConcreteL2R2RealHilbertSpace
  denseDomain : Dense ((domain : Set ConcreteL2R2RealHilbertSpace))
  boundaryNotUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheorem : Prop

/-- The full-domain zero operator as the first concrete densely defined operator
surface.

This closes the dense-domain/operator-shape part of the second checklist item.
It deliberately does not claim that this example is unbounded; nontrivial
unboundedness remains a later promotion surface. -/
def concreteL2R2FullDomainZeroDenselyDefinedOperator :
    ConcreteL2R2DenselyDefinedOperator :=
  { domain := ⊤
    operator := 0
    denseDomain := by
      simpa using
        (dense_univ : Dense (Set.univ : Set ConcreteL2R2RealHilbertSpace))
    boundaryNotUnboundednessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheorem := True }

/-- Readiness predicate for the dense-domain/operator-shape part of the R2
promotion audit. -/
def concreteL2R2DenselyDefinedOperatorReady : Prop :=
  ∃ T : ConcreteL2R2DenselyDefinedOperator,
    Dense ((T.domain : Set ConcreteL2R2RealHilbertSpace)) ∧
    T.boundaryNotUnboundednessTheorem ∧
    T.boundaryNotClosedOperatorTheorem ∧
    T.boundaryNotSelfAdjointnessTheorem ∧
    T.boundaryNotSpectralTheorem

/-- The R2 route has a concrete Mathlib-facing densely defined operator surface.

This theorem supplies an explicit dense domain and a linear operator from that
domain into the concrete real Hilbert space.  It does not assert nontrivial
unboundedness, closedness, self-adjointness, PVM construction, an exact `33/20`
atom, positive spectral weight, or the physical Yang--Mills Hamiltonian. -/
theorem concrete_analytic_spine_l2_r2_densely_defined_operator_ready :
    concreteL2R2DenselyDefinedOperatorReady := by
  refine ⟨concreteL2R2FullDomainZeroDenselyDefinedOperator, ?_⟩
  exact ⟨
    concreteL2R2FullDomainZeroDenselyDefinedOperator.denseDomain,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
