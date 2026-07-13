import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelInnerSymmetry
import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMMeasureConstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- The quadratic form of a canonical simple-function PVM integral is exactly
the simple-function integral against the quadratic scalar spectral measure. -/
theorem pvmSimpleFuncSpectralIntegralOperator_inner_self_eq_simpleFuncIntegral
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (f : SimpleFunc ℝ ℝ) (ψ : M.H) :
    inner ℝ ψ (pvmSimpleFuncSpectralIntegralOperator M.spectralPVM f ψ) =
      f.integral (A.scalarMeasure ψ) := by
  classical
  have hProjectionQuadratic : ∀ c : f.range,
      inner ℝ ψ
          (M.spectralPVM.projection (pvmSimpleFuncFiber f c) ψ) =
        ‖M.spectralPVM.projection (pvmSimpleFuncFiber f c) ψ‖ ^ 2 := by
    intro c
    calc
      inner ℝ ψ
          (M.spectralPVM.projection (pvmSimpleFuncFiber f c) ψ) =
        inner ℝ ψ
          (M.spectralPVM.projection (pvmSimpleFuncFiber f c)
            (M.spectralPVM.projection (pvmSimpleFuncFiber f c) ψ)) := by
          rw [M.spectralPVM.idempotent]
      _ = inner ℝ
          (M.spectralPVM.projection (pvmSimpleFuncFiber f c) ψ)
          (M.spectralPVM.projection (pvmSimpleFuncFiber f c) ψ) :=
        (M.spectralPVM.selfAdjoint
          (pvmSimpleFuncFiber f c) ψ
          (M.spectralPVM.projection (pvmSimpleFuncFiber f c) ψ)).symm
      _ = ‖M.spectralPVM.projection (pvmSimpleFuncFiber f c) ψ‖ ^ 2 :=
        real_inner_self_eq_norm_sq
  rw [pvmSimpleFuncSpectralIntegralOperator_apply]
  unfold pvmFiniteSimpleSpectralIntegral
  simp only [inner_sum, real_inner_smul_right]
  rw [SimpleFunc.integral_eq]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hProjectionQuadratic c]
  rw [← quadraticPVM_scalarMeasure_real_apply A ψ
    (pvmSimpleFuncFiber f c) (pvmSimpleFuncFiber_measurable f c)]
  simp [pvmSimpleFuncFiber]

/-- Equivalent orientation, useful when the completed PVM symmetry theorem is
used downstream. -/
theorem pvmSimpleFuncSpectralIntegralOperator_inner_self_eq_simpleFuncIntegral'
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (f : SimpleFunc ℝ ℝ) (ψ : M.H) :
    inner ℝ (pvmSimpleFuncSpectralIntegralOperator M.spectralPVM f ψ) ψ =
      f.integral (A.scalarMeasure ψ) := by
  rw [pvmSimpleFuncSpectralIntegralOperator_inner_eq]
  exact pvmSimpleFuncSpectralIntegralOperator_inner_self_eq_simpleFuncIntegral
    A f ψ

end

end MathlibAnalytic
end MGAP4D
