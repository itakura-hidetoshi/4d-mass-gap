import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMMeasureConstruction
import Mathlib.Analysis.InnerProductSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Disjoint PVM ranges are orthogonal.  This follows from self-adjointness and
the disjoint-composition-zero law. -/
theorem explicit_wightman_os_disjoint_projection_inner_eq_zero
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasDisjointCompositionZero)
    {s t : Set ℝ} (hDisjoint : Disjoint s t) (ψ : M.H) :
    inner ℝ
      (M.spectralPVM.projection s ψ)
      (M.spectralPVM.projection t ψ) = 0 := by
  calc
    inner ℝ
        (M.spectralPVM.projection s ψ)
        (M.spectralPVM.projection t ψ) =
      inner ℝ ψ
        (M.spectralPVM.projection s
          (M.spectralPVM.projection t ψ)) :=
      M.spectralPVM.selfAdjoint s ψ
        (M.spectralPVM.projection t ψ)
    _ = inner ℝ ψ 0 := by
      rw [hComposition s t hDisjoint ψ]
    _ = 0 := by simp

/-- Pythagoras for disjoint PVM projections. -/
theorem explicit_wightman_os_disjoint_projection_norm_sq_add
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasDisjointCompositionZero)
    {s t : Set ℝ} (hDisjoint : Disjoint s t) (ψ : M.H) :
    ‖M.spectralPVM.projection (s ∪ t) ψ‖ ^ 2 =
      ‖M.spectralPVM.projection s ψ‖ ^ 2 +
        ‖M.spectralPVM.projection t ψ‖ ^ 2 := by
  rw [M.spectralPVM.disjoint_additive s t hDisjoint ψ]
  rw [norm_add_sq_real]
  rw [explicit_wightman_os_disjoint_projection_inner_eq_zero
    M hComposition hDisjoint ψ]
  ring

/-- The ENNReal-valued quadratic PVM weight is finitely additive on disjoint
measurable energy sets. -/
theorem quadraticPVMWeight_disjoint_union
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasDisjointCompositionZero)
    {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hDisjoint : Disjoint s t) (ψ : M.H) :
    M.quadraticPVMWeight ψ (s ∪ t) (hs.union ht) =
      M.quadraticPVMWeight ψ s hs +
        M.quadraticPVMWeight ψ t ht := by
  unfold ExplicitWightmanOSReconstructedModel.quadraticPVMWeight
  rw [explicit_wightman_os_disjoint_projection_norm_sq_add
    M hComposition hDisjoint ψ]
  exact ENNReal.ofReal_add
    (sq_nonneg ‖M.spectralPVM.projection s ψ‖)
    (sq_nonneg ‖M.spectralPVM.projection t ψ‖)

/-- All finite measure axioms required by the scalar spectral measure construction
are already consequences of the existing PVM laws.  Only countable-union
continuity remains genuinely additional. -/
theorem explicit_wightman_os_quadratic_pvm_finite_measure_laws
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasDisjointCompositionZero) :
    (∀ ψ : M.H,
      M.quadraticPVMWeight ψ ∅ MeasurableSet.empty = 0) ∧
    (∀ (ψ : M.H) {s t : Set ℝ}
      (hs : MeasurableSet s) (ht : MeasurableSet t),
      Disjoint s t →
        M.quadraticPVMWeight ψ (s ∪ t) (hs.union ht) =
          M.quadraticPVMWeight ψ s hs +
            M.quadraticPVMWeight ψ t ht) := by
  exact ⟨quadraticPVMWeight_empty M,
    fun ψ s t hs ht hDisjoint =>
      quadraticPVMWeight_disjoint_union
        M hComposition hs ht hDisjoint ψ⟩

end

end MathlibAnalytic
end MGAP4D
