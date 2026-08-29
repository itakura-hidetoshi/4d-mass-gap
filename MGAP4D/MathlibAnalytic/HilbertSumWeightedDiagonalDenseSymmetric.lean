import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalLinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped InnerProductSpace lp

noncomputable section

universe u v

open Classical in
/-- Every one-coordinate vector lies in the maximal weighted `ℓ²` domain. -/
theorem realHilbertSumWeightedDiagonal_single_mem_domain
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)]
    (w : ι → ℝ)
    (i : ι)
    (a : G i) :
    lp.single 2 i a ∈
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w).domain := by
  rw [realHilbertSumWeightedDiagonalLinearPMap_domain,
    mem_realHilbertSumWeightedDiagonalDomain]
  have h : Memℓp
      (fun j => (lp.single 2 i (w i • a) : lp G 2) j) 2 :=
    (lp.single 2 i (w i • a) : lp G 2).property
  convert h using 1
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [lp.single_apply, hji]

/-- The maximal weighted diagonal domain is dense.  No countability of the
index type is required: Mathlib's canonical finite-coordinate partial sums
converge to every `lp` vector. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_dense_domain
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)]
    (w : ι → ℝ) :
    Dense
      (((realHilbertSumWeightedDiagonalLinearPMap (G := G) w).domain :
        Submodule ℝ (lp G 2)) : Set (lp G 2)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  refine mem_closure_of_tendsto
    (lp.hasSum_single (p := 2) (by norm_num) x)
    (Eventually.of_forall ?_)
  intro s
  rw [SetLike.mem_coe]
  refine Submodule.sum_mem _ ?_
  intro i hi
  exact realHilbertSumWeightedDiagonal_single_mem_domain (G := G) w i (x i)

/-- A real diagonal multiplication operator on its maximal weighted domain is
formally symmetric. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_isFormalAdjoint_self
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℝ (G i)]
    (w : ι → ℝ) :
    LinearPMap.IsFormalAdjoint (𝕜 := ℝ)
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w)
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [realHilbertSumWeightedDiagonalLinearPMap_apply,
    realHilbertSumWeightedDiagonalLinearPMap_apply,
    real_inner_smul_left, real_inner_smul_right]

/-- The intrinsic logarithmic generator coordinates of every compact positive
real-Hilbert operator have dense domain. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_dense_domain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    Dense
      (((realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive).domain :
        Submodule ℝ
          (lp
            (fun mu : Module.End.Eigenvalues
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
              Module.End.eigenspace
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
            2)) : Set _) := by
  exact
    realHilbertSumWeightedDiagonalLinearPMap_dense_domain
      (G := fun mu : Module.End.Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        Module.End.eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
      (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)

/-- The intrinsic logarithmic generator coordinates are formally symmetric. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_isFormalAdjoint_self
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    LinearPMap.IsFormalAdjoint (𝕜 := ℝ)
      (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive)
      (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive) := by
  exact
    realHilbertSumWeightedDiagonalLinearPMap_isFormalAdjoint_self
      (G := fun mu : Module.End.Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        Module.End.eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
      (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)

end

end MathlibAnalytic
end MGAP4D