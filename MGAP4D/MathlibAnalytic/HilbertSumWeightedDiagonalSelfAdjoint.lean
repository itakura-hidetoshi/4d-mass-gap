import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalDenseSymmetric
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped InnerProductSpace lp

noncomputable section

universe u v

/-- The adjoint of a maximal real weighted diagonal operator has exactly the
same coordinate action.  This is the key maximal-domain step: testing the
adjoint identity against a one-coordinate vector determines every coordinate. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_adjoint_apply_coord
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℝ (G i)]
    [∀ i, CompleteSpace (G i)]
    (w : ι → ℝ)
    (y : (LinearPMap.adjoint
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w)).domain)
    (i : ι) :
    LinearPMap.adjoint
        (realHilbertSumWeightedDiagonalLinearPMap (G := G) w) y i =
      w i •
        ((y : (LinearPMap.adjoint
          (realHilbertSumWeightedDiagonalLinearPMap (G := G) w)).domain) :
          lp G 2) i := by
  classical
  let H := realHilbertSumWeightedDiagonalLinearPMap (G := G) w
  have hDense : Dense (H.domain : Set (lp G 2)) := by
    simpa [H] using
      realHilbertSumWeightedDiagonalLinearPMap_dense_domain (G := G) w
  have hAdj : (LinearPMap.adjoint H).IsFormalAdjoint H :=
    LinearPMap.adjoint_isFormalAdjoint hDense
  apply (Set.univ_dense.eq_of_inner_left ℝ)
  intro a ha
  let s0 : lp G 2 := lp.single 2 i a
  have hs0 : s0 ∈ H.domain := by
    simpa [H, s0] using
      realHilbertSumWeightedDiagonal_single_mem_domain (G := G) w i a
  let s : H.domain := ⟨s0, hs0⟩
  have hHsingle : H s = lp.single 2 i (w i • a) := by
    apply lp.ext
    funext j
    change w j • s0 j = (lp.single 2 i (w i • a) : lp G 2) j
    by_cases hji : j = i
    · subst j
      simp [s0]
    · simp [s0, lp.single_apply, hji]
  have h := hAdj y s
  have hs_coe : (s : lp G 2) = lp.single 2 i a := rfl
  rw [hs_coe, hHsingle, lp.inner_single_right, lp.inner_single_right] at h
  simpa [real_inner_smul_left, real_inner_smul_right] using h

/-- Every vector in the adjoint domain already belongs to the maximal weighted
domain. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_adjoint_domain_le
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℝ (G i)]
    [∀ i, CompleteSpace (G i)]
    (w : ι → ℝ) :
    (LinearPMap.adjoint
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w)).domain ≤
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w).domain := by
  intro y hy
  rw [realHilbertSumWeightedDiagonalLinearPMap_domain,
    mem_realHilbertSumWeightedDiagonalDomain]
  let ya : (LinearPMap.adjoint
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w)).domain := ⟨y, hy⟩
  have hz : Memℓp
      (fun i =>
        LinearPMap.adjoint
          (realHilbertSumWeightedDiagonalLinearPMap (G := G) w) ya i) 2 :=
    (LinearPMap.adjoint
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w) ya).property
  convert hz using 1
  funext i
  exact
    (realHilbertSumWeightedDiagonalLinearPMap_adjoint_apply_coord
      (G := G) w ya i).symm

/-- The adjoint is contained in the maximal weighted diagonal operator. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_adjoint_le
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℝ (G i)]
    [∀ i, CompleteSpace (G i)]
    (w : ι → ℝ) :
    LinearPMap.adjoint
        (realHilbertSumWeightedDiagonalLinearPMap (G := G) w) ≤
      realHilbertSumWeightedDiagonalLinearPMap (G := G) w := by
  refine ⟨realHilbertSumWeightedDiagonalLinearPMap_adjoint_domain_le
    (G := G) w, ?_⟩
  intro x y hxy
  apply lp.ext
  funext i
  rw [realHilbertSumWeightedDiagonalLinearPMap_adjoint_apply_coord (G := G) w x i,
    realHilbertSumWeightedDiagonalLinearPMap_apply]
  congr 1
  exact congrArg (fun z : lp G 2 => z i) hxy

/-- A real multiplication operator on a dependent Hilbert sum, with its
maximal weighted `ℓ²` domain, is self-adjoint. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_isSelfAdjoint
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℝ (G i)]
    [∀ i, CompleteSpace (G i)]
    (w : ι → ℝ) :
    IsSelfAdjoint
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · exact realHilbertSumWeightedDiagonalLinearPMap_adjoint_le (G := G) w
  · exact
      (realHilbertSumWeightedDiagonalLinearPMap_isFormalAdjoint_self
        (G := G) w).le_adjoint
          (realHilbertSumWeightedDiagonalLinearPMap_dense_domain (G := G) w)

/-- In particular the maximal real weighted diagonal operator is closed. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_isClosed
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℝ (G i)]
    [∀ i, CompleteSpace (G i)]
    (w : ι → ℝ) :
    (realHilbertSumWeightedDiagonalLinearPMap (G := G) w).IsClosed :=
  (realHilbertSumWeightedDiagonalLinearPMap_isSelfAdjoint (G := G) w).isClosed

end

end MathlibAnalytic
end MGAP4D