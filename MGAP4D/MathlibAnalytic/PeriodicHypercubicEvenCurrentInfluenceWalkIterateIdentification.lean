import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinIterateKernel
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Identification of current influence walk and iterate kernels

The same-root route has two finite influence carriers:

* the explicit endpoint-constrained walk kernel, whose support is controlled by
  actual Wilson-plaquette-local distance;
* the recursive finite iterate kernel, whose rows are controlled by powers of
  the current Dobrushin coefficient.

This file identifies them exactly.  The proof uses the canonical `Fin.cons`
head/tail decomposition of a finite walk and finite-sum reindexing.  As a
result, exact geometric support vanishing and coefficient-power bounds now live
on the same finite kernel.

This remains finite-kernel algebra.  No covariance representation or infinite
Neumann series is asserted here.  In particular, the explicit finite-volume
high-temperature threshold is not asserted along the factorial continuum
coupling sequence, update time is not identified with physical OS Euclidean
time, and no positive mass or Hamiltonian gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_walkIterateIdentification
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Adding the first vertex to a length-`d` tail factors the length-`d+1`
walk weight into the first influence coefficient and the tail weight. -/
private theorem periodicHypercubicEvenInfluenceWalkWeight_cons
    (H d : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (head : PeriodicHypercubicEvenEdge H)
    (tail : Fin (d + 1) → PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenInfluenceWalkWeight H (d + 1) influence
        (Fin.cons head tail) =
      influence head (tail 0) *
        periodicHypercubicEvenInfluenceWalkWeight H d influence tail := by
  simp [periodicHypercubicEvenInfluenceWalkWeight, Fin.prod_univ_succ]

/-- The explicit walk kernel of degree zero is the identity kernel. -/
private theorem periodicHypercubicEvenInfluenceWalkKernel_zero
    (H : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (target source : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenInfluenceWalkKernel H 0 influence target source =
      if target = source then 1 else 0 := by
  classical
  by_cases hts : target = source
  · subst source
    unfold periodicHypercubicEvenInfluenceWalkKernel
    rw [Finset.sum_eq_single (fun _ : Fin 1 => target)]
    · simp [periodicHypercubicEvenInfluenceWalkWeight]
    · intro γ _ hγ
      have hzero : γ 0 ≠ target := by
        intro hγ0
        apply hγ
        funext i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact hγ0
      simp [hzero]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ (fun _ : Fin 1 => target)))
  · have hsum :
        periodicHypercubicEvenInfluenceWalkKernel H 0 influence target source = 0 := by
      unfold periodicHypercubicEvenInfluenceWalkKernel
      apply Finset.sum_eq_zero
      intro γ _
      by_cases h0 : γ 0 = target
      · have hnotSource : γ 0 ≠ source := by
          intro hs
          exact hts (h0.symm.trans hs)
        simp [h0, hnotSource]
      · simp [h0]
    simpa [hts] using hsum

/-- The explicit length-`d+1` walk kernel obeys the same one-step convolution
recursion as the recursive finite iterate kernel. -/
private theorem periodicHypercubicEvenInfluenceWalkKernel_succ
    (H d : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (target source : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenInfluenceWalkKernel H (d + 1) influence target source =
      ∑ mid : PeriodicHypercubicEvenEdge H,
        influence target mid *
          periodicHypercubicEvenInfluenceWalkKernel H d influence mid source := by
  classical
  unfold periodicHypercubicEvenInfluenceWalkKernel
  calc
    _ =
        ∑ p : PeriodicHypercubicEvenEdge H ×
            (Fin (d + 1) → PeriodicHypercubicEvenEdge H),
          if p.1 = target ∧ p.2 (Fin.last d) = source then
            influence p.1 (p.2 0) *
              periodicHypercubicEvenInfluenceWalkWeight H d influence p.2
          else 0 := by
      refine Fintype.sum_equiv
        ((Fin.consEquiv
          (fun _ : Fin (d + 2) => PeriodicHypercubicEvenEdge H)).symm)
        _ _ ?_
      intro γ
      change
        (if γ 0 = target ∧ γ (Fin.last (d + 1)) = source then
          periodicHypercubicEvenInfluenceWalkWeight H (d + 1) influence γ
        else 0) =
        if γ 0 = target ∧ Fin.tail γ (Fin.last d) = source then
          influence (γ 0) (Fin.tail γ 0) *
            periodicHypercubicEvenInfluenceWalkWeight H d influence (Fin.tail γ)
        else 0
      rw [← Fin.cons_self_tail γ]
      simp [periodicHypercubicEvenInfluenceWalkWeight_cons]
    _ =
        ∑ head : PeriodicHypercubicEvenEdge H,
          ∑ tail : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
            if head = target ∧ tail (Fin.last d) = source then
              influence head (tail 0) *
                periodicHypercubicEvenInfluenceWalkWeight H d influence tail
            else 0 := by
      rw [Fintype.sum_prod_type]
    _ =
        ∑ tail : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
          if tail (Fin.last d) = source then
            influence target (tail 0) *
              periodicHypercubicEvenInfluenceWalkWeight H d influence tail
          else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro tail _
      rw [Finset.sum_eq_single target]
      · simp
      · intro head _ hhead
        simp [hhead]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ target))
    _ =
        ∑ mid : PeriodicHypercubicEvenEdge H,
          influence target mid *
            periodicHypercubicEvenInfluenceWalkKernel H d influence mid source := by
      symm
      unfold periodicHypercubicEvenInfluenceWalkKernel
      calc
        _ =
            ∑ mid : PeriodicHypercubicEvenEdge H,
              ∑ tail : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
                influence target mid *
                  (if tail 0 = mid ∧ tail (Fin.last d) = source then
                    periodicHypercubicEvenInfluenceWalkWeight H d influence tail
                  else 0) := by
          apply Finset.sum_congr rfl
          intro mid _
          rw [Finset.mul_sum]
        _ =
            ∑ tail : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
              ∑ mid : PeriodicHypercubicEvenEdge H,
                influence target mid *
                  (if tail 0 = mid ∧ tail (Fin.last d) = source then
                    periodicHypercubicEvenInfluenceWalkWeight H d influence tail
                  else 0) := by
          rw [Finset.sum_comm]
        _ =
            ∑ tail : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
              if tail (Fin.last d) = source then
                influence target (tail 0) *
                  periodicHypercubicEvenInfluenceWalkWeight H d influence tail
              else 0 := by
          apply Finset.sum_congr rfl
          intro tail _
          rw [Finset.sum_eq_single (tail 0)]
          · by_cases hlast : tail (Fin.last d) = source <;> simp [hlast]
          · intro mid _ hmid
            have hne : tail 0 ≠ mid := by
              exact fun h => hmid h.symm
            simp [hne]
          · intro hmem
            exact False.elim (hmem (Finset.mem_univ (tail 0)))

/-- The endpoint-constrained explicit finite walk kernel is exactly the
recursive finite influence iterate kernel. -/
theorem periodicHypercubicEvenInfluenceWalkKernel_eq_finiteInfluenceIterateKernel
    (H d : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (target source : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenInfluenceWalkKernel H d influence target source =
      finiteInfluenceIterateKernel influence d target source := by
  classical
  induction d generalizing target source with
  | zero =>
      rw [periodicHypercubicEvenInfluenceWalkKernel_zero]
      simp [finiteInfluenceIterateKernel]
  | succ d ih =>
      rw [periodicHypercubicEvenInfluenceWalkKernel_succ]
      simp only [finiteInfluenceIterateKernel]
      apply Finset.sum_congr rfl
      intro mid _
      rw [ih]

/-- Actual plaquette-local support separation kills the recursive finite
influence iterate below the separation distance. -/
theorem finiteInfluenceIterateKernel_eq_zero_of_supportsSeparatedBy
    (H D d : ℕ)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (hLocal :
      ∀ target source : PeriodicHypercubicEvenEdge H,
        influence target source ≠ 0 →
          periodicHypercubicEvenPlaquetteLocal H target source)
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (hd : d < D)
    (target : PeriodicHypercubicEvenEdge H)
    (htarget : target ∈ S)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    finiteInfluenceIterateKernel influence d target source = 0 := by
  rw [← periodicHypercubicEvenInfluenceWalkKernel_eq_finiteInfluenceIterateKernel]
  exact
    periodicHypercubicEvenInfluenceWalkKernel_eq_zero_of_supportsSeparatedBy
      H D d S T influence hLocal hsep hd target htarget source hsource

/-- Same-root scaling therefore makes every fixed sub-distance recursive sparse
influence iterate eventually vanish between the literal midpoint supports.  The
coupling sequence remains arbitrary. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_sparseActiveTVInfluenceIterateKernel_eq_zero_of_scaling
    (H : ℕ → ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 < r)
    (beta : ℕ → ℝ)
    (D : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ d : ℕ, d < D →
        ∀ target : PeriodicHypercubicEvenEdge (H n),
          target ∈
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
              (H n) latticeSpacing n J →
          ∀ source : PeriodicHypercubicEvenEdge (H n),
            source ∈
              periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
                (H n) latticeSpacing n J r →
            finiteInfluenceIterateKernel
              (fun target source =>
                periodicHypercubicSpecialUnitarySparseActiveTVInfluence
                  (PeriodicHypercubicEvenSideLength (H n)) (beta n) target source)
              d target source = 0 := by
  have hWalk :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_sparseActiveTVInfluenceWalkKernel_eq_zero_of_scaling
      H latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero hreach
      J hJ r hr beta D
  filter_upwards [hWalk] with n hn
  intro d hd target htarget source hsource
  rw [← periodicHypercubicEvenInfluenceWalkKernel_eq_finiteInfluenceIterateKernel]
  exact hn d hd target htarget source hsource

/-- Under the explicit finite-volume threshold, the explicit walk kernel of the
actual periodic compact `SU(N)` Dobrushin carrier satisfies the same coefficient
power bound as the recursive iterate. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influenceWalkKernel_le_pow
    (H N : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (d : ℕ)
    (target source : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenInfluenceWalkKernel H d
        (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
          (PeriodicHypercubicEvenSideLength H) N
          (by
            simp [PeriodicHypercubicEvenSideLength]
            omega)
          hN beta hBeta hThreshold).influence
        target source ≤
      (18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ d := by
  rw [periodicHypercubicEvenInfluenceWalkKernel_eq_finiteInfluenceIterateKernel]
  exact
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influenceIterateKernel_le_pow
      H N hH hN beta hBeta hThreshold d target source

/-- Under the same explicit threshold, actual support separation also kills the
recursive current compact `SU(N)` Dobrushin iterate below the support distance. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influenceIterateKernel_eq_zero_of_supportsSeparatedBy
    (H N D d : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (hd : d < D)
    (target : PeriodicHypercubicEvenEdge H)
    (htarget : target ∈ S)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    finiteInfluenceIterateKernel
      (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold).influence
      d target source = 0 := by
  rw [← periodicHypercubicEvenInfluenceWalkKernel_eq_finiteInfluenceIterateKernel]
  exact
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influenceWalkKernel_eq_zero_of_supportsSeparatedBy
      H N D d hH hN beta hBeta hThreshold S T hsep hd
      target htarget source hsource

end

end MathlibAnalytic
end MGAP4D