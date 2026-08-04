import MGAP4D.MathlibAnalytic.FinitePositiveWeightHilbertRealization
import MGAP4D.MathlibAnalytic.SymmetricEigenvalueUpperBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every nonzero centered Hilbert eigenvector inherits the generic Dobrushin
eigenvalue bound. -/
theorem finitePositiveWeightHilbertRandomScanRestricted_eigenvalue_abs_le_rate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι)
    (x : finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight))
    (r : ℝ)
    (hx : x ≠ 0)
    (hEigen : finitePositiveWeightHilbertRandomScanRestrictedLinearMap
      weight hweight hCard x = r • x) :
    |r| ≤ finitePositiveWeightDobrushinRandomScanRate D := by
  let f : (ι → G) → ℝ :=
    finitePositiveWeightHilbertObserveLinearMap weight
      (x : FinitePositiveWeightHilbertSpace ι G)
  have hOrth :
      inner ℝ (finitePositiveWeightHilbertVacuum weight)
        (x : FinitePositiveWeightHilbertSpace ι G) = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      (finitePositiveWeightHilbertVacuum weight)
      (x : FinitePositiveWeightHilbertSpace ι G)).mp x.property
  have hCenter : finitePositiveWeightSum weight f = 0 := by
    rw [← finitePositiveWeightHilbert_inner_vacuum_embed
      weight hweight f,
      finitePositiveWeightHilbert_embed_observe weight hweight
        (x : FinitePositiveWeightHilbertSpace ι G)]
    exact hOrth
  have hf : f ≠ 0 := by
    intro hf
    apply hx
    apply Subtype.ext
    change (x : FinitePositiveWeightHilbertSpace ι G) = 0
    calc
      (x : FinitePositiveWeightHilbertSpace ι G) =
          finitePositiveWeightHilbertEmbedLinearMap weight f :=
        (finitePositiveWeightHilbert_embed_observe weight hweight
          (x : FinitePositiveWeightHilbertSpace ι G)).symm
      _ = 0 := by simp [hf]
  have hEigenHilbert :
      finitePositiveWeightHilbertRandomScanLinearMap weight
          (x : FinitePositiveWeightHilbertSpace ι G) =
        r • (x : FinitePositiveWeightHilbertSpace ι G) := by
    simpa [finitePositiveWeightHilbertRandomScanRestrictedLinearMap]
      using congrArg
        (fun y : finiteVacuumOrthogonal
            (finitePositiveWeightHilbertVacuum weight) =>
          (y : FinitePositiveWeightHilbertSpace ι G)) hEigen
  have hEmbeddedEigen :
      finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightRandomScanConditionalExpectation weight f) =
        r • finitePositiveWeightHilbertEmbedLinearMap weight f := by
    rw [← finitePositiveWeightHilbertRandomScanLinearMap_embed
      weight hweight f,
      finitePositiveWeightHilbert_embed_observe weight hweight
        (x : FinitePositiveWeightHilbertSpace ι G)]
    exact hEigenHilbert
  have hObservableEigen :
      finitePositiveWeightRandomScanConditionalExpectation weight f =
        r • f := by
    calc
      finitePositiveWeightRandomScanConditionalExpectation weight f =
          finitePositiveWeightHilbertObserveLinearMap weight
            (finitePositiveWeightHilbertEmbedLinearMap weight
              (finitePositiveWeightRandomScanConditionalExpectation weight f)) :=
        (finitePositiveWeightHilbert_observe_embed weight hweight
          (finitePositiveWeightRandomScanConditionalExpectation weight f)).symm
      _ = finitePositiveWeightHilbertObserveLinearMap weight
          (r • finitePositiveWeightHilbertEmbedLinearMap weight f) :=
        congrArg
          (fun y : FinitePositiveWeightHilbertSpace ι G =>
            finitePositiveWeightHilbertObserveLinearMap weight y)
          hEmbeddedEigen
      _ = r • f := by
        rw [map_smul, finitePositiveWeightHilbert_observe_embed]
  exact finitePositiveWeight_centered_randomScan_eigenvalue_abs_le_rate
    weight hweight f D hCard r hCenter hf hObservableEigen

/-- The Dobrushin eigenvalue bound lifts through the finite-dimensional
orthonormal spectral basis to the full centered Hilbert Rayleigh estimate. -/
theorem finitePositiveWeightHilbertRandomScanRestricted_rayleigh_le_rate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι)
    (x : finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight)) :
    inner ℝ
        (finitePositiveWeightHilbertRandomScanRestrictedLinearMap
          weight hweight hCard x) x ≤
      finitePositiveWeightDobrushinRandomScanRate D * ‖x‖ ^ 2 := by
  let hT := finitePositiveWeightHilbertRandomScanRestrictedLinearMap_isSymmetric
    weight hweight hCard
  apply symmetric_quadraticForm_le_of_eigenvalues_le
    hT rfl (finitePositiveWeightDobrushinRandomScanRate D) ?_ x
  intro i
  have hAbs :=
    finitePositiveWeightHilbertRandomScanRestricted_eigenvalue_abs_le_rate
      weight hweight D hCard
      (hT.eigenvectorBasis rfl i)
      (hT.eigenvalues rfl i)
      ((hT.eigenvectorBasis rfl).toBasis.ne_zero i)
      (hT.apply_eigenvectorBasis rfl i)
  exact le_trans (le_abs_self _) hAbs

/-- Generic centered Dobrushin random-scan Rayleigh contraction for an
arbitrary positive finite product weight. -/
theorem finitePositiveWeight_centered_randomScan_rayleigh_le_rate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι)
    (f : (ι → G) → ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0) :
    finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) f ≤
      finitePositiveWeightDobrushinRandomScanRate D *
        finitePositiveWeightPairing weight f f := by
  have hx :
      finitePositiveWeightHilbertEmbedLinearMap weight f ∈
        finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight) := by
    rw [finite_wilson_mem_vacuumOrthogonal_iff,
      finitePositiveWeightHilbert_inner_vacuum_embed weight hweight]
    exact hCenter
  let x : finiteVacuumOrthogonal
      (finitePositiveWeightHilbertVacuum weight) :=
    ⟨finitePositiveWeightHilbertEmbedLinearMap weight f, hx⟩
  have hRayleigh :=
    finitePositiveWeightHilbertRandomScanRestricted_rayleigh_le_rate
      weight hweight D hCard x
  change
    inner ℝ
        (finitePositiveWeightHilbertRandomScanLinearMap weight
          (finitePositiveWeightHilbertEmbedLinearMap weight f))
        (finitePositiveWeightHilbertEmbedLinearMap weight f) ≤
      finitePositiveWeightDobrushinRandomScanRate D *
        ‖finitePositiveWeightHilbertEmbedLinearMap weight f‖ ^ 2 at hRayleigh
  rw [finitePositiveWeightHilbertRandomScanLinearMap_embed weight hweight,
    finitePositiveWeightHilbert_inner_embed weight hweight,
    finitePositiveWeightHilbert_norm_sq_embed weight hweight] at hRayleigh
  exact hRayleigh

end

end MathlibAnalytic
end MGAP4D
