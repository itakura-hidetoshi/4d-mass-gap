import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonRandomScanHilbertOperator
import MGAP4D.MathlibAnalytic.SymmetricEigenvalueUpperBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem finite_oriented_gibbsRandomScanLinearMap_preserves_vacuumOrthogonal
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : L.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    L.gibbsRandomScanLinearMap x ∈
      finiteVacuumOrthogonal L.gibbsHilbertVacuum := by
  rw [finite_wilson_mem_vacuumOrthogonal_iff]
  have hOrth : inner ℝ L.gibbsHilbertVacuum x = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      L.gibbsHilbertVacuum x).mp hx
  calc
    inner ℝ L.gibbsHilbertVacuum (L.gibbsRandomScanLinearMap x) =
      inner ℝ (L.gibbsRandomScanLinearMap x) L.gibbsHilbertVacuum :=
        real_inner_comm _ _
    _ = inner ℝ x (L.gibbsRandomScanLinearMap L.gibbsHilbertVacuum) :=
      (finite_oriented_gibbsRandomScanLinearMap_isSymmetric L)
        x L.gibbsHilbertVacuum
    _ = inner ℝ x L.gibbsHilbertVacuum := by
      rw [finite_oriented_gibbsRandomScanLinearMap_vacuum L hEdge]
    _ = inner ℝ L.gibbsHilbertVacuum x := real_inner_comm _ _
    _ = 0 := hOrth

noncomputable def
    FiniteOrientedLatticeWilsonSystem.gibbsRandomScanRestrictedLinearMap
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteVacuumOrthogonal L.gibbsHilbertVacuum →ₗ[ℝ]
      finiteVacuumOrthogonal L.gibbsHilbertVacuum :=
  L.gibbsRandomScanLinearMap.restrict
    (finite_oriented_gibbsRandomScanLinearMap_preserves_vacuumOrthogonal
      L hEdge)

theorem finite_oriented_gibbsRandomScanRestrictedLinearMap_isSymmetric
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    (L.gibbsRandomScanRestrictedLinearMap hEdge).IsSymmetric :=
  (finite_oriented_gibbsRandomScanLinearMap_isSymmetric L).restrict_invariant
    (finite_oriented_gibbsRandomScanLinearMap_preserves_vacuumOrthogonal
      L hEdge)

theorem finite_oriented_gibbsRandomScanRestricted_eigenvalue_abs_le_rate
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : finiteVacuumOrthogonal L.gibbsHilbertVacuum)
    (r : ℝ)
    (hx : x ≠ 0)
    (hEigen : L.gibbsRandomScanRestrictedLinearMap hEdge x = r • x) :
    |r| ≤ finiteOrientedLatticeWilsonDobrushinRandomScanRate L D := by
  let f : L.Configuration → ℝ :=
    L.gibbsHilbertObserveLinearMap (x : L.GibbsHilbertSpace)
  have hOrth :
      inner ℝ L.gibbsHilbertVacuum (x : L.GibbsHilbertSpace) = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      L.gibbsHilbertVacuum (x : L.GibbsHilbertSpace)).mp x.property
  have hMean : L.gibbsExpectationReal f = 0 := by
    rw [← finite_oriented_gibbsHilbert_inner_vacuum_embed L f,
      finite_oriented_gibbsHilbert_embed_observe L
        (x : L.GibbsHilbertSpace)]
    exact hOrth
  have hf : f ≠ 0 := by
    intro hf
    apply hx
    apply Subtype.ext
    change (x : L.GibbsHilbertSpace) = 0
    calc
      (x : L.GibbsHilbertSpace) = L.gibbsHilbertEmbedLinearMap f :=
        (finite_oriented_gibbsHilbert_embed_observe L
          (x : L.GibbsHilbertSpace)).symm
      _ = 0 := by simp [hf]
  have hEigenHilbert :
      L.gibbsRandomScanLinearMap (x : L.GibbsHilbertSpace) =
        r • (x : L.GibbsHilbertSpace) := by
    simpa [FiniteOrientedLatticeWilsonSystem.gibbsRandomScanRestrictedLinearMap]
      using congrArg
        (fun y : finiteVacuumOrthogonal L.gibbsHilbertVacuum =>
          (y : L.GibbsHilbertSpace)) hEigen
  have hEmbeddedEigen :
      L.gibbsHilbertEmbedLinearMap (L.randomScanHeatBathSweep f) =
        r • L.gibbsHilbertEmbedLinearMap f := by
    rw [← finite_oriented_gibbsRandomScanLinearMap_embed L f,
      finite_oriented_gibbsHilbert_embed_observe L
        (x : L.GibbsHilbertSpace)]
    exact hEigenHilbert
  have hObservableEigen :
      L.randomScanHeatBathSweep f = r • f := by
    calc
      L.randomScanHeatBathSweep f =
          L.gibbsHilbertObserveLinearMap
            (L.gibbsHilbertEmbedLinearMap
              (L.randomScanHeatBathSweep f)) :=
        (finite_oriented_gibbsHilbert_observe_embed L
          (L.randomScanHeatBathSweep f)).symm
      _ = L.gibbsHilbertObserveLinearMap
          (r • L.gibbsHilbertEmbedLinearMap f) :=
        congrArg (fun y : L.GibbsHilbertSpace =>
          L.gibbsHilbertObserveLinearMap y) hEmbeddedEigen
      _ = r • f := by
        rw [map_smul, finite_oriented_gibbsHilbert_observe_embed]
  exact finite_oriented_centered_randomScanHeatBathSweep_eigenvalue_abs_le_rate
    L f D hEdge r hMean hf hObservableEigen

theorem finite_oriented_gibbsRandomScanRestricted_rayleigh_le_rate
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    inner ℝ (L.gibbsRandomScanRestrictedLinearMap hEdge x) x ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D * ‖x‖ ^ 2 := by
  let hT := finite_oriented_gibbsRandomScanRestrictedLinearMap_isSymmetric
    L hEdge
  apply symmetric_quadraticForm_le_of_eigenvalues_le
    hT rfl (finiteOrientedLatticeWilsonDobrushinRandomScanRate L D) ?_ x
  intro i
  have hAbs :=
    finite_oriented_gibbsRandomScanRestricted_eigenvalue_abs_le_rate
      L D hEdge
      (hT.eigenvectorBasis rfl i)
      (hT.eigenvalues rfl i)
      ((hT.eigenvectorBasis rfl).toBasis.ne_zero i)
      (hT.apply_eigenvectorBasis rfl i)
  exact le_trans (le_abs_self _) hAbs

theorem finite_oriented_centered_randomScanHeatBathSweep_rayleigh_le_dobrushinRate
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ)
    (hMean : L.gibbsExpectationReal f = 0) :
    L.gibbsPairingReal (L.randomScanHeatBathSweep f) f ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D *
        L.gibbsPairingReal f f := by
  have hx :
      L.gibbsHilbertEmbedLinearMap f ∈
        finiteVacuumOrthogonal L.gibbsHilbertVacuum := by
    rw [finite_wilson_mem_vacuumOrthogonal_iff,
      finite_oriented_gibbsHilbert_inner_vacuum_embed]
    exact hMean
  let x : finiteVacuumOrthogonal L.gibbsHilbertVacuum :=
    ⟨L.gibbsHilbertEmbedLinearMap f, hx⟩
  have hRayleigh :=
    finite_oriented_gibbsRandomScanRestricted_rayleigh_le_rate
      L D hEdge x
  change
    inner ℝ
        (L.gibbsRandomScanLinearMap
          (L.gibbsHilbertEmbedLinearMap f))
        (L.gibbsHilbertEmbedLinearMap f) ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D *
        ‖L.gibbsHilbertEmbedLinearMap f‖ ^ 2 at hRayleigh
  rw [finite_oriented_gibbsRandomScanLinearMap_embed,
    finite_oriented_gibbsHilbert_inner_embed,
    finite_oriented_gibbsHilbert_norm_sq_embed] at hRayleigh
  exact hRayleigh

noncomputable def finiteOrientedLatticeWilsonCanonicalDobrushinRandomScanRayleighCertificate
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    FiniteOrientedLatticeWilsonDobrushinRandomScanRayleighCertificate L :=
  { matrixData := D
    edgeCard_pos := hEdge
    centered_rayleigh_contraction :=
      finite_oriented_centered_randomScanHeatBathSweep_rayleigh_le_dobrushinRate
        L D hEdge }

end
end MathlibAnalytic
end MGAP4D
