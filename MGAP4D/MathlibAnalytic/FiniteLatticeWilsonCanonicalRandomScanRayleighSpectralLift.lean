import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalHamiltonianEigenvalueBound
import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalRandomScanRayleigh
import MGAP4D.MathlibAnalytic.SymmetricEigenvalueUpperBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical random-scan operator on the Gibbs Hilbert carrier intertwines
with the concrete random-scan heat-bath sweep on observables. -/
theorem finite_lattice_gibbsCanonicalRandomScanLinearMap_embed
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ) :
    L.gibbsCanonicalRandomScanLinearMap
        (L.gibbsHilbertEmbedLinearMap f) =
      L.gibbsHilbertEmbedLinearMap
        (L.randomScanHeatBathSweep f) := by
  rw [finite_lattice_gibbsCanonicalRandomScanLinearMap_apply,
    finite_lattice_gibbsHeatBathHamiltonianLinearMap_apply,
    finite_lattice_gibbsHilbert_observe_embed,
    finite_lattice_singleLinkHeatBathHamiltonianObservable_eq_edgeCard_sub_randomScan
      L hEdge f]
  have hCard : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hEdge
  calc
    L.gibbsHilbertEmbedLinearMap f -
          (Fintype.card L.Edge : ℝ)⁻¹ •
            L.gibbsHilbertEmbedLinearMap
              ((Fintype.card L.Edge : ℝ) • f -
                (Fintype.card L.Edge : ℝ) •
                  L.randomScanHeatBathSweep f) =
        L.gibbsHilbertEmbedLinearMap
          (f - (Fintype.card L.Edge : ℝ)⁻¹ •
            ((Fintype.card L.Edge : ℝ) • f -
              (Fintype.card L.Edge : ℝ) •
                L.randomScanHeatBathSweep f)) := by
      rw [map_sub, map_smul]
    _ = L.gibbsHilbertEmbedLinearMap
        (L.randomScanHeatBathSweep f) := by
      apply congrArg L.gibbsHilbertEmbedLinearMap
      ext A
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hCard]
      ring

/-- The canonical Gibbs-Hilbert random-scan operator is symmetric. -/
theorem finite_lattice_gibbsCanonicalRandomScanLinearMap_isSymmetric
    (L : FiniteLatticeWilsonSystem) :
    L.gibbsCanonicalRandomScanLinearMap.IsSymmetric := by
  unfold FiniteLatticeWilsonSystem.gibbsCanonicalRandomScanLinearMap
  exact LinearMap.IsSymmetric.id.sub
    (LinearMap.IsSymmetric.smul (by simp)
      (finite_lattice_gibbsHeatBathHamiltonianLinearMap_isSymmetric L))

/-- The canonical Gibbs-Hilbert random-scan operator fixes the vacuum. -/
theorem finite_lattice_gibbsCanonicalRandomScanLinearMap_vacuum
    (L : FiniteLatticeWilsonSystem) :
    L.gibbsCanonicalRandomScanLinearMap L.gibbsHilbertVacuum =
      L.gibbsHilbertVacuum := by
  rw [finite_lattice_gibbsCanonicalRandomScanLinearMap_apply,
    finite_lattice_gibbsHeatBathHamiltonianLinearMap_vacuum]
  simp

/-- Symmetry and vacuum preservation imply invariance of the physical centered
sector under the canonical random-scan operator. -/
theorem finite_lattice_gibbsCanonicalRandomScanLinearMap_preserves_vacuumOrthogonal
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    L.gibbsCanonicalRandomScanLinearMap x ∈
      finiteVacuumOrthogonal L.gibbsHilbertVacuum := by
  rw [finite_wilson_mem_vacuumOrthogonal_iff]
  have hOrth : inner ℝ L.gibbsHilbertVacuum x = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      L.gibbsHilbertVacuum x).mp hx
  calc
    inner ℝ L.gibbsHilbertVacuum
        (L.gibbsCanonicalRandomScanLinearMap x) =
      inner ℝ (L.gibbsCanonicalRandomScanLinearMap x)
        L.gibbsHilbertVacuum := real_inner_comm _ _
    _ = inner ℝ x
        (L.gibbsCanonicalRandomScanLinearMap L.gibbsHilbertVacuum) :=
      (finite_lattice_gibbsCanonicalRandomScanLinearMap_isSymmetric L)
        x L.gibbsHilbertVacuum
    _ = inner ℝ x L.gibbsHilbertVacuum := by
      rw [finite_lattice_gibbsCanonicalRandomScanLinearMap_vacuum]
    _ = inner ℝ L.gibbsHilbertVacuum x := real_inner_comm _ _
    _ = 0 := hOrth

/-- Restriction of the canonical random-scan operator to the centered Gibbs
Hilbert sector. -/
noncomputable def
    FiniteLatticeWilsonSystem.gibbsCanonicalRandomScanRestrictedLinearMap
    (L : FiniteLatticeWilsonSystem) :
    finiteVacuumOrthogonal L.gibbsHilbertVacuum →ₗ[ℝ]
      finiteVacuumOrthogonal L.gibbsHilbertVacuum :=
  L.gibbsCanonicalRandomScanLinearMap.restrict
    (finite_lattice_gibbsCanonicalRandomScanLinearMap_preserves_vacuumOrthogonal L)

/-- The centered restriction of canonical random scan remains symmetric. -/
theorem finite_lattice_gibbsCanonicalRandomScanRestrictedLinearMap_isSymmetric
    (L : FiniteLatticeWilsonSystem) :
    L.gibbsCanonicalRandomScanRestrictedLinearMap.IsSymmetric :=
  (finite_lattice_gibbsCanonicalRandomScanLinearMap_isSymmetric L).restrict_invariant
    (finite_lattice_gibbsCanonicalRandomScanLinearMap_preserves_vacuumOrthogonal L)

/-- Every nonzero eigenvector of the centered Gibbs-Hilbert random-scan
restriction inherits the canonical Dobrushin eigenvalue bound. -/
theorem finite_lattice_gibbsCanonicalRandomScanRestricted_eigenvalue_abs_le_rate
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : finiteVacuumOrthogonal L.gibbsHilbertVacuum)
    (r : ℝ)
    (hx : x ≠ 0)
    (hEigen : L.gibbsCanonicalRandomScanRestrictedLinearMap x = r • x) :
    |r| ≤ finiteLatticeWilsonDobrushinRandomScanRate L D := by
  let f : L.Configuration → ℝ :=
    L.gibbsHilbertObserveLinearMap (x : L.GibbsHilbertSpace)
  have hOrth :
      inner ℝ L.gibbsHilbertVacuum (x : L.GibbsHilbertSpace) = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      L.gibbsHilbertVacuum (x : L.GibbsHilbertSpace)).mp x.property
  have hMean : L.gibbsExpectationReal f = 0 := by
    rw [← finite_lattice_gibbsHilbert_inner_vacuum_embed L f,
      finite_lattice_gibbsHilbert_embed_observe L
        (x : L.GibbsHilbertSpace)]
    exact hOrth
  have hf : f ≠ 0 := by
    intro hf
    apply hx
    apply Subtype.ext
    change (x : L.GibbsHilbertSpace) = 0
    calc
      (x : L.GibbsHilbertSpace) =
          L.gibbsHilbertEmbedLinearMap f :=
        (finite_lattice_gibbsHilbert_embed_observe L
          (x : L.GibbsHilbertSpace)).symm
      _ = 0 := by simp [hf]
  have hEigenHilbert :
      L.gibbsCanonicalRandomScanLinearMap
          (x : L.GibbsHilbertSpace) =
        r • (x : L.GibbsHilbertSpace) := by
    simpa [FiniteLatticeWilsonSystem.gibbsCanonicalRandomScanRestrictedLinearMap]
      using congrArg
        (fun y : finiteVacuumOrthogonal L.gibbsHilbertVacuum =>
          (y : L.GibbsHilbertSpace)) hEigen
  have hEmbeddedEigen :
      L.gibbsHilbertEmbedLinearMap
          (L.randomScanHeatBathSweep f) =
        r • L.gibbsHilbertEmbedLinearMap f := by
    rw [← finite_lattice_gibbsCanonicalRandomScanLinearMap_embed L hEdge f,
      finite_lattice_gibbsHilbert_embed_observe L
        (x : L.GibbsHilbertSpace)]
    exact hEigenHilbert
  have hObservableEigen :
      L.randomScanHeatBathSweep f = r • f := by
    calc
      L.randomScanHeatBathSweep f =
          L.gibbsHilbertObserveLinearMap
            (L.gibbsHilbertEmbedLinearMap
              (L.randomScanHeatBathSweep f)) :=
        (finite_lattice_gibbsHilbert_observe_embed L
          (L.randomScanHeatBathSweep f)).symm
      _ = L.gibbsHilbertObserveLinearMap
          (r • L.gibbsHilbertEmbedLinearMap f) :=
        congrArg (fun y : L.GibbsHilbertSpace =>
          L.gibbsHilbertObserveLinearMap y) hEmbeddedEigen
      _ = r • f := by
        rw [map_smul, finite_lattice_gibbsHilbert_observe_embed]
  exact
    finite_lattice_centered_randomScanHeatBathSweep_eigenvalue_abs_le_rate
      L f D hEdge r hMean hf hObservableEigen

/-- The Dobrushin eigenvalue bound lifts, through mathlib's orthonormal spectral
basis, to the full centered Gibbs-Hilbert Rayleigh bound. -/
theorem finite_lattice_gibbsCanonicalRandomScanRestricted_rayleigh_le_rate
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    inner ℝ (L.gibbsCanonicalRandomScanRestrictedLinearMap x) x ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D * ‖x‖ ^ 2 := by
  let hT :=
    finite_lattice_gibbsCanonicalRandomScanRestrictedLinearMap_isSymmetric L
  apply symmetric_quadraticForm_le_of_eigenvalues_le
    hT rfl (finiteLatticeWilsonDobrushinRandomScanRate L D) ?_ x
  intro i
  have hAbs :=
    finite_lattice_gibbsCanonicalRandomScanRestricted_eigenvalue_abs_le_rate
      L D hEdge
      (hT.eigenvectorBasis rfl i)
      (hT.eigenvalues rfl i)
      ((hT.eigenvectorBasis rfl).toBasis.ne_zero i)
      (hT.apply_eigenvectorBasis rfl i)
  exact le_trans (le_abs_self _) hAbs

/-- Canonical Dobrushin contraction for every centered observable, obtained from
the symmetric random-scan spectral decomposition rather than postulated as a
separate `L²` certificate. -/
theorem finite_lattice_centered_randomScanHeatBathSweep_rayleigh_le_dobrushinRate
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ)
    (hMean : L.gibbsExpectationReal f = 0) :
    L.gibbsPairingReal (L.randomScanHeatBathSweep f) f ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D *
        L.gibbsPairingReal f f := by
  have hx :
      L.gibbsHilbertEmbedLinearMap f ∈
        finiteVacuumOrthogonal L.gibbsHilbertVacuum := by
    rw [finite_wilson_mem_vacuumOrthogonal_iff,
      finite_lattice_gibbsHilbert_inner_vacuum_embed]
    exact hMean
  let x : finiteVacuumOrthogonal L.gibbsHilbertVacuum :=
    ⟨L.gibbsHilbertEmbedLinearMap f, hx⟩
  have hRayleigh :=
    finite_lattice_gibbsCanonicalRandomScanRestricted_rayleigh_le_rate
      L D hEdge x
  change
    inner ℝ
        (L.gibbsCanonicalRandomScanLinearMap
          (L.gibbsHilbertEmbedLinearMap f))
        (L.gibbsHilbertEmbedLinearMap f) ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D *
        ‖L.gibbsHilbertEmbedLinearMap f‖ ^ 2 at hRayleigh
  rw [finite_lattice_gibbsCanonicalRandomScanLinearMap_embed L hEdge f,
    finite_lattice_gibbsHilbert_inner_embed,
    finite_lattice_gibbsHilbert_norm_sq_embed] at hRayleigh
  exact hRayleigh

/-- The canonical variation construction now generates the actual centered
Dobrushin random-scan Rayleigh certificate required by the Hamiltonian gap
spine. -/
noncomputable def finiteLatticeWilsonCanonicalDobrushinRandomScanRayleighCertificate
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L :=
  { matrixData := D
    edgeCard_pos := hEdge
    centered_rayleigh_contraction :=
      finite_lattice_centered_randomScanHeatBathSweep_rayleigh_le_dobrushinRate
        L D hEdge }

end

end MathlibAnalytic
end MGAP4D
