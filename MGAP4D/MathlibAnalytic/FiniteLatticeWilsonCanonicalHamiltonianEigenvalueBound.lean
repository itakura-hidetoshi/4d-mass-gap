import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalRandomScanEigenvalueBound
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanRayleighContraction
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanScale

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A random-scan eigenobservable is an observable heat-bath Hamiltonian
eigenobservable with eigenvalue `|E| * (1 - r)`. -/
theorem finite_lattice_singleLinkHeatBathHamiltonianObservable_eigen_of_randomScan
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hEdge : 0 < Fintype.card L.Edge)
    (r : ℝ)
    (hEigen : L.randomScanHeatBathSweep f = r • f) :
    L.singleLinkHeatBathHamiltonianObservable f =
      ((Fintype.card L.Edge : ℝ) * (1 - r)) • f := by
  rw [finite_lattice_singleLinkHeatBathHamiltonianObservable_eq_edgeCard_sub_randomScan
    L hEdge f, hEigen]
  ext A
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The same random-scan eigenobservable gives an eigenvector of the concrete
Gibbs-Hilbert heat-bath Hamiltonian after multiplication by `sqrt(μ)`. -/
theorem finite_lattice_gibbsHeatBathHamiltonian_embed_eigen_of_randomScan
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hEdge : 0 < Fintype.card L.Edge)
    (r : ℝ)
    (hEigen : L.randomScanHeatBathSweep f = r • f) :
    L.gibbsHeatBathHamiltonianLinearMap
        (L.gibbsHilbertEmbedLinearMap f) =
      ((Fintype.card L.Edge : ℝ) * (1 - r)) •
        L.gibbsHilbertEmbedLinearMap f := by
  rw [finite_lattice_gibbsHeatBathHamiltonianLinearMap_apply,
    finite_lattice_gibbsHilbert_observe_embed,
    finite_lattice_singleLinkHeatBathHamiltonianObservable_eigen_of_randomScan
      L f hEdge r hEigen,
    map_smul]

/-- Every nonzero centered random-scan eigenobservable therefore produces an
observable heat-bath Hamiltonian eigenvalue at least the Dobrushin heat-bath
gap `1 - α`. -/
theorem finite_lattice_centered_heatBathHamiltonian_eigenvalue_ge_dobrushinGap
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (r : ℝ)
    (hMean : L.gibbsExpectationReal f = 0)
    (hNonzero : f ≠ 0)
    (hEigen : L.randomScanHeatBathSweep f = r • f) :
    finiteLatticeWilsonDobrushinHeatBathGap D ≤
      (Fintype.card L.Edge : ℝ) * (1 - r) := by
  have hAbs :
      |r| ≤ finiteLatticeWilsonDobrushinRandomScanRate L D :=
    finite_lattice_centered_randomScanHeatBathSweep_eigenvalue_abs_le_rate
      L f D hEdge r hMean hNonzero hEigen
  have hr : r ≤ finiteLatticeWilsonDobrushinRandomScanRate L D :=
    le_trans (le_abs_self r) hAbs
  rw [finite_lattice_edgeCard_mul_one_sub_dobrushinRandomScanRate
    L D hEdge]
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left hr 1)
    (Nat.cast_nonneg _)

end

end MathlibAnalytic
end MGAP4D
