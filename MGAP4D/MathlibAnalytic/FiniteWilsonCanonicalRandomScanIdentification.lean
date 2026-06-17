import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalRandomScanRayleigh
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanRayleighContraction
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumOrthogonalInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The concrete Wilson random-scan heat-bath sweep is exactly
`I - |E|⁻¹ H_HB` on observables, where `H_HB = ∑ₑ Qₑ`. -/
theorem finite_lattice_randomScanHeatBathSweep_eq_id_sub_inv_smul_hamiltonianObservable
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ) :
    L.randomScanHeatBathSweep f =
      f - (Fintype.card L.Edge : ℝ)⁻¹ •
        L.singleLinkHeatBathHamiltonianObservable f := by
  classical
  have hCardReal : (Fintype.card L.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  funext A
  rw [finite_lattice_randomScanHeatBathSweep_apply,
    finite_lattice_singleLinkHeatBathHamiltonianObservable_apply]
  simp only [FiniteLatticeWilsonSystem.singleLinkHeatBathOperator,
    finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_lattice_singleLinkHeatBathProjectionLinearMap_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hCardReal]
  ring

/-- On a Gibbs-embedded observable, the canonical Hilbert random-scan operator
is the Gibbs embedding of the concrete Wilson random-scan sweep. -/
theorem finite_lattice_gibbsCanonicalRandomScan_embed
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ) :
    L.gibbsCanonicalRandomScanLinearMap
        (L.gibbsHilbertEmbedLinearMap f) =
      L.gibbsHilbertEmbedLinearMap
        (L.randomScanHeatBathSweep f) := by
  rw [finite_lattice_gibbsCanonicalRandomScanLinearMap_apply,
    finite_lattice_gibbsHeatBathHamiltonianLinearMap_apply,
    finite_lattice_gibbsHilbert_observe_embed]
  calc
    L.gibbsHilbertEmbedLinearMap f -
        (Fintype.card L.Edge : ℝ)⁻¹ •
          L.gibbsHilbertEmbedLinearMap
            (L.singleLinkHeatBathHamiltonianObservable f) =
      L.gibbsHilbertEmbedLinearMap
        (f - (Fintype.card L.Edge : ℝ)⁻¹ •
          L.singleLinkHeatBathHamiltonianObservable f) := by
      symm
      rw [map_sub, map_smul]
    _ = L.gibbsHilbertEmbedLinearMap
        (L.randomScanHeatBathSweep f) := by
      apply congrArg L.gibbsHilbertEmbedLinearMap
      exact
        (finite_lattice_randomScanHeatBathSweep_eq_id_sub_inv_smul_hamiltonianObservable
          L hEdge f).symm

/-- The canonical Hilbert random-scan operator is the square-root-density
transport of the concrete Wilson random-scan sweep. -/
theorem finite_lattice_gibbsCanonicalRandomScan_eq_embed_randomScan_observe
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : L.GibbsHilbertSpace) :
    L.gibbsCanonicalRandomScanLinearMap x =
      L.gibbsHilbertEmbedLinearMap
        (L.randomScanHeatBathSweep
          (L.gibbsHilbertObserveLinearMap x)) := by
  calc
    L.gibbsCanonicalRandomScanLinearMap x =
        L.gibbsCanonicalRandomScanLinearMap
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap x)) := by
      rw [finite_lattice_gibbsHilbert_embed_observe]
    _ = L.gibbsHilbertEmbedLinearMap
        (L.randomScanHeatBathSweep
          (L.gibbsHilbertObserveLinearMap x)) :=
      finite_lattice_gibbsCanonicalRandomScan_embed
        L hEdge (L.gibbsHilbertObserveLinearMap x)

/-- The Hilbert-space Rayleigh pairing of the canonical scan is exactly the
finite Gibbs pairing of the concrete Wilson random-scan sweep. -/
theorem finite_lattice_gibbsCanonicalRandomScan_inner_eq_gibbsPairing
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : L.GibbsHilbertSpace) :
    inner ℝ (L.gibbsCanonicalRandomScanLinearMap x) x =
      L.gibbsPairingReal
        (L.randomScanHeatBathSweep
          (L.gibbsHilbertObserveLinearMap x))
        (L.gibbsHilbertObserveLinearMap x) := by
  calc
    inner ℝ (L.gibbsCanonicalRandomScanLinearMap x) x =
        inner ℝ
          (L.gibbsHilbertEmbedLinearMap
            (L.randomScanHeatBathSweep
              (L.gibbsHilbertObserveLinearMap x)))
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap x)) := by
      rw [finite_lattice_gibbsCanonicalRandomScan_eq_embed_randomScan_observe,
        finite_lattice_gibbsHilbert_embed_observe]
    _ = L.gibbsPairingReal
        (L.randomScanHeatBathSweep
          (L.gibbsHilbertObserveLinearMap x))
        (L.gibbsHilbertObserveLinearMap x) :=
      finite_lattice_gibbsHilbert_inner_embed L _ _

/-- The squared Hilbert norm is the Gibbs squared norm of the recovered
observable. -/
theorem finite_lattice_gibbsHilbert_norm_sq_eq_gibbsPairing_observe
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    ‖x‖ ^ 2 =
      L.gibbsPairingReal
        (L.gibbsHilbertObserveLinearMap x)
        (L.gibbsHilbertObserveLinearMap x) := by
  calc
    ‖x‖ ^ 2 =
        ‖L.gibbsHilbertEmbedLinearMap
          (L.gibbsHilbertObserveLinearMap x)‖ ^ 2 := by
      rw [finite_lattice_gibbsHilbert_embed_observe]
    _ = L.gibbsPairingReal
        (L.gibbsHilbertObserveLinearMap x)
        (L.gibbsHilbertObserveLinearMap x) :=
      finite_lattice_gibbsHilbert_norm_sq_embed L _

/-- Recovering an observable from a Gibbs Hilbert vector converts its Gibbs
expectation into the Hilbert pairing with the square-root-density vacuum. -/
theorem finite_lattice_gibbsExpectationReal_observe_eq_inner_vacuum
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    L.gibbsExpectationReal (L.gibbsHilbertObserveLinearMap x) =
      inner ℝ L.gibbsHilbertVacuum x := by
  calc
    L.gibbsExpectationReal (L.gibbsHilbertObserveLinearMap x) =
        inner ℝ L.gibbsHilbertVacuum
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap x)) :=
      (finite_lattice_gibbsHilbert_inner_vacuum_embed
        L (L.gibbsHilbertObserveLinearMap x)).symm
    _ = inner ℝ L.gibbsHilbertVacuum x := by
      rw [finite_lattice_gibbsHilbert_embed_observe]

/-- Vacuum-orthogonal Gibbs Hilbert vectors recover precisely mean-zero
observables. -/
theorem finite_lattice_gibbsExpectationReal_observe_eq_zero_of_mem_vacuumOrthogonal
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    L.gibbsExpectationReal (L.gibbsHilbertObserveLinearMap x) = 0 := by
  rw [finite_lattice_gibbsExpectationReal_observe_eq_inner_vacuum]
  exact
    (finite_wilson_mem_vacuumOrthogonal_iff
      L.gibbsHilbertVacuum x).mp hx

/-- The centered observable-side random-scan Rayleigh certificate from the
finite Wilson Gibbs system generates the canonical Hilbert-space certificate. -/
noncomputable def
    FiniteLatticeWilsonRandomScanRayleighContractionData.toCanonicalData
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonRandomScanRayleighContractionData L) :
    FiniteLatticeWilsonCanonicalRandomScanRayleighData L :=
  { edgeCard_pos := R.edgeCard_pos
    contractionRate := R.contractionRate
    contractionRate_nonneg := R.contractionRate_nonneg
    contractionRate_lt_one := R.contractionRate_lt_one
    rayleigh_contraction := by
      intro x hx
      rw [finite_lattice_gibbsCanonicalRandomScan_inner_eq_gibbsPairing
          L R.edgeCard_pos x,
        finite_lattice_gibbsHilbert_norm_sq_eq_gibbsPairing_observe]
      exact R.centered_rayleigh_contraction
        (L.gibbsHilbertObserveLinearMap x)
        (finite_lattice_gibbsExpectationReal_observe_eq_zero_of_mem_vacuumOrthogonal
          L x hx)
    exactGap_le_edgeCard_mul_one_sub_rate :=
      R.exactGap_le_edgeCard_mul_one_sub_rate }

/-- Centered concrete Wilson random-scan Rayleigh contraction implies the
canonical finite-volume Hamiltonian lower bound on the excitation sector. -/
theorem finite_lattice_randomScanRayleigh_implies_hamiltonian_gap
    (L : FiniteLatticeWilsonSystem)
    (R : FiniteLatticeWilsonRandomScanRayleighContractionData L)
    (x : L.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x :=
  finite_lattice_canonicalRandomScanRayleigh_implies_hamiltonian_gap
    L R.toCanonicalData x hx

end

end MathlibAnalytic
end MGAP4D
