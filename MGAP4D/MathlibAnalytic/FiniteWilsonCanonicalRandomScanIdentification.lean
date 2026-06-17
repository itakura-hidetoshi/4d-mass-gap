import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalRandomScanRayleigh
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonRandomScanHeatBathSweep

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

/-- Concrete observable-side Rayleigh contraction data for the actual finite
Wilson random-scan heat-bath sweep. -/
structure FiniteLatticeWilsonConcreteRandomScanRayleighData
    (L : FiniteLatticeWilsonSystem) where
  edgeCard_pos : 0 < Fintype.card L.Edge
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  gibbsPairing_randomScan_le :
    ∀ f : L.Configuration → ℝ,
      L.gibbsPairingReal (L.randomScanHeatBathSweep f) f ≤
        contractionRate * L.gibbsPairingReal f f
  exactGap_le_edgeCard_mul_one_sub_rate :
    exactGapValueReal ≤
      (Fintype.card L.Edge : ℝ) * (1 - contractionRate)

/-- Concrete observable-side random-scan contraction generates the canonical
Hilbert-space Rayleigh package. -/
noncomputable def
    FiniteLatticeWilsonConcreteRandomScanRayleighData.toCanonicalData
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonConcreteRandomScanRayleighData L) :
    FiniteLatticeWilsonCanonicalRandomScanRayleighData L :=
  { edgeCard_pos := R.edgeCard_pos
    contractionRate := R.contractionRate
    contractionRate_nonneg := R.contractionRate_nonneg
    contractionRate_lt_one := R.contractionRate_lt_one
    rayleigh_contraction := by
      intro x _hx
      rw [finite_lattice_gibbsCanonicalRandomScan_inner_eq_gibbsPairing
          L R.edgeCard_pos x,
        finite_lattice_gibbsHilbert_norm_sq_eq_gibbsPairing_observe]
      exact R.gibbsPairing_randomScan_le
        (L.gibbsHilbertObserveLinearMap x)
    exactGap_le_edgeCard_mul_one_sub_rate :=
      R.exactGap_le_edgeCard_mul_one_sub_rate }

/-- Concrete Wilson random-scan Rayleigh contraction implies the canonical
finite-volume Hamiltonian lower bound on the excitation sector. -/
theorem finite_lattice_concreteRandomScanRayleigh_implies_hamiltonian_gap
    (L : FiniteLatticeWilsonSystem)
    (R : FiniteLatticeWilsonConcreteRandomScanRayleighData L)
    (x : L.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x :=
  finite_lattice_canonicalRandomScanRayleigh_implies_hamiltonian_gap
    L R.toCanonicalData x hx

end

end MathlibAnalytic
end MGAP4D
