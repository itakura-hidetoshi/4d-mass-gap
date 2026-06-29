import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonRandomScanHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The oriented heat-bath Hamiltonian quadratic form is the random-scan
Rayleigh defect multiplied by the number of physical links. -/
theorem finite_oriented_singleLinkHeatBathHamiltonianObservable_quadraticForm_eq_randomScanDefect
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.singleLinkHeatBathHamiltonianObservable f) f =
      (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal f f -
          L.gibbsPairingReal (L.randomScanHeatBathSweep f) f) := by
  rw [finite_oriented_singleLinkHeatBathHamiltonianObservable_eq_card_mul_one_sub_randomScan
    L hEdge f]
  change
    L.gibbsPairingReal
        (fun A => (Fintype.card L.Edge : ℝ) *
          ((f - L.randomScanHeatBathSweep f) A)) f = _
  rw [finite_oriented_gibbsPairingReal_const_mul_left,
    finite_oriented_gibbsPairingReal_sub_left]

/-- The explicit analytic input needed beyond a strict oriented Dobrushin
matrix: centered Gibbs-pairing contraction of the exact random-scan sweep at
the canonical Dobrushin rate. -/
structure FiniteOrientedLatticeWilsonDobrushinRandomScanRayleighCertificate
    (L : FiniteOrientedLatticeWilsonSystem) where
  matrixData : FiniteOrientedLatticeWilsonDobrushinMatrixData L
  edgeCard_pos : 0 < Fintype.card L.Edge
  centered_rayleigh_contraction :
    ∀ f : L.Configuration → ℝ,
      L.gibbsExpectationReal f = 0 →
        L.gibbsPairingReal (L.randomScanHeatBathSweep f) f ≤
          finiteOrientedLatticeWilsonDobrushinRandomScanRate L matrixData *
            L.gibbsPairingReal f f

/-- The rate carried by an oriented Dobrushin-Rayleigh certificate belongs to
`[0,1)`. -/
theorem
    FiniteOrientedLatticeWilsonDobrushinRandomScanRayleighCertificate.rate_mem
    {L : FiniteOrientedLatticeWilsonSystem}
    (C : FiniteOrientedLatticeWilsonDobrushinRandomScanRayleighCertificate L) :
    finiteOrientedLatticeWilsonDobrushinRandomScanRate L C.matrixData ∈
      Set.Ico (0 : ℝ) 1 :=
  finite_oriented_dobrushinRandomScanRate_mem
    L C.matrixData C.edgeCard_pos

/-- Centered random-scan Rayleigh contraction yields the exact unnormalized
orientation-correct heat-bath coercivity `1 - alpha`. -/
theorem finite_oriented_dobrushinHeatBathGap_mul_self_le_hamiltonian
    (L : FiniteOrientedLatticeWilsonSystem)
    (C : FiniteOrientedLatticeWilsonDobrushinRandomScanRayleighCertificate L)
    (f : L.Configuration → ℝ)
    (hCentered : L.gibbsExpectationReal f = 0) :
    finiteOrientedLatticeWilsonDobrushinHeatBathGap C.matrixData *
        L.gibbsPairingReal f f ≤
      L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) f := by
  have hRayleigh := C.centered_rayleigh_contraction f hCentered
  have hCardNonneg : 0 ≤ (Fintype.card L.Edge : ℝ) := Nat.cast_nonneg _
  calc
    finiteOrientedLatticeWilsonDobrushinHeatBathGap C.matrixData *
        L.gibbsPairingReal f f =
      ((Fintype.card L.Edge : ℝ) *
        (1 - finiteOrientedLatticeWilsonDobrushinRandomScanRate
          L C.matrixData)) * L.gibbsPairingReal f f := by
        rw [finite_oriented_edgeCard_mul_one_sub_dobrushinRandomScanRate
          L C.matrixData C.edgeCard_pos]
    _ = (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal f f -
          finiteOrientedLatticeWilsonDobrushinRandomScanRate L C.matrixData *
            L.gibbsPairingReal f f) := by ring
    _ ≤ (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal f f -
          L.gibbsPairingReal (L.randomScanHeatBathSweep f) f) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_left hRayleigh (L.gibbsPairingReal f f))
        hCardNonneg
    _ = L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) f :=
      (finite_oriented_singleLinkHeatBathHamiltonianObservable_quadraticForm_eq_randomScanDefect
        L C.edgeCard_pos f).symm

end

end MathlibAnalytic
end MGAP4D
