import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalHeatBathHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical normalized random-scan operator on the concrete Gibbs Hilbert
carrier.  It is the Euler step `I - |E|⁻¹ H_HB` for the unnormalized heat-bath
Hamiltonian `H_HB = ∑ₑ Qₑ`. -/
noncomputable def FiniteLatticeWilsonSystem.gibbsCanonicalRandomScanLinearMap
    (L : FiniteLatticeWilsonSystem) :
    L.GibbsHilbertSpace →ₗ[ℝ] L.GibbsHilbertSpace :=
  (LinearMap.id : L.GibbsHilbertSpace →ₗ[ℝ] L.GibbsHilbertSpace) -
    (Fintype.card L.Edge : ℝ)⁻¹ •
      L.gibbsHeatBathHamiltonianLinearMap

@[simp] theorem finite_lattice_gibbsCanonicalRandomScanLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    L.gibbsCanonicalRandomScanLinearMap x =
      x - (Fintype.card L.Edge : ℝ)⁻¹ •
        L.gibbsHeatBathHamiltonianLinearMap x := by
  rfl

/-- For a nonempty edge set, the canonical heat-bath Hamiltonian is exactly
`|E|` times `I - P_scan`. -/
theorem finite_lattice_gibbsHeatBathHamiltonian_eq_edgeCard_smul_id_sub_randomScan
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : L.GibbsHilbertSpace) :
    L.gibbsHeatBathHamiltonianLinearMap x =
      (Fintype.card L.Edge : ℝ) •
        (x - L.gibbsCanonicalRandomScanLinearMap x) := by
  have hCardRealPos :
      (0 : ℝ) < (Fintype.card L.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  have hCardReal : (Fintype.card L.Edge : ℝ) ≠ 0 :=
    ne_of_gt hCardRealPos
  rw [finite_lattice_gibbsCanonicalRandomScanLinearMap_apply]
  rw [sub_sub_cancel_left, smul_smul,
    mul_inv_cancel₀ hCardReal, one_smul]

/-- Exact Rayleigh identity relating the canonical random-scan operator and the
unnormalized heat-bath Hamiltonian. -/
theorem finite_lattice_gibbsHeatBathHamiltonian_quadraticForm_eq_edgeCard_mul_randomScan_defect
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (x : L.GibbsHilbertSpace) :
    inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x =
      (Fintype.card L.Edge : ℝ) *
        (‖x‖ ^ 2 -
          inner ℝ (L.gibbsCanonicalRandomScanLinearMap x) x) := by
  have hVector := congrArg
    (fun y : L.GibbsHilbertSpace => inner ℝ y x)
    (finite_lattice_gibbsHeatBathHamiltonian_eq_edgeCard_smul_id_sub_randomScan
      L hEdge x)
  rw [real_inner_smul_left, inner_sub_left,
    real_inner_self_eq_norm_sq] at hVector
  exact hVector

/-- Rayleigh contraction data for the canonical normalized random-scan
operator on the vacuum-orthogonal sector. -/
structure FiniteLatticeWilsonCanonicalRandomScanRayleighData
    (L : FiniteLatticeWilsonSystem) where
  edgeCard_pos : 0 < Fintype.card L.Edge
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  rayleigh_contraction :
    ∀ x : L.GibbsHilbertSpace,
      x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum →
        inner ℝ (L.gibbsCanonicalRandomScanLinearMap x) x ≤
          contractionRate * ‖x‖ ^ 2
  exactGap_le_edgeCard_mul_one_sub_rate :
    exactGapValueReal ≤
      (Fintype.card L.Edge : ℝ) * (1 - contractionRate)

/-- Canonical random-scan Rayleigh contraction implies the exact lower bound
for the heat-bath Hamiltonian on the vacuum-orthogonal sector. -/
theorem finite_lattice_canonicalRandomScanRayleigh_implies_hamiltonian_gap
    (L : FiniteLatticeWilsonSystem)
    (R : FiniteLatticeWilsonCanonicalRandomScanRayleighData L)
    (x : L.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x := by
  have hNormSq : 0 ≤ ‖x‖ ^ 2 := sq_nonneg ‖x‖
  have hCardNonneg : 0 ≤ (Fintype.card L.Edge : ℝ) :=
    Nat.cast_nonneg _
  have hRayleigh := R.rayleigh_contraction x hx
  calc
    exactGapValueReal * ‖x‖ ^ 2 ≤
        ((Fintype.card L.Edge : ℝ) *
          (1 - R.contractionRate)) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        R.exactGap_le_edgeCard_mul_one_sub_rate hNormSq
    _ = (Fintype.card L.Edge : ℝ) *
        (‖x‖ ^ 2 - R.contractionRate * ‖x‖ ^ 2) := by
      ring
    _ ≤ (Fintype.card L.Edge : ℝ) *
        (‖x‖ ^ 2 -
          inner ℝ (L.gibbsCanonicalRandomScanLinearMap x) x) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_left hRayleigh (‖x‖ ^ 2)) hCardNonneg
    _ = inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x :=
      (finite_lattice_gibbsHeatBathHamiltonian_quadraticForm_eq_edgeCard_mul_randomScan_defect
        L R.edgeCard_pos x).symm

/-- Package canonical random-scan Rayleigh contraction directly as the
established vacuum-orthogonal Hamiltonian gap data at one finite Wilson scale. -/
noncomputable def finiteWilsonCanonicalRandomScanRayleighDerivedGapData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (R : FiniteLatticeWilsonCanonicalRandomScanRayleighData (W.system i)) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  { StateSpace := (W.system i).GibbsHilbertSpace
    stateNormedAddCommGroup := inferInstance
    stateInnerProductSpace := inferInstance
    stateFiniteDimensional := inferInstance
    vacuum := (W.system i).gibbsHilbertVacuum
    vacuum_norm := finite_lattice_gibbsHilbertVacuum_norm (W.system i)
    hamiltonian := fun _n =>
      (W.system i).gibbsHeatBathHamiltonianLinearMap
    hamiltonianSymmetric := fun _n =>
      finite_lattice_gibbsHeatBathHamiltonianLinearMap_isSymmetric
        (W.system i)
    vacuumEnergyZero := fun _n =>
      finite_lattice_gibbsHeatBathHamiltonianLinearMap_vacuum
        (W.system i)
    hamiltonianQuadraticFormLowerBoundOnVacuumOrthogonal := by
      intro _n x hx
      exact
        finite_lattice_canonicalRandomScanRayleigh_implies_hamiltonian_gap
          (W.system i) R x hx
    ExcitedDimension :=
      Module.finrank ℝ
        (finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum)
    excitedFinrank := rfl }

/-- Every excitation-sector eigenvalue of the canonical finite Wilson
heat-bath Hamiltonian inherits the exact lower bound from random-scan Rayleigh
contraction. -/
theorem finite_wilson_canonicalRandomScanRayleigh_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (R : FiniteLatticeWilsonCanonicalRandomScanRayleighData (W.system i))
    (j : Fin
      (Module.finrank ℝ
        (finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum))) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (finiteWilsonCanonicalRandomScanRayleighDerivedGapData W i R).toVacuumOrthogonalGapData
        0).eigenvalues rfl j :=
  finite_wilson_derived_invariance_restricted_eigenvalues_ge_exactGap
    (finiteWilsonCanonicalRandomScanRayleighDerivedGapData W i R) 0 j

end

end MathlibAnalytic
end MGAP4D
