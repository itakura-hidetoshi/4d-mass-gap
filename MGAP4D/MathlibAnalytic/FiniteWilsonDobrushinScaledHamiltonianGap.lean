import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanScale
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumOrthogonalDerivedInvarianceGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A certified centered Dobrushin random-scan contraction gives the
unnormalized heat-bath Poincare inequality with coefficient `1 - alpha`. -/
theorem finite_lattice_dobrushinHeatBathGap_mul_variance_le_dirichlet
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L)
    (f : L.Configuration → ℝ) :
    finiteLatticeWilsonDobrushinHeatBathGap C.matrixData *
        L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f := by
  let centered := L.gibbsCenteredObservable f
  have hCenteredMean : L.gibbsExpectationReal centered = 0 :=
    finite_lattice_gibbsExpectationReal_centered L f
  have hRayleigh :=
    C.centered_rayleigh_contraction centered hCenteredMean
  have hCardNonneg : 0 ≤ (Fintype.card L.Edge : ℝ) :=
    Nat.cast_nonneg _
  calc
    finiteLatticeWilsonDobrushinHeatBathGap C.matrixData *
        L.gibbsVarianceReal f =
      ((Fintype.card L.Edge : ℝ) *
        (1 - finiteLatticeWilsonDobrushinRandomScanRate L C.matrixData)) *
          L.gibbsVarianceReal f := by
      rw [finite_lattice_edgeCard_mul_one_sub_dobrushinRandomScanRate
        L C.matrixData C.edgeCard_pos]
    _ = (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal centered centered -
          finiteLatticeWilsonDobrushinRandomScanRate L C.matrixData *
            L.gibbsPairingReal centered centered) := by
      rw [finite_lattice_gibbsPairingReal_centered_self]
      ring
    _ ≤ (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal centered centered -
          L.gibbsPairingReal (L.randomScanHeatBathSweep centered) centered) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_left hRayleigh
          (L.gibbsPairingReal centered centered))
        hCardNonneg
    _ = L.singleLinkHeatBathDirichletForm centered :=
      (finite_lattice_singleLinkHeatBathDirichletForm_eq_edgeCard_mul_randomScanRayleighDefect
        L C.edgeCard_pos centered).symm
    _ = L.singleLinkHeatBathDirichletForm f :=
      finite_lattice_singleLinkHeatBathDirichletForm_centered L f

/-- After applying the explicit positive normalization scale, the Dobrushin
coercive estimate carries the repository's public exact-gap coefficient. -/
theorem finite_lattice_exactGap_mul_variance_le_dobrushinScale_mul_dirichlet
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L)
    (f : L.Configuration → ℝ) :
    exactGapValueReal * L.gibbsVarianceReal f ≤
      finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        L.singleLinkHeatBathDirichletForm f := by
  have hScaleNonneg :
      0 ≤ finiteLatticeWilsonDobrushinNormalizedScale C.matrixData :=
    le_of_lt (finite_lattice_dobrushinNormalizedScale_pos C.matrixData)
  calc
    exactGapValueReal * L.gibbsVarianceReal f =
        (finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
          finiteLatticeWilsonDobrushinHeatBathGap C.matrixData) *
            L.gibbsVarianceReal f := by
      rw [finite_lattice_dobrushinNormalizedScale_mul_heatBathGap]
    _ = finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        (finiteLatticeWilsonDobrushinHeatBathGap C.matrixData *
          L.gibbsVarianceReal f) := by
      ring
    _ ≤ finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        L.singleLinkHeatBathDirichletForm f :=
      mul_le_mul_of_nonneg_left
        (finite_lattice_dobrushinHeatBathGap_mul_variance_le_dirichlet
          L C f)
        hScaleNonneg

/-- The canonical finite Wilson heat-bath Hamiltonian rescaled by the explicit
Dobrushin-to-public-gap normalization factor. -/
noncomputable def
    FiniteLatticeWilsonSystem.gibbsDobrushinScaledHeatBathHamiltonianLinearMap
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L) :
    L.GibbsHilbertSpace →ₗ[ℝ] L.GibbsHilbertSpace :=
  finiteLatticeWilsonDobrushinNormalizedScale C.matrixData •
    L.gibbsHeatBathHamiltonianLinearMap

@[simp] theorem finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L)
    (x : L.GibbsHilbertSpace) :
    L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C x =
      finiteLatticeWilsonDobrushinNormalizedScale C.matrixData •
        L.gibbsHeatBathHamiltonianLinearMap x :=
  rfl

/-- The normalized Dobrushin heat-bath Hamiltonian remains symmetric. -/
theorem finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_isSymmetric
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L) :
    (L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C).IsSymmetric := by
  intro x y
  rw [finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply,
    finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply,
    real_inner_smul_left, real_inner_smul_right]
  exact congrArg
    (fun t : ℝ =>
      finiteLatticeWilsonDobrushinNormalizedScale C.matrixData * t)
    ((finite_lattice_gibbsHeatBathHamiltonianLinearMap_isSymmetric L) x y)

/-- The normalized Dobrushin heat-bath Hamiltonian annihilates the Gibbs
vacuum. -/
theorem finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_vacuum
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L) :
    L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C
        L.gibbsHilbertVacuum = 0 := by
  rw [finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply,
    finite_lattice_gibbsHeatBathHamiltonianLinearMap_vacuum]
  simp

/-- Its quadratic form is the explicitly normalized heat-bath Dirichlet form. -/
theorem finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_quadraticForm
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L)
    (x : L.GibbsHilbertSpace) :
    inner ℝ
        (L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C x) x =
      finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        L.singleLinkHeatBathDirichletForm
          (L.gibbsHilbertObserveLinearMap x) := by
  rw [finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply,
    real_inner_smul_left,
    finite_lattice_gibbsHeatBathHamiltonianLinearMap_quadraticForm]

/-- The normalized Dobrushin Hamiltonian has the public exact lower bound on
the physical vacuum-orthogonal sector. -/
theorem finite_lattice_dobrushinScaled_hamiltonian_gap_on_vacuumOrthogonal
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L)
    (x : L.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        (L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C x) x := by
  have hOrth : inner ℝ L.gibbsHilbertVacuum x = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      L.gibbsHilbertVacuum x).mp hx
  have hCentered : finiteVacuumCentered L.gibbsHilbertVacuum x = x := by
    unfold finiteVacuumCentered
    rw [hOrth]
    simp
  have hVar :
      L.gibbsVarianceReal (L.gibbsHilbertObserveLinearMap x) = ‖x‖ ^ 2 := by
    have h := finite_lattice_gibbsHilbert_vacuumCentered_norm_sq_observe L x
    rw [hCentered] at h
    exact h.symm
  calc
    exactGapValueReal * ‖x‖ ^ 2 =
        exactGapValueReal *
          L.gibbsVarianceReal (L.gibbsHilbertObserveLinearMap x) := by
      rw [hVar]
    _ ≤ finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        L.singleLinkHeatBathDirichletForm
          (L.gibbsHilbertObserveLinearMap x) :=
      finite_lattice_exactGap_mul_variance_le_dobrushinScale_mul_dirichlet
        L C (L.gibbsHilbertObserveLinearMap x)
    _ = inner ℝ
        (L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C x) x :=
      (finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_quadraticForm
        L C x).symm

/-- Package the normalized Dobrushin Hamiltonian as finite-volume
vacuum-orthogonal gap data. -/
noncomputable def finiteWilsonDobrushinScaledHamiltonianGapData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      (W.system i)) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  { StateSpace := (W.system i).GibbsHilbertSpace
    stateNormedAddCommGroup := inferInstance
    stateInnerProductSpace := inferInstance
    stateFiniteDimensional := inferInstance
    vacuum := (W.system i).gibbsHilbertVacuum
    vacuum_norm := finite_lattice_gibbsHilbertVacuum_norm (W.system i)
    hamiltonian := fun _n =>
      (W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap C
    hamiltonianSymmetric := fun _n =>
      finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_isSymmetric
        (W.system i) C
    vacuumEnergyZero := fun _n =>
      finite_lattice_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_vacuum
        (W.system i) C
    hamiltonianQuadraticFormLowerBoundOnVacuumOrthogonal := by
      intro _n x hx
      exact finite_lattice_dobrushinScaled_hamiltonian_gap_on_vacuumOrthogonal
        (W.system i) C x hx
    ExcitedDimension :=
      Module.finrank ℝ
        (finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum)
    excitedFinrank := rfl }

/-- Every excitation-sector eigenvalue of the normalized Dobrushin Hamiltonian
lies above the public exact gap. -/
theorem finite_wilson_dobrushinScaled_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      (W.system i))
    (j : Fin (finiteWilsonDobrushinScaledHamiltonianGapData W i C).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (finiteWilsonDobrushinScaledHamiltonianGapData W i C).toVacuumOrthogonalGapData
        0).eigenvalues
          (finiteWilsonDobrushinScaledHamiltonianGapData W i C).excitedFinrank
          j :=
  finite_wilson_derived_invariance_restricted_eigenvalues_ge_exactGap
    (finiteWilsonDobrushinScaledHamiltonianGapData W i C) 0 j

end

end MathlibAnalytic
end MGAP4D
