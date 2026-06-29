import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonExponentTwoDobrushinPoincare
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsHeatBathHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Native oriented heat-bath Hamiltonian rescaled by the explicit
Dobrushin-to-public-gap normalization factor. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.gibbsDobrushinScaledHeatBathHamiltonianLinearMap
    (L : FiniteOrientedLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy) :
    L.GibbsHilbertSpace →ₗ[ℝ] L.GibbsHilbertSpace :=
  finiteLatticeWilsonDobrushinNormalizedScale C.matrixData •
    L.gibbsHeatBathHamiltonianLinearMap

@[simp] theorem finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy)
    (x : L.GibbsHilbertSpace) :
    L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C x =
      finiteLatticeWilsonDobrushinNormalizedScale C.matrixData •
        L.gibbsHeatBathHamiltonianLinearMap x :=
  rfl

/-- The native normalized Dobrushin Hamiltonian remains symmetric. -/
theorem finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_isSymmetric
    (L : FiniteOrientedLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy) :
    (L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C).IsSymmetric := by
  intro x y
  rw [finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply,
    finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply,
    real_inner_smul_left, real_inner_smul_right]
  exact congrArg
    (fun t : ℝ =>
      finiteLatticeWilsonDobrushinNormalizedScale C.matrixData * t)
    ((finite_oriented_gibbsHeatBathHamiltonianLinearMap_isSymmetric L) x y)

/-- The native normalized Dobrushin Hamiltonian annihilates the Gibbs vacuum. -/
theorem finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_vacuum
    (L : FiniteOrientedLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy) :
    L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C
        L.gibbsHilbertVacuum = 0 := by
  rw [finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply,
    finite_oriented_gibbsHeatBathHamiltonianLinearMap_vacuum]
  simp

/-- Quadratic form of the native normalized Dobrushin Hamiltonian. -/
theorem finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_quadraticForm
    (L : FiniteOrientedLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy)
    (x : L.GibbsHilbertSpace) :
    inner ℝ
        (L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C x) x =
      finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        L.singleLinkHeatBathDirichletForm
          (L.gibbsHilbertObserveLinearMap x) := by
  rw [finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_apply,
    real_inner_smul_left,
    finite_oriented_gibbsHeatBathHamiltonianLinearMap_quadraticForm]

/-- The native normalized Dobrushin Hamiltonian has the public exact lower
bound on the vacuum-orthogonal sector. -/
theorem finite_oriented_dobrushinScaled_hamiltonian_gap_on_vacuumOrthogonal
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy)
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
    have h := finite_oriented_gibbsHilbert_vacuumCentered_norm_sq_observe L x
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
      finite_oriented_exactGap_mul_variance_le_dobrushinScale_mul_dirichlet
        L hInv C (L.gibbsHilbertObserveLinearMap x)
    _ = inner ℝ
        (L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C x) x :=
      (finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_quadraticForm
        L C x).symm

end

end MathlibAnalytic
end MGAP4D
