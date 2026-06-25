import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic
noncomputable section
open Filter Set Topology
open scoped InnerProductSpace LinearPMap
namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}
namespace StronglyContinuousPhysicalSemigroup

/-- The vacuum-orthogonal restriction obtained from ambient self-adjointness. -/
def vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    P.VacuumOrthogonalHilbert →ₗ.[ℝ] P.VacuumOrthogonalHilbert :=
  T.vacuumOrthogonalClosedRightHamiltonian
    ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf)

/-- The intersection of the closed Hamiltonian domain with the excitation sector is dense. -/
theorem vacuumOrthogonalClosedRightHamiltonian_dense_domain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    Dense (((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain :
      Set P.VacuumOrthogonalHilbert)) := by
  intro psi
  rw [mem_closure_iff_seq_limit]
  have hAmbientClosure :
      ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) ∈
        closure (T.closedRightHamiltonian.domain : Set P.PhysicalHilbert) :=
    hSelf.dense_domain _
  rw [mem_closure_iff_seq_limit] at hAmbientClosure
  rcases hAmbientClosure with ⟨u, huDomain, huTendsto⟩
  have hVacuumInner : inner ℝ P.vacuum P.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, P.norm_vacuum hP]
    norm_num
  have hPsiOrthogonal :
      inner ℝ ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
        P.vacuum = 0 := by
    rw [real_inner_comm]
    exact (P.mem_vacuumOrthogonal_iff _).mp psi.property
  let coefficient : ℕ → ℝ := fun n => inner ℝ (u n) P.vacuum
  have hCoefficient : Tendsto coefficient atTop (nhds 0) := by
    have hInner :
        Tendsto (fun n => inner ℝ (u n) P.vacuum) atTop
          (nhds (inner ℝ
            ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
            P.vacuum)) :=
      huTendsto.inner (𝕜 := ℝ) tendsto_const_nhds
    simpa only [coefficient, hPsiOrthogonal] using hInner
  let correctedAmbient : ℕ → P.PhysicalHilbert := fun n =>
    u n - coefficient n • P.vacuum
  have hCorrectedOrthogonal (n : ℕ) :
      correctedAmbient n ∈ P.vacuumOrthogonal := by
    rw [P.mem_vacuumOrthogonal_iff, real_inner_comm]
    change inner ℝ (u n - coefficient n • P.vacuum) P.vacuum = 0
    rw [inner_sub_left, real_inner_smul_left, hVacuumInner, mul_one]
    simp [coefficient]
  have hCorrectedDomain (n : ℕ) :
      correctedAmbient n ∈ T.closedRightHamiltonian.domain :=
    T.closedRightHamiltonian.domain.sub_mem (huDomain n)
      (T.closedRightHamiltonian.domain.smul_mem (coefficient n)
        T.closedRightHamiltonianVacuumDomainPoint.property)
  have hCorrectedAmbientTendsto :
      Tendsto correctedAmbient atTop
        (nhds ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) := by
    simpa [correctedAmbient] using
      huTendsto.sub (hCoefficient.smul_const P.vacuum)
  let corrected : ℕ → P.VacuumOrthogonalHilbert := fun n =>
    ⟨correctedAmbient n, hCorrectedOrthogonal n⟩
  have hCorrectedTendsto : Tendsto corrected atTop (nhds psi) := by
    apply (IsInducing.subtypeVal.tendsto_nhds_iff).2
    simpa [corrected] using hCorrectedAmbientTendsto
  refine ⟨corrected, ?_, hCorrectedTendsto⟩
  intro n
  change ((corrected n : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) ∈
    T.closedRightHamiltonian.domain
  simpa [corrected] using hCorrectedDomain n

/-- In the self-adjoint realization on the excitation Hilbert space, every
putative eigenvector with eigenvalue below the transferred mass is zero. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_eq_zero_of_eigenvalue_lt_mass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain)
    (hEigen :
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x =
        lambda • (x : P.VacuumOrthogonalHilbert)) :
    (x : P.VacuumOrthogonalHilbert) = 0 := by
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_eq_zero_of_eigenvalue_lt_mass
      T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf)
      hlambda x hEigen

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end
end MathlibAnalytic
end MGAP4D
