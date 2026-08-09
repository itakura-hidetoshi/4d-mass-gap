import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalSelfAdjoint
import Mathlib.Topology.Sequences
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

/-- Any nonzero vector in the complete physical excitation Hilbert space gives
an actual nonzero vacuum-orthogonal closed-Hamiltonian domain state once the OS
Hamiltonian is self-adjoint.

The point is density, not a choice of synthetic spectrum: approximate the given
excitation by vectors in the restricted closed-Hamiltonian domain.  If every
approximant vanished, uniqueness of limits would force the target excitation to
vanish. -/
theorem physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (phi : P.VacuumOrthogonalHilbert)
    (hphi : phi ≠ 0) :
    T.PhysicalYangMillsExcitationDomainWitness := by
  let hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian :=
    (T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf
  have hDense :
      Dense (((T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain :
        Set P.VacuumOrthogonalHilbert)) := by
    simpa [hSymmetric, vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
      T.vacuumOrthogonalClosedRightHamiltonian_dense_domain hP hSelf
  have hClosure :
      phi ∈ closure
        ((T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain :
          Set P.VacuumOrthogonalHilbert) :=
    hDense phi
  rw [mem_closure_iff_seq_limit] at hClosure
  rcases hClosure with ⟨u, huDomain, huTendsto⟩
  have hExists : ∃ n : ℕ, u n ≠ 0 := by
    by_contra hNo
    push_neg at hNo
    have huZero : u = fun _ => 0 := by
      funext n
      exact hNo n
    rw [huZero] at huTendsto
    have hphiZero : phi = 0 :=
      tendsto_nhds_unique huTendsto tendsto_const_nhds
    exact hphi hphiZero
  rcases hExists with ⟨n, hn⟩
  let xCore : T.vacuumOrthogonalClosedRightHamiltonianDomain :=
    ⟨u n, by
      simpa only [T.vacuumOrthogonalClosedRightHamiltonian_domain] using
        huDomain n⟩
  let psi : T.closedRightHamiltonian.domain :=
    T.vacuumOrthogonalAmbientDomainPoint xCore
  have hpsiNonzero : (psi : P.PhysicalHilbert) ≠ 0 := by
    intro hzero
    apply hn
    apply Subtype.ext
    simpa [psi, xCore, vacuumOrthogonalAmbientDomainPoint] using hzero
  have huOrthogonal :
      inner ℝ
          (((u n : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
          P.vacuum = 0 := by
    rw [real_inner_comm]
    exact (P.mem_vacuumOrthogonal_iff _).mp (u n).property
  have hpsiOrthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 := by
    simpa [psi, xCore, vacuumOrthogonalAmbientDomainPoint] using huOrthogonal
  exact
    { state := psi
      state_ne_zero := hpsiNonzero
      state_orthogonal := hpsiOrthogonal }

/-- Therefore, after self-adjoint OS reconstruction, the variational mass needs
only nontriviality of the complete excitation Hilbert sector; membership in the
closed Hamiltonian domain follows automatically from density. -/
theorem physicalYangMillsExcitationDomainWitness_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    T.PhysicalYangMillsExcitationDomainWitness := by
  obtain ⟨phi, hphi⟩ := exists_ne (0 : P.VacuumOrthogonalHilbert)
  exact T.physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation
    hP hSelf phi hphi

/-- Under the same genuinely physical nontriviality assumption, the derived
Yang--Mills mass is automatically nonnegative. -/
theorem physicalYangMillsMass_nonneg_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    0 ≤ T.physicalYangMillsMass :=
  T.physicalYangMillsMass_nonneg
    (T.physicalYangMillsExcitationDomainWitness_of_nontrivial hP hSelf)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
