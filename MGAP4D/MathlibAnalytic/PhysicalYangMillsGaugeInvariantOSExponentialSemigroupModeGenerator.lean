import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalHamiltonian
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- An exact exponential orbit is automatically an eigenmode of the right
Euclidean Hamiltonian in the semigroup-generator sense.

This is the bounded-to-unbounded bridge needed by the transfer/OS frontier: no
Hamiltonian-domain assumption and no infinitesimal action equation are supplied.
Both are generated from the full positive-time orbit

`T_t psi = exp (-energy * t) psi`

and the canonical right difference quotient. -/
theorem hasRightHamiltonianValue_of_exponential_orbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (energy : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t psi =
        Real.exp (-energy * (t : ℝ)) • psi) :
    T.HasRightHamiltonianValue psi (energy • psi) := by
  have hscalar := tendsto_nnreal_inv_mul_one_sub_exp_neg_mul energy
  have hscaled :
      Tendsto
        (fun t : NNReal =>
          ((t : ℝ)⁻¹ *
            (1 - Real.exp (-energy * (t : ℝ)))) • psi)
        (nhdsWithin 0 (Ioi 0))
        (nhds (energy • psi)) :=
    hscalar.smul_const psi
  have hham :
      Tendsto
        (fun t : NNReal => T.rightHamiltonianDifferenceQuotient psi t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (energy • psi)) := by
    convert hscaled using 1
    funext t
    rw [rightHamiltonianDifferenceQuotient, hOrbit t]
    module
  unfold HasRightHamiltonianValue HasRightGeneratorValue
  have hneg := hham.neg
  simpa only [rightHamiltonianDifferenceQuotient_eq_neg, neg_neg] using hneg

/-- Exact exponential semigroup modes belong to the canonical right-generator
(and hence right-Hamiltonian) domain. -/
theorem exponential_orbit_mem_rightGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (energy : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t psi =
        Real.exp (-energy * (t : ℝ)) • psi) :
    psi ∈ T.rightGeneratorDomain := by
  refine ⟨-(energy • psi), ?_⟩
  exact T.hasRightHamiltonianValue_of_exponential_orbit psi energy hOrbit

/-- The canonical right Hamiltonian acts on an exact exponential orbit by its
exponential energy. -/
theorem rightHamiltonian_apply_of_exponential_orbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (energy : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t psi =
        Real.exp (-energy * (t : ℝ)) • psi) :
    T.rightHamiltonian
        ⟨psi, T.exponential_orbit_mem_rightGeneratorDomain psi energy hOrbit⟩ =
      energy • psi := by
  apply T.hasRightHamiltonianValue_unique
    (T.rightHamiltonian_hasRightHamiltonianValue
      ⟨psi, T.exponential_orbit_mem_rightGeneratorDomain psi energy hOrbit⟩)
  exact T.hasRightHamiltonianValue_of_exponential_orbit psi energy hOrbit

/-- The same exact exponential mode belongs to the graph-closed right
Hamiltonian used by the self-adjoint OS excitation theory. -/
theorem exponential_orbit_mem_closedRightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (energy : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t psi =
        Real.exp (-energy * (t : ℝ)) • psi) :
    psi ∈ T.closedRightHamiltonian.domain :=
  T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1
    (T.exponential_orbit_mem_rightGeneratorDomain psi energy hOrbit)

/-- Passing to the canonical graph closure does not alter the eigenvalue of an
exact exponential semigroup mode. -/
theorem closedRightHamiltonian_apply_of_exponential_orbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (energy : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t psi =
        Real.exp (-energy * (t : ℝ)) • psi) :
    T.closedRightHamiltonian
        ⟨psi,
          T.exponential_orbit_mem_closedRightHamiltonianDomain
            psi energy hOrbit⟩ =
      energy • psi := by
  let hright : psi ∈ T.rightGeneratorDomain :=
    T.exponential_orbit_mem_rightGeneratorDomain psi energy hOrbit
  let hclosed : psi ∈ T.closedRightHamiltonian.domain :=
    T.exponential_orbit_mem_closedRightHamiltonianDomain psi energy hOrbit
  have hext :
      T.rightHamiltonianLinearPMap ⟨psi, hright⟩ =
        T.closedRightHamiltonian ⟨psi, hclosed⟩ :=
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.2 rfl
  calc
    T.closedRightHamiltonian ⟨psi, hclosed⟩ =
        T.rightHamiltonianLinearPMap ⟨psi, hright⟩ := hext.symm
    _ = T.rightHamiltonian ⟨psi, hright⟩ := rfl
    _ = energy • psi := by
      exact T.rightHamiltonian_apply_of_exponential_orbit psi energy hOrbit

/-- Logarithmic form suited to a positive transfer eigenvalue `mu`: if the
physical OS orbit is `exp (log(mu) t) psi`, then the closed OS Hamiltonian energy
is exactly `-log(mu)`.  Positivity of `mu` is intentionally not needed for this
analytic implication; it is supplied by the compact-positive transfer spectral
support when this theorem is specialized. -/
theorem closedRightHamiltonian_apply_of_logarithmic_semigroup_mode
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (mu : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t psi =
        Real.exp (Real.log mu * (t : ℝ)) • psi) :
    T.closedRightHamiltonian
        ⟨psi,
          T.exponential_orbit_mem_closedRightHamiltonianDomain
            psi (-Real.log mu) (by
              intro t
              simpa using hOrbit t)⟩ =
      (-Real.log mu) • psi := by
  apply T.closedRightHamiltonian_apply_of_exponential_orbit
  intro t
  simpa using hOrbit t

/-- An exact exponential orbit already lying in the physical excitation sector
belongs automatically to the restricted closed-Hamiltonian domain. -/
theorem exponential_orbit_mem_vacuumOrthogonalClosedRightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.VacuumOrthogonalHilbert) (energy : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert) =
        Real.exp (-energy * (t : ℝ)) • (psi : P.PhysicalHilbert)) :
    psi ∈ T.vacuumOrthogonalClosedRightHamiltonianDomain :=
  T.exponential_orbit_mem_closedRightHamiltonianDomain
    (psi : P.PhysicalHilbert) energy hOrbit

/-- On the vacuum-orthogonal excitation carrier, exact exponential semigroup
modes are eigenvectors of the restricted graph-closed Hamiltonian. -/
theorem vacuumOrthogonalClosedRightHamiltonian_apply_of_exponential_orbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert) (energy : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert) =
        Real.exp (-energy * (t : ℝ)) • (psi : P.PhysicalHilbert)) :
    T.vacuumOrthogonalClosedRightHamiltonian hSymmetric
        ⟨psi,
          T.exponential_orbit_mem_vacuumOrthogonalClosedRightHamiltonianDomain
            psi energy hOrbit⟩ =
      energy • psi := by
  apply Subtype.ext
  change T.closedRightHamiltonian
      (T.vacuumOrthogonalAmbientDomainPoint
        ⟨psi,
          T.exponential_orbit_mem_vacuumOrthogonalClosedRightHamiltonianDomain
            psi energy hOrbit⟩) =
    energy • (psi : P.PhysicalHilbert)
  simpa only [vacuumOrthogonalAmbientDomainPoint] using
    T.closedRightHamiltonian_apply_of_exponential_orbit
      (psi : P.PhysicalHilbert) energy hOrbit

/-- Transfer-logarithmic form on the physical excitation carrier.  A bounded OS
mode with full-time orbit `exp (log(mu) t)` has restricted closed-Hamiltonian
energy exactly `-log(mu)`. -/
theorem vacuumOrthogonalClosedRightHamiltonian_apply_of_logarithmic_semigroup_mode
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert) (mu : ℝ)
    (hOrbit : ∀ t : NNReal,
      T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert) =
        Real.exp (Real.log mu * (t : ℝ)) • (psi : P.PhysicalHilbert)) :
    T.vacuumOrthogonalClosedRightHamiltonian hSymmetric
        ⟨psi,
          T.exponential_orbit_mem_vacuumOrthogonalClosedRightHamiltonianDomain
            psi (-Real.log mu) (by
              intro t
              simpa using hOrbit t)⟩ =
      (-Real.log mu) • psi := by
  apply T.vacuumOrthogonalClosedRightHamiltonian_apply_of_exponential_orbit
  intro t
  simpa using hOrbit t

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
