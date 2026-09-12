import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Exact identification principle for the mass of the *actual* graph-closed
Osterwalder--Schrader Yang--Mills Hamiltonian.

Suppose `lambda` is a uniform Rayleigh lower bound on every nonzero
vacuum-orthogonal vector in the closed Hamiltonian domain, and suppose one
actual physical excitation attains the Rayleigh value `lambda`.  Then the
variationally defined physical Yang--Mills mass is exactly `lambda`.

No numerical mass value, finite-volume transfer rate, synthetic spectral
carrier, or prescribed eigenvalue enters this theorem.  It is the final
order-theoretic identification step needed after the Yang--Mills construction
has supplied both the lower bound and an attaining physical excitation. -/
theorem physicalYangMillsMass_eq_of_uniformRayleighLowerBound_of_attained
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ}
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattained : T.physicalYangMillsClosedRayleighQuotient psi = lambda)
    (hlower :
      ∀ phi : T.closedRightHamiltonian.domain,
        (phi : P.PhysicalHilbert) ≠ 0 →
        inner ℝ (phi : P.PhysicalHilbert) P.vacuum = 0 →
        lambda * ‖(phi : P.PhysicalHilbert)‖ ^ 2 ≤
          inner ℝ (T.closedRightHamiltonian phi)
            (phi : P.PhysicalHilbert)) :
    T.physicalYangMillsMass = lambda := by
  have hlambda_mem :
      lambda ∈ T.physicalYangMillsClosedExcitationRayleighSet := by
    exact ⟨psi, hpsi, horthogonal, hattained⟩
  have hmass_le : T.physicalYangMillsMass ≤ lambda :=
    T.physicalYangMillsMass_le_rayleigh hlambda_mem
  let W : T.PhysicalYangMillsExcitationDomainWitness :=
    { state := psi
      state_ne_zero := hpsi
      state_orthogonal := horthogonal }
  have hlambda_le : lambda ≤ T.physicalYangMillsMass :=
    T.uniformRayleighLowerBound_le_physicalYangMillsMass W hlower
  exact le_antisymm hmass_le hlambda_le

/-- An actual nonzero vacuum-orthogonal eigenvector realizes its eigenvalue as
an excitation Rayleigh value.  This is stated for the genuine closed OS
Hamiltonian and not for a symbolic eigenvalue record. -/
theorem physicalYangMillsClosedRayleighQuotient_eq_of_eigenvector
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ}
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (heigen :
      T.closedRightHamiltonian psi =
        lambda • (psi : P.PhysicalHilbert)) :
    T.physicalYangMillsClosedRayleighQuotient psi = lambda := by
  have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
    norm_pos_iff.mpr hpsi
  have hnorm_sq_ne : ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≠ 0 := by
    positivity
  unfold physicalYangMillsClosedRayleighQuotient
  rw [heigen, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp [hnorm_sq_ne]

/-- Eigenvector specialization of
`physicalYangMillsMass_eq_of_uniformRayleighLowerBound_of_attained`.

Thus an exact numerical mass theorem for the complete Yang--Mills construction
may be proved in the physically correct direction:

1. derive a uniform lower bound from the actual Wilson/continuum dynamics;
2. construct an actual vacuum-orthogonal closed-Hamiltonian eigenstate at the
   same value;
3. conclude equality with the variational physical Yang--Mills mass.

The value itself remains completely parametric here. -/
theorem physicalYangMillsMass_eq_of_uniformRayleighLowerBound_of_eigenvector
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ}
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (heigen :
      T.closedRightHamiltonian psi =
        lambda • (psi : P.PhysicalHilbert))
    (hlower :
      ∀ phi : T.closedRightHamiltonian.domain,
        (phi : P.PhysicalHilbert) ≠ 0 →
        inner ℝ (phi : P.PhysicalHilbert) P.vacuum = 0 →
        lambda * ‖(phi : P.PhysicalHilbert)‖ ^ 2 ≤
          inner ℝ (T.closedRightHamiltonian phi)
            (phi : P.PhysicalHilbert)) :
    T.physicalYangMillsMass = lambda := by
  exact T.physicalYangMillsMass_eq_of_uniformRayleighLowerBound_of_attained
    psi hpsi horthogonal
    (T.physicalYangMillsClosedRayleighQuotient_eq_of_eigenvector psi hpsi heigen)
    hlower

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
