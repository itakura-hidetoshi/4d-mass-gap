import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridgeL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

variable
    {sideLength : ℕ → ℕ}
    {sideLength_pos : ∀ n, 0 < sideLength n}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {W : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : W.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

/-- The continuum OS convergence bridge specialized to the periodic
four-dimensional `SU(N)` Wilson family. -/
abbrev UniformImplicitEulerOSBridge
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg) :=
  ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
    P T D.toUniformFamily

/-- The periodic `SU(N)` bridge transfers the common finite-volume gap to the
continuum right Hamiltonian. -/
theorem rightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : D.UniformImplicitEulerOSBridge)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    (1 - D.coefficientBound) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  simpa only [toUniformFamily_gap] using
    B.rightHamiltonian_inner_ge_uniformDobrushinGap_mul_norm_sq psi hpsi

/-- The periodic `SU(N)` uniform gap survives graph closure of the continuum
OS Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : D.UniformImplicitEulerOSBridge)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    (1 - D.coefficientBound) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  simpa only [toUniformFamily_gap] using
    B.closedRightHamiltonian_inner_ge_uniformDobrushinGap_mul_norm_sq
      hP psi hpsi

end PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

end

end MathlibAnalytic
end MGAP4D
