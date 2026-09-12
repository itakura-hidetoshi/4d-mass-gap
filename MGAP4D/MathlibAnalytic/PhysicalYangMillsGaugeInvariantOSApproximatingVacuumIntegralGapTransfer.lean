import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingVacuumIntegralGapRoundTrip
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer

noncomputable section

open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- The existing common-carrier continuum transfer specialized to a
nonnegative finite-volume vacuum norm-decay certificate. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toPhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

/-- The same nonnegative completed norm-decay data simultaneously certify the
actual finite periodic Wilson reflected integrals. -/
noncomputable def finiteIntegralGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate

/-- The reverse finite-integral reconstruction and the continuum transfer use
exactly the same physical mass parameter. -/
@[simp] theorem finiteIntegralGapCertificate_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    A.finiteIntegralGapCertificate.mass = Q.mass :=
  rfl

/-- Nonnegative finite-volume norm decay therefore yields the continuum
right-Hamiltonian coercive lower bound while also carrying the actual finite
Wilson reflected-integral certificate. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer.rightHamiltonian_inner_ge_mass_mul_norm_sq
      A psi hpsi

/-- The same lower bound survives graph closure of the continuum OS
Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      A hP psi hpsi

/-- Under the common-carrier bridge, zero energy remains exactly the normalized
continuum vacuum line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
      A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
