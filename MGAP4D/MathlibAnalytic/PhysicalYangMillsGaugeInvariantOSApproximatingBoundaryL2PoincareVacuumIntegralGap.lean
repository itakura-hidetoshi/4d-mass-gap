import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingVacuumIntegralGapTransfer

noncomputable section

open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate

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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- A shared-boundary `L²` Poincaré defect estimate generates the actual finite
periodic Wilson reflected-integral decay certificate. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryMomentGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

/-- The same Poincaré estimate generates a completed vacuum norm-decay
certificate whose decay factor is explicitly nonnegative. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate
    |>.toApproximatingNonnegativeVacuumGapCertificate

/-- The boundary Poincaré route preserves the physical mass parameter exactly. -/
@[simp] theorem toApproximatingNonnegativeVacuumGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingNonnegativeVacuumGapCertificate.mass = Q.mass :=
  rfl

/-- The finite reflected-integral certificate reconstructed through completed
nonnegative vacuum decay has the same mass as the original boundary Poincaré
certificate. -/
@[simp] theorem nonnegativeVacuum_finiteIntegral_roundTrip_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingNonnegativeVacuumGapCertificate
        |>.toApproximatingFiniteIntegralGapCertificate
        |>.mass = Q.mass :=
  rfl

/-- The Poincaré quadratic decay factor is unchanged by the finite-integral to
nonnegative-vacuum to finite-integral round trip. -/
@[simp] theorem nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    Q.toApproximatingNonnegativeVacuumGapCertificate
        |>.toApproximatingFiniteIntegralGapCertificate
        |>.quadraticDecayFactor t =
      1 - Q.defectFactor t := by
  simpa only [toApproximatingNonnegativeVacuumGapCertificate,
    toApproximatingFiniteIntegralGapCertificate,
    toApproximatingBoundaryMomentGapCertificate,
    toApproximatingBoundaryL2QuadraticGapCertificate,
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate.toApproximatingBoundaryMomentGapCertificate,
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate.toApproximatingBoundaryMomentGapCertificate]
    using
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate.nonnegativeVacuum_roundTrip_quadraticDecayFactor
        Q.toApproximatingFiniteIntegralGapCertificate t

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate

/-- The common-carrier continuum transfer specialized all the way back to a
shared-boundary `L²` Poincaré defect estimate. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer
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
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toApproximatingNonnegativeVacuumGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer

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
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

/-- Recover the actual finite periodic Wilson reflected-integral certificate
from the shared-boundary Poincaré input. -/
noncomputable def finiteIntegralGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingNonnegativeVacuumGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

@[simp] theorem finiteIntegralGapCertificate_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    A.finiteIntegralGapCertificate.mass = Q.mass :=
  rfl

/-- Shared-boundary Poincaré decay and the actual finite Wilson reflected
integrals therefore feed the continuum right-Hamiltonian coercive estimate with
the same mass. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer.rightHamiltonian_inner_ge_mass_mul_norm_sq
      A psi hpsi

/-- The same mass lower bound survives graph closure of the continuum OS
Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      A hP psi hpsi

/-- Zero energy remains exactly the normalized continuum vacuum line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSNonnegativeVacuumCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
      A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
