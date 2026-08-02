import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingMeasurableBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2PoincareVacuumIntegralGap

noncomputable section

open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate

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

/-- Measurability and squared-integrability data together with the boundary
Poincaré defect estimate generate the actual finite Wilson reflected-integral
certificate. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2PoincareGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

/-- The measurable boundary package generates completed nonnegative vacuum
norm decay without adding a separate sign assumption. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2PoincareGapCertificate
    |>.toApproximatingNonnegativeVacuumGapCertificate

@[simp] theorem toApproximatingNonnegativeVacuumGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingNonnegativeVacuumGapCertificate.mass = Q.mass :=
  rfl

/-- The measurable boundary route preserves the Poincaré quadratic factor
through the nonnegative-vacuum round trip. -/
@[simp] theorem nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    Q.toApproximatingNonnegativeVacuumGapCertificate
        |>.toApproximatingFiniteIntegralGapCertificate
        |>.quadraticDecayFactor t =
      1 - Q.defectFactor t := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate.nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
      Q.toApproximatingBoundaryL2PoincareGapCertificate t

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate

/-- Common-carrier endpoint generated directly from measurable boundary
Poincaré data. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer
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
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toApproximatingBoundaryL2PoincareGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer

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
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

noncomputable def finiteIntegralGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate

@[simp] theorem finiteIntegralGapCertificate_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    A.finiteIntegralGapCertificate.mass = Q.mass :=
  rfl

/-- Measurable boundary Poincaré data imply the continuum right-Hamiltonian
coercive estimate with exactly the same mass. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer.rightHamiltonian_inner_ge_mass_mul_norm_sq
      A psi hpsi

/-- The graph-closed continuum Hamiltonian retains the measurable-boundary
mass lower bound. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      A hP psi hpsi

/-- Zero energy is exactly the normalized continuum vacuum line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
      A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
