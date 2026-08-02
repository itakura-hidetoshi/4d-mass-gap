import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingMeasurableBoundaryL2PoincareVacuumIntegralGap

noncomputable section

open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate

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

/-- An exponential boundary-transfer defect estimate generates the actual
finite periodic Wilson reflected-integral certificate. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate.toApproximatingFiniteIntegralGapCertificate
    Q.toApproximatingMeasurableBoundaryL2PoincareGapCertificate

/-- The exponential defect package generates a completed vacuum norm-decay
certificate with an explicitly nonnegative factor. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate.toApproximatingNonnegativeVacuumGapCertificate
    Q.toApproximatingMeasurableBoundaryL2PoincareGapCertificate

@[simp] theorem toApproximatingNonnegativeVacuumGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingNonnegativeVacuumGapCertificate.mass = Q.mass :=
  rfl

/-- The exponential quadratic factor is recovered exactly after passing
through completed nonnegative vacuum decay and back to finite integrals. -/
@[simp] theorem nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    (PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate.toApproximatingFiniteIntegralGapCertificate
      Q.toApproximatingNonnegativeVacuumGapCertificate).quadraticDecayFactor t =
      Real.exp (-Q.mass * (t : ℝ)) := by
  simpa only [sub_sub_cancel] using
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate.nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
      Q.toApproximatingMeasurableBoundaryL2PoincareGapCertificate t

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate

/-- Common-carrier continuum endpoint generated from the explicit exponential
boundary defect estimate. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2PoincareCommonCarrierGapTransfer
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
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toApproximatingMeasurableBoundaryL2PoincareGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2PoincareCommonCarrierGapTransfer

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
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

noncomputable def finiteIntegralGapCertificate
    (_A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate

@[simp] theorem finiteIntegralGapCertificate_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    A.finiteIntegralGapCertificate.mass = Q.mass :=
  rfl

/-- The explicit exponential boundary estimate implies continuum
right-Hamiltonian coercivity with slope `Q.mass`. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer.rightHamiltonian_inner_ge_mass_mul_norm_sq
      A psi hpsi

/-- The graph-closed continuum Hamiltonian retains the exponential-boundary
mass lower bound. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      A hP psi hpsi

/-- Zero energy remains exactly the normalized continuum vacuum line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2PoincareCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSMeasurableBoundaryL2PoincareCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
      A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2PoincareCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
