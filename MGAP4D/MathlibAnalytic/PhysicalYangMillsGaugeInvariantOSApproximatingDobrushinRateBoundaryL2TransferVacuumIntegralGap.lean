import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinPoincareL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryL2TransferVacuumIntegralGap

noncomputable section

open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A uniform Dobrushin-rate specialization of the exponential shared-boundary
transfer package.

The strict coefficient `coefficient < 1` fixes the physical rate

`mass = 1 - coefficient`.

The embedded exponential transfer certificate still carries the genuinely
model-specific operator-norm contraction and OS boundary-moment intertwining.
This structure does not infer an `L²` estimate from total variation and does
not identify compact heat-bath evolution with Euclidean-time OS translation. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
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
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant) where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  coefficient_lt_one : coefficient < 1
  exponentialTransfer :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C
  exponentialTransfer_mass_eq :
    exponentialTransfer.mass =
      continuousCompactOrientedDobrushinHeatBathGap coefficient

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate

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

/-- The strict uniform Dobrushin coefficient gives a positive transfer rate. -/
theorem dobrushinHeatBathGap_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    0 < continuousCompactOrientedDobrushinHeatBathGap Q.coefficient := by
  unfold continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr Q.coefficient_lt_one

/-- The embedded exponential transfer certificate has exactly rate
`1 - coefficient`. -/
@[simp] theorem exponentialTransfer_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.exponentialTransfer.mass = 1 - Q.coefficient := by
  simpa only [continuousCompactOrientedDobrushinHeatBathGap] using
    Q.exponentialTransfer_mass_eq

/-- A uniform Dobrushin-rate transfer package generates the boundary Poincaré
certificate with defect `1 - exp (-(1 - coefficient) * t)`. -/
noncomputable def toApproximatingBoundaryL2PoincareGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.exponentialTransfer.toApproximatingBoundaryL2PoincareGapCertificate

@[simp] theorem toApproximatingBoundaryL2PoincareGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingBoundaryL2PoincareGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficient := by
  exact Q.exponentialTransfer_mass_eq

@[simp] theorem toApproximatingBoundaryL2PoincareGapCertificate_defectFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    Q.toApproximatingBoundaryL2PoincareGapCertificate.defectFactor t =
      1 - Real.exp
        (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficient *
          (t : ℝ)) := by
  rw [toApproximatingBoundaryL2PoincareGapCertificate]
  rw [PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate.toApproximatingBoundaryL2PoincareGapCertificate_defectFactor]
  rw [Q.exponentialTransfer_mass_eq]

/-- The uniform Dobrushin-rate package generates the actual finite periodic
Wilson reflected-integral gap certificate. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.exponentialTransfer.toApproximatingFiniteIntegralGapCertificate

/-- It also generates completed nonnegative vacuum norm decay. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.exponentialTransfer.toApproximatingNonnegativeVacuumGapCertificate

@[simp] theorem toApproximatingFiniteIntegralGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingFiniteIntegralGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficient := by
  exact Q.exponentialTransfer_mass_eq

/-- The finite-integral round trip recovers the exact Dobrushin-rate
exponential quadratic factor. -/
@[simp] theorem nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    (PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate.toApproximatingFiniteIntegralGapCertificate
      Q.toApproximatingNonnegativeVacuumGapCertificate).quadraticDecayFactor t =
      Real.exp
        (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficient *
          (t : ℝ)) := by
  rw [toApproximatingNonnegativeVacuumGapCertificate]
  rw [PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate.nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor]
  rw [Q.exponentialTransfer_mass_eq]

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate

/-- Common-carrier continuum endpoint specialized to the uniform Dobrushin
rate `1 - coefficient`. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer
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
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.exponentialTransfer

namespace PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer

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
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

noncomputable def finiteIntegralGapCertificate
    (_A : PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate

@[simp] theorem finiteIntegralGapCertificate_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    A.finiteIntegralGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficient := by
  exact Q.exponentialTransfer_mass_eq

/-- The continuum right-Hamiltonian coercive constant is exactly the uniform
Dobrushin rate `1 - coefficient`. -/
theorem rightHamiltonian_inner_ge_dobrushinGap_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedDobrushinHeatBathGap Q.coefficient *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  rw [← Q.exponentialTransfer_mass_eq]
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer.rightHamiltonian_inner_ge_mass_mul_norm_sq
      A psi hpsi

/-- The same Dobrushin-rate lower bound survives graph closure. -/
theorem closedRightHamiltonian_inner_ge_dobrushinGap_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedDobrushinHeatBathGap Q.coefficient *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  rw [← Q.exponentialTransfer_mass_eq]
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      A hP psi hpsi

/-- Zero energy remains exactly the normalized continuum vacuum line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
      A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
