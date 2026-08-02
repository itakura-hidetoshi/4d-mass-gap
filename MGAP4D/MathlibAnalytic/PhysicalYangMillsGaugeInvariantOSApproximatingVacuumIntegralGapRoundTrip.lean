import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingNonnegativeVacuumIntegralGap

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate

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

/-- Every finite reflected-integral certificate canonically yields a
nonnegative completed vacuum norm-decay certificate. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  toPhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate :=
    Q.toApproximatingVacuumGapCertificate
  decayFactor_nonneg := fun t => Real.sqrt_nonneg _

/-- Passing from a finite integral certificate to completed norm decay and back
recovers the original quadratic decay factor exactly. -/
@[simp] theorem nonnegativeVacuum_roundTrip_quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    Q.toApproximatingNonnegativeVacuumGapCertificate.quadraticDecayFactor t =
      Q.quadraticDecayFactor t := by
  have hhalf : t / 2 + t / 2 = t := by
    ext
    norm_num <;> ring
  unfold
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate.quadraticDecayFactor
    toApproximatingNonnegativeVacuumGapCertificate
  dsimp only
  rw [hhalf, Real.sq_sqrt (Q.quadraticDecayFactor_nonneg t)]

/-- The round-trip finite-integral certificate preserves its mass parameter. -/
@[simp] theorem nonnegativeVacuum_roundTrip_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingNonnegativeVacuumGapCertificate
        |>.toApproximatingFiniteIntegralGapCertificate
        |>.mass = Q.mass :=
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate

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

/-- Passing from nonnegative completed norm decay to finite reflected integrals
and through the existing forward constructor recovers the original norm-decay
factor exactly. -/
@[simp] theorem finiteIntegral_roundTrip_decayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    Q.toApproximatingFiniteIntegralGapCertificate
        |>.toApproximatingVacuumGapCertificate
        |>.decayFactor t = Q.decayFactor t := by
  change Real.sqrt (Q.quadraticDecayFactor (t + t)) = Q.decayFactor t
  exact Q.sqrt_quadraticDecayFactor_add_self t

/-- The reverse-forward round trip also preserves the physical mass slope. -/
@[simp] theorem finiteIntegral_roundTrip_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingFiniteIntegralGapCertificate
        |>.toApproximatingVacuumGapCertificate
        |>.mass = Q.mass :=
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate

end MathlibAnalytic
end MGAP4D

end
