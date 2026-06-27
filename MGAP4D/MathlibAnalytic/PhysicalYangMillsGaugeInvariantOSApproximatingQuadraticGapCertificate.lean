import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PhysicalSemigroup

/-- For a symmetric Euclidean semigroup, the squared norm after time `t` is the
quadratic matrix coefficient at time `2t`.

This elementary identity is the bridge from a diagonal Wilson OS correlation
estimate to the operator-norm decay estimate required by the continuum
Hamiltonian gap transfer. -/
theorem operator_norm_sq_eq_inner_operator_add_self
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    ‖T.operator t psi‖ ^ 2 =
      inner ℝ (T.operator (t + t) psi) psi := by
  calc
    ‖T.operator t psi‖ ^ 2 =
        inner ℝ (T.operator t psi) (T.operator t psi) := by
      simpa using (real_inner_self_eq_norm_sq (T.operator t psi)).symm
    _ = inner ℝ psi (T.operator t (T.operator t psi)) :=
      hSymmetric t psi (T.operator t psi)
    _ = inner ℝ psi (T.operator (t + t) psi) := by
      rw [T.operator_add]
      rfl
    _ = inner ℝ (T.operator (t + t) psi) psi :=
      real_inner_comm _ _

end PhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- A finite-volume Wilson OS gap certificate stated only through diagonal
quadratic matrix coefficients.

For symmetric transfer operators, this is strictly closer to the concrete
reflection-positive Wilson integral than a norm estimate.  The semigroup square
identity converts the bound at time `2t` into norm decay at time `t`.

The square-root slope is stated explicitly because it is the physical mass
which survives the continuum right-generator limit. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
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
  mass : ℝ
  mass_pos : 0 < mass
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg :
    ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  finite_quadratic_decay :
    ∀ (n : ℕ) (t : NNReal)
      (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n),
      inner ℝ phi
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta B hInvariant n) = 0 →
        inner ℝ (C.finiteOperator n t phi) phi ≤
          quadraticDecayFactor t * ‖phi‖ ^ 2

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate

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

/-- The diagonal quadratic Wilson OS estimate implies the finite-volume norm
decay needed by the gap-transfer package. -/
theorem finite_decay
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n)
    (hphi : inner ℝ phi
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
        S D halfExtent N hN beta hbeta B hInvariant n) = 0) :
    ‖C.finiteOperator n t phi‖ ≤
      Real.sqrt (Q.quadraticDecayFactor (t + t)) * ‖phi‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  have hSymmetric :
      (C.finitePhysicalSemigroup n).IsInnerSymmetric := by
    exact
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange.toPhysicalSemigroup_isInnerSymmetric
        (Q.exchange n)
  have hsq :
      ‖C.finiteOperator n t phi‖ ^ 2 ≤
        Q.quadraticDecayFactor (t + t) * ‖phi‖ ^ 2 := by
    calc
      ‖C.finiteOperator n t phi‖ ^ 2 =
          inner ℝ (C.finiteOperator n (t + t) phi) phi := by
        exact
          PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PhysicalSemigroup.operator_norm_sq_eq_inner_operator_add_self
            (C.finitePhysicalSemigroup n) hSymmetric t phi
      _ ≤ Q.quadraticDecayFactor (t + t) * ‖phi‖ ^ 2 :=
        Q.finite_quadratic_decay n (t + t) phi hphi
  have hq : 0 ≤ Q.quadraticDecayFactor (t + t) :=
    Q.quadraticDecayFactor_nonneg (t + t)
  have hsqrt_sq :
      (Real.sqrt (Q.quadraticDecayFactor (t + t))) ^ 2 =
        Q.quadraticDecayFactor (t + t) :=
    Real.sq_sqrt hq
  have hleft : 0 ≤ ‖C.finiteOperator n t phi‖ := norm_nonneg _
  have hright :
      0 ≤ Real.sqrt (Q.quadraticDecayFactor (t + t)) * ‖phi‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

/-- Convert the quadratic correlation certificate into the norm-decay
certificate consumed by the common-carrier continuum gap bridge. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  decayFactor := fun t =>
    Real.sqrt (Q.quadraticDecayFactor (t + t))
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  finite_decay := Q.finite_decay

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate

end MathlibAnalytic
end MGAP4D

end
