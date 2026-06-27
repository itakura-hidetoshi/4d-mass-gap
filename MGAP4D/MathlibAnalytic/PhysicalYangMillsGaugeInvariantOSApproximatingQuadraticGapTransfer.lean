import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A finite-volume Wilson OS gap certificate stated at the level of reflected
quadratic correlations.

For a symmetric semigroup, the semigroup law gives

`‖T_t φ‖² = ⟪T_t φ, T_t φ⟫ = ⟪T_(t+t) φ, φ⟫`.

Consequently a vacuum-orthogonal quadratic estimate at time `t + t` produces a
norm estimate at time `t` with decay factor `sqrt (q (t + t))`.  This is closer
to the actual Wilson Gibbs input than postulating norm decay directly, because
the left-hand side of `finite_quadratic_decay` is an OS two-point function. -/
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
  normDecaySlope_tendsto :
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

/-- The quadratic certificate supplies the symmetry package needed to move one
copy of `T_t` across the inner product. -/
theorem finitePhysicalSemigroup_isInnerSymmetric
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) :
    (C.finitePhysicalSemigroup n).IsInnerSymmetric := by
  exact
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange.toPhysicalSemigroup_isInnerSymmetric
      (Q.exchange n)

/-- The squared norm after time `t` is exactly the quadratic correlation at
time `t + t`. -/
theorem finiteOperator_norm_sq_eq_quadratic_doubleTime
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ‖C.finiteOperator n t phi‖ ^ 2 =
      inner ℝ (C.finiteOperator n (t + t) phi) phi := by
  have hadd :
      C.finiteOperator n (t + t) phi =
        C.finiteOperator n t (C.finiteOperator n t phi) := by
    rw [C.finiteOperator_add]
    rfl
  calc
    ‖C.finiteOperator n t phi‖ ^ 2 =
        inner ℝ (C.finiteOperator n t phi)
          (C.finiteOperator n t phi) := by
      simpa using
        (real_inner_self_eq_norm_sq (C.finiteOperator n t phi)).symm
    _ = inner ℝ phi
          (C.finiteOperator n t (C.finiteOperator n t phi)) :=
      Q.finitePhysicalSemigroup_isInnerSymmetric n
        t phi (C.finiteOperator n t phi)
    _ = inner ℝ
          (C.finiteOperator n t (C.finiteOperator n t phi)) phi :=
      real_inner_comm _ _
    _ = inner ℝ (C.finiteOperator n (t + t) phi) phi := by
      rw [hadd]

/-- A reflected quadratic correlation bound produces the corresponding norm
contraction with square-root double-time decay. -/
theorem finite_norm_decay
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
  have hsq :
      ‖C.finiteOperator n t phi‖ ^ 2 ≤
        Q.quadraticDecayFactor (t + t) * ‖phi‖ ^ 2 := by
    rw [Q.finiteOperator_norm_sq_eq_quadratic_doubleTime]
    exact Q.finite_quadratic_decay n (t + t) phi hphi
  have hq : 0 ≤ Q.quadraticDecayFactor (t + t) :=
    Q.quadraticDecayFactor_nonneg (t + t)
  have hsqrt : 0 ≤ Real.sqrt (Q.quadraticDecayFactor (t + t)) :=
    Real.sqrt_nonneg _
  have hrhs :
      0 ≤ Real.sqrt (Q.quadraticDecayFactor (t + t)) * ‖phi‖ :=
    mul_nonneg hsqrt (norm_nonneg phi)
  have hsq' :
      ‖C.finiteOperator n t phi‖ ^ 2 ≤
        (Real.sqrt (Q.quadraticDecayFactor (t + t)) * ‖phi‖) ^ 2 := by
    calc
      ‖C.finiteOperator n t phi‖ ^ 2 ≤
          Q.quadraticDecayFactor (t + t) * ‖phi‖ ^ 2 := hsq
      _ = (Real.sqrt (Q.quadraticDecayFactor (t + t)) * ‖phi‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hq]
  nlinarith [norm_nonneg (C.finiteOperator n t phi), hrhs]

/-- Convert the quadratic two-point-function certificate into the direct norm
vacuum-gap certificate used by the continuum transfer layer. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  decayFactor := fun t =>
    Real.sqrt (Q.quadraticDecayFactor (t + t))
  slope_tendsto := Q.normDecaySlope_tendsto
  exchange := Q.exchange
  finite_decay := Q.finite_norm_decay

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate

end MathlibAnalytic
end MGAP4D

end
