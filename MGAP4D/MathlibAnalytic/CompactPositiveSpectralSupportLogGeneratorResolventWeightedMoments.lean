import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventCoordinates
import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalQuadraticCoercive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp LinearPMap

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

local instance spectralSupportResolventWeightedMomentsComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Every power of the canonical ambient resolvent remains diagonal in the
intrinsic spectral coordinates.  The `k`-th power multiplies coordinate `mu`
by the `k`-th power of the positive shifted reciprocal energy.

This is the exact coordinate bridge from resolvent powers to weighted moments. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_pow_coordinates
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (c : ℝ)
    (hc : 0 < c)
    (hLower : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (hNorm : ∀ x : (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ≤
        ‖realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x‖)
    (hKer : ∀ x : (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).domain,
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x = 0 → x = 0)
    (hSurj : Function.Surjective
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (k : ℕ)
    (v : realHilbertZeroEigenspaceSupport T)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
    let U :=
      realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
        T hCompact hPositive
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    (U (((F lambda) ^ k) v)) mu =
      ((realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹ ^ k) •
        (U v) mu := by
  dsimp only
  let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  induction k with
  | zero =>
      simp [F, U]
  | succ k ih =>
      rw [pow_succ]
      change (U (F lambda (((F lambda) ^ k) v))) mu = _
      have hcoord :=
        realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_coordinates
          T hCompact hPositive c hc hLower hNorm hKer hSurj
          lambda hlambda (((F lambda) ^ k) v) mu
      rw [show (U (F lambda (((F lambda) ^ k) v))) mu =
          (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹ •
            (U (((F lambda) ^ k) v)) mu by
        simpa [A, U, F] using hcoord]
      rw [ih, smul_smul]
      simp only [pow_succ]
      rw [mul_comm]

/-- The quadratic resolvent moment is the positive weighted sum of shifted
spectral reciprocals.  The weight of coordinate `mu` is exactly
`‖(U v) mu‖²`, hence it is positive precisely on the state-visible spectral
coordinates.

This formula isolates the remaining asymptotic problem as a scalar weighted
moment-ratio theorem. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_pow_quadratic_eq_tsum
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (c : ℝ)
    (hc : 0 < c)
    (hLower : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (hNorm : ∀ x : (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ≤
        ‖realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x‖)
    (hKer : ∀ x : (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).domain,
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x = 0 → x = 0)
    (hSurj : Function.Surjective
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (k : ℕ)
    (v : realHilbertZeroEigenspaceSupport T) :
    let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
    let U :=
      realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
        T hCompact hPositive
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    inner ℝ (((F lambda) ^ k) v) v =
      ∑' mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
        ((realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹ ^ k) *
          ‖(U v) mu‖ ^ 2 := by
  dsimp only
  let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  calc
    inner ℝ (((F lambda) ^ k) v) v =
        inner ℝ (U (((F lambda) ^ k) v)) (U v) := by
      symm
      exact U.inner_map_map _ _
    _ = ∑' mu, inner ℝ ((U (((F lambda) ^ k) v)) mu) ((U v) mu) :=
      lp.inner_eq_tsum _ _
    _ = ∑' mu,
        ((realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹ ^ k) *
          ‖(U v) mu‖ ^ 2 := by
      apply tsum_congr
      intro mu
      rw [show (U (((F lambda) ^ k) v)) mu =
          ((realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹ ^ k) •
            (U v) mu by
        simpa [A, U, F] using
          (realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_pow_coordinates
            T hCompact hPositive c hc hLower hNorm hKer hSurj
            lambda hlambda k v mu)]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]

end

end MathlibAnalytic
end MGAP4D
