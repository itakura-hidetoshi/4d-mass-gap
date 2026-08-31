import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGenerator
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventDifferentiability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp LinearPMap

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

local instance spectralSupportResolventCoordinatesComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- The ambient resolvent of the compact-positive support logarithmic generator
is exactly diagonal in the intrinsic Hilbert-sum spectral coordinates.

For every coordinate `mu`, the canonical inverse of `A - lambda` acts by the
scalar reciprocal `(E_mu - lambda)⁻¹`.  The proof stays on the true maximal
domain of the partially defined logarithmic generator: a domain preimage of
the ambient resolvent is chosen first, the already-proved coordinate formula
for `A` is applied there, and only then is the scalar equation solved.

The pointwise lower bound on logarithmic energies is used only to ensure that
`E_mu - lambda` is nonzero throughout the coercive gap. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_coordinates
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
    (U (F lambda v)) mu =
      (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹ •
        (U v) mu := by
  dsimp only
  let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj lambda hlambda v with
    ⟨x, hshift, hFx⟩
  have hlambdaLtC : lambda < c :=
    lt_of_le_of_lt (le_abs_self lambda) hlambda
  have hEnergyGt :
      lambda < realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu :=
    lt_of_lt_of_le hlambdaLtC (hLower mu)
  have hdiff :
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda ≠ 0 :=
    ne_of_gt (sub_pos.mpr hEnergyGt)
  have hAxCoord :
      (U (A x)) mu =
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
          (U (x : realHilbertZeroEigenspaceSupport T)) mu := by
    have hcoord :=
      realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
        T hCompact hPositive x
    have hcomponent := congrArg (fun y => y mu) hcoord
    simpa [A, U, realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply]
      using hcomponent
  have hShiftCoord :
      (U v) mu =
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda) •
          (U (x : realHilbertZeroEigenspaceSupport T)) mu := by
    calc
      (U v) mu = (U (realLinearPMapDomainShift A lambda x)) mu := by rw [hshift]
      _ = (U (A x - lambda • (x : realHilbertZeroEigenspaceSupport T))) mu := by rfl
      _ = (U (A x)) mu - lambda • (U (x : realHilbertZeroEigenspaceSupport T)) mu := by
        rw [U.map_sub, U.map_smul]
        rfl
      _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
            (U (x : realHilbertZeroEigenspaceSupport T)) mu -
          lambda • (U (x : realHilbertZeroEigenspaceSupport T)) mu := by
        rw [hAxCoord]
      _ = (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda) •
          (U (x : realHilbertZeroEigenspaceSupport T)) mu := by
        exact (sub_smul
          (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
          lambda
          ((U (x : realHilbertZeroEigenspaceSupport T)) mu)).symm
  have hxCoord :
      (U (x : realHilbertZeroEigenspaceSupport T)) mu =
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹ •
          (U v) mu := by
    rw [hShiftCoord, smul_smul, inv_mul_cancel₀ hdiff, one_smul]
  rw [show F lambda v = (x : realHilbertZeroEigenspaceSupport T) by simpa [F] using hFx]
  exact hxCoord

end

end MathlibAnalytic
end MGAP4D
