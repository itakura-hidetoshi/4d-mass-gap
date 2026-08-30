import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGenerator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Module End
open scoped InnerProductSpace lp

noncomputable section

universe u

local instance logGeneratorTransferEigenspaceBridgeSupportComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

open Classical in
/-- Every strictly-positive transfer eigenspace lies in the natural domain of
`-log T`, and the logarithmic generator acts there by the exact spectral
energy `-log mu`.  This is the actual-domain half of the transfer/generator
eigenmode bridge. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_domain_action
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
    ∃ x : (realHilbertCompactPositiveZeroSupportLogGenerator
        T hCompact hPositive).domain,
      (x : realHilbertZeroEigenspaceSupport T) =
          (v : realHilbertZeroEigenspaceSupport T) ∧
        realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x =
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
            (v : realHilbertZeroEigenspaceSupport T) := by
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let C := realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates T hCompact hPositive
  have hUv : U (v : realHilbertZeroEigenspaceSupport T) = lp.single 2 mu v := by
    have h := congrArg U
      (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
        T hCompact hPositive mu v)
    simpa [U] using h.symm
  have hvDomain : (v : realHilbertZeroEigenspaceSupport T) ∈ A.domain := by
    change U (v : realHilbertZeroEigenspaceSupport T) ∈ C.domain
    rw [hUv]
    rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_domain_mem_iff]
    let hsingle :
        lp
          (fun nu : Eigenvalues
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
            eigenspace
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
          2 :=
      lp.single 2 mu
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • v)
    have hmem := hsingle.property
    simpa only [hsingle, lp.single_apply] using hmem
  let x : A.domain := ⟨(v : realHilbertZeroEigenspaceSupport T), hvDomain⟩
  refine ⟨x, rfl, ?_⟩
  apply U.injective
  have hcoords :=
    realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
      T hCompact hPositive x
  change U (A x) =
    U (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
      (v : realHilbertZeroEigenspaceSupport T))
  rw [hcoords]
  apply lp.ext
  funext nu
  rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply]
  change realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu •
      (U (v : realHilbertZeroEigenspaceSupport T)) nu =
    (U (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
      (v : realHilbertZeroEigenspaceSupport T))) nu
  rw [hUv]
  rw [U.map_smul]
  rw [hUv]
  by_cases hnu : nu = mu
  · subst nu
    simp
  · simp [hnu]

open Classical in
/-- On each positive support eigenspace, the bounded transfer and its
logarithmic generator carry exactly the mutually inverse spectral labels
`mu` and `E(mu) = -log mu`, with `mu = exp (-E(mu))`. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_transfer_eigenspace_bridge
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
    ∃ x : (realHilbertCompactPositiveZeroSupportLogGenerator
        T hCompact hPositive).domain,
      (x : realHilbertZeroEigenspaceSupport T) =
          (v : realHilbertZeroEigenspaceSupport T) ∧
        realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x =
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
            (v : realHilbertZeroEigenspaceSupport T) ∧
        realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric
            (v : realHilbertZeroEigenspaceSupport T) =
          Real.exp (- realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) •
            (v : realHilbertZeroEigenspaceSupport T) := by
  obtain ⟨x, hx, hAx⟩ :=
    realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_domain_action
      T hCompact hPositive mu v
  refine ⟨x, hx, hAx, ?_⟩
  exact
    realHilbertZeroEigenspaceSupportRestriction_apply_eigenvector_eq_exp_neg_logEnergy_smul
      T hPositive mu v

end

end MathlibAnalytic
end MGAP4D