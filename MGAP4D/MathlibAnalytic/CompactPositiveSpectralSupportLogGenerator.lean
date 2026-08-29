import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportHilbertSumEquiv
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralLogWeights
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Module End
open scoped InnerProductSpace lp

noncomputable section

universe u

local instance spectralSupportLogGeneratorComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Natural domain of the logarithmic generator on the actual positive spectral
support.  A support vector is in the domain exactly when its intrinsic spectral
coordinates remain square-summable after multiplication by `-log mu`. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGeneratorDomain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    Submodule ℝ (realHilbertZeroEigenspaceSupport T) where
  carrier := {x |
    Memℓp
      (fun mu =>
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
          (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
            T hCompact hPositive x) mu)
      2}
  zero_mem' := by
    have hzero : Memℓp
        (0 : (mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T))) →
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) 2 := zero_memℓp
    simpa using hzero
  add_mem' := by
    intro x y hx hy
    simpa only [LinearIsometryEquiv.map_add, lp.coeFn_add, Pi.add_apply, smul_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    have h := hx.const_smul c
    change Memℓp
      (fun mu => c •
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
          (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
            T hCompact hPositive x) mu)) 2 at h
    simpa only [LinearIsometryEquiv.map_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_smul, mul_comm] using h

@[simp] theorem mem_realHilbertCompactPositiveZeroSupportLogGeneratorDomain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (x : realHilbertZeroEigenspaceSupport T) :
    x ∈ realHilbertCompactPositiveZeroSupportLogGeneratorDomain T hCompact hPositive ↔
      Memℓp
        (fun mu =>
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
            (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
              T hCompact hPositive x) mu)
        2 := Iff.rfl

/-- The logarithmic Hamiltonian directly on the actual positive spectral
support.  It is the intrinsic diagonal multiplication by `-log mu`, transported
back through the canonical eigenspace Hilbert-sum equivalence. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGenerator
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    realHilbertZeroEigenspaceSupport T →ₗ.[ℝ]
      realHilbertZeroEigenspaceSupport T where
  domain := realHilbertCompactPositiveZeroSupportLogGeneratorDomain T hCompact hPositive
  toFun :=
    { toFun := fun x =>
        (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive).symm
          ⟨fun mu =>
              realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
                (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
                  T hCompact hPositive (x : realHilbertZeroEigenspaceSupport T)) mu,
            x.property⟩
      map_add' := by
        intro x y
        apply (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive).injective
        apply lp.ext
        funext mu
        simp [smul_add]
      map_smul' := by
        intro c x
        apply (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive).injective
        apply lp.ext
        funext mu
        simp [smul_smul, mul_comm] }

@[simp] theorem realHilbertCompactPositiveZeroSupportLogGenerator_domain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain =
      realHilbertCompactPositiveZeroSupportLogGeneratorDomain T hCompact hPositive := rfl

/-- Exact coordinate formula for the support logarithmic generator. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain) :
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
        T hCompact hPositive
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x) =
      ⟨fun mu =>
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
            (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
              T hCompact hPositive
              (x : realHilbertZeroEigenspaceSupport T)) mu,
        x.property⟩ := by
  exact (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
    T hCompact hPositive).apply_symm_apply _

end

end MathlibAnalytic
end MGAP4D
