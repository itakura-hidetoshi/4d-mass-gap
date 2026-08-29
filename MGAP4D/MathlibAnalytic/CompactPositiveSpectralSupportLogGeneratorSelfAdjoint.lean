import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorDenseSymmetric
import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Module End
open scoped InnerProductSpace lp LinearPMap

noncomputable section

universe u

local instance spectralSupportLogGeneratorSelfAdjointComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Every vector in the adjoint domain of the logarithmic generator on the
actual positive spectral support already lies in its maximal logarithmic
domain.  The proof transports the adjoint identity to intrinsic spectral
coordinates, invokes maximality of the real weighted diagonal there, and then
pulls the resulting domain membership back to the actual support carrier. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_adjoint_domain_le
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (LinearPMap.adjoint
      (realHilbertCompactPositiveZeroSupportLogGenerator
        T hCompact hPositive)).domain ≤
      (realHilbertCompactPositiveZeroSupportLogGenerator
        T hCompact hPositive).domain := by
  classical
  let H := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A := realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
    T hCompact hPositive
  have hDenseH : Dense (H.domain : Set (realHilbertZeroEigenspaceSupport T)) := by
    simpa [H] using
      realHilbertCompactPositiveZeroSupportLogGenerator_dense_domain
        T hCompact hPositive
  have hAdjH : (LinearPMap.adjoint H).IsFormalAdjoint H :=
    LinearPMap.adjoint_isFormalAdjoint hDenseH
  have hInner (p q : realHilbertZeroEigenspaceSupport T) :
      inner ℝ (U p) (U q) = inner ℝ p q := by
    simpa [U] using
      realHilbertCompactPositive_zeroSupportHilbertSumEquiv_inner_map_map
        T hCompact hPositive p q
  intro y hy
  let ya : (LinearPMap.adjoint H).domain := ⟨y, hy⟩
  have hUyAdj : U y ∈ (LinearPMap.adjoint A).domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨U (LinearPMap.adjoint H ya), ?_⟩
    intro a
    have hxmem : U.symm (a : _) ∈ H.domain := by
      change U (U.symm (a : _)) ∈ A.domain
      simpa using a.property
    let x : H.domain := ⟨U.symm (a : _), hxmem⟩
    have haU : (a : _) = U (x : realHilbertZeroEigenspaceSupport T) := by
      simpa [x] using (U.apply_symm_apply (a : _)).symm
    have hHcoord : U (H x) = A a := by
      calc
        U (H x) =
            A ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩ := by
              simpa [H, U, A] using
                realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
                  T hCompact hPositive x
        _ = A a := by
          congr 1
          exact Subtype.ext (U.apply_symm_apply (a : _))
    calc
      inner ℝ (U (LinearPMap.adjoint H ya)) (a : _) =
          inner ℝ (U (LinearPMap.adjoint H ya))
            (U (x : realHilbertZeroEigenspaceSupport T)) := by rw [haU]
      _ = inner ℝ (LinearPMap.adjoint H ya)
            (x : realHilbertZeroEigenspaceSupport T) :=
          hInner _ _
      _ = inner ℝ (ya : realHilbertZeroEigenspaceSupport T) (H x) :=
          hAdjH ya x
      _ = inner ℝ (U (ya : realHilbertZeroEigenspaceSupport T)) (U (H x)) := by
          symm
          exact hInner _ _
      _ = inner ℝ (U y) (A a) := by
          rw [hHcoord]
          rfl
  have hUyDom : U y ∈ A.domain := by
    have h :=
      (realHilbertSumWeightedDiagonalLinearPMap_adjoint_domain_le
        (G := fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)) hUyAdj
    simpa [A, realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates] using h
  change U y ∈ A.domain
  exact hUyDom

/-- The adjoint of the actual-support logarithmic generator is contained in the
generator itself. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_adjoint_le
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    LinearPMap.adjoint
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive) ≤
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive := by
  let H := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  have hDense : Dense (H.domain : Set (realHilbertZeroEigenspaceSupport T)) := by
    simpa [H] using
      realHilbertCompactPositiveZeroSupportLogGenerator_dense_domain
        T hCompact hPositive
  have hSymm : H.IsFormalAdjoint H := by
    simpa [H] using
      realHilbertCompactPositiveZeroSupportLogGenerator_isFormalAdjoint_self
        T hCompact hPositive
  refine ⟨?_, ?_⟩
  · simpa [H] using
      realHilbertCompactPositiveZeroSupportLogGenerator_adjoint_domain_le
        T hCompact hPositive
  · intro x y hxy
    exact LinearPMap.adjoint_apply_eq hDense x (by
      intro z
      rw [hxy]
      exact hSymm y z)

/-- The logarithmic generator on the actual positive spectral support equals
its Hilbert-space adjoint. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_adjoint_eq
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    LinearPMap.adjoint
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive) =
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive := by
  apply le_antisymm
  · exact realHilbertCompactPositiveZeroSupportLogGenerator_adjoint_le
      T hCompact hPositive
  · exact
      (realHilbertCompactPositiveZeroSupportLogGenerator_isFormalAdjoint_self
        T hCompact hPositive).le_adjoint
          (realHilbertCompactPositiveZeroSupportLogGenerator_dense_domain
            T hCompact hPositive)

/-- The logarithmic Hamiltonian on the actual positive spectral support is
self-adjoint. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    IsSelfAdjoint
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive) := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact realHilbertCompactPositiveZeroSupportLogGenerator_adjoint_eq
    T hCompact hPositive

/-- Consequently the actual-support logarithmic generator is closed. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_isClosed
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).IsClosed :=
  (realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
    T hCompact hPositive).isClosed

open Classical in
/-- Every vector in a positive support eigenspace belongs to the logarithmic
generator domain. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_domain
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
    (v : realHilbertZeroEigenspaceSupport T) ∈
      (realHilbertCompactPositiveZeroSupportLogGenerator
        T hCompact hPositive).domain := by
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A := realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
    T hCompact hPositive
  have hUv : U (v : realHilbertZeroEigenspaceSupport T) = lp.single 2 mu v := by
    have h := congrArg (fun z => U z)
      (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
        T hCompact hPositive mu v)
    simpa [U] using h.symm
  change U (v : realHilbertZeroEigenspaceSupport T) ∈ A.domain
  rw [hUv]
  simpa [A, realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates] using
    (realHilbertSumWeightedDiagonal_single_mem_domain
      (G := fun nu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
      (fun nu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu)
      mu v)

open Classical in
/-- On each support eigenspace the actual logarithmic generator acts exactly by
`-log mu`. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_apply_eigenvector
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
    realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
        ⟨(v : realHilbertZeroEigenspaceSupport T),
          realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_domain
            T hCompact hPositive mu v⟩ =
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
        (v : realHilbertZeroEigenspaceSupport T) := by
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A := realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
    T hCompact hPositive
  let xv : (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).domain :=
    ⟨(v : realHilbertZeroEigenspaceSupport T),
      realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_domain
        T hCompact hPositive mu v⟩
  have hUv : U (v : realHilbertZeroEigenspaceSupport T) = lp.single 2 mu v := by
    have h := congrArg (fun z => U z)
      (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
        T hCompact hPositive mu v)
    simpa [U] using h.symm
  apply U.injective
  rw [U.map_smul]
  have hcoord :=
    realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
      T hCompact hPositive xv
  change U
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive xv) =
    A ⟨U (xv : realHilbertZeroEigenspaceSupport T), xv.property⟩ at hcoord
  rw [hcoord]
  rw [hUv]
  apply lp.ext
  funext nu
  rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply]
  by_cases hnu : nu = mu
  · subst nu
    simp [hUv, xv]
  · simp [hUv, xv, lp.single_apply, hnu]

/-- On a support eigenvector, exponentiating the negative logarithmic
eigenvalue reproduces the original support-restricted transfer action exactly.
This is the eigenvector-level `exp (-H) = T` statement and does not assert a
global functional-calculus operator equality. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_exp_neg_eigenvalue_smul_eq_transfer
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
    Real.exp (- realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) •
        (v : realHilbertZeroEigenspaceSupport T) =
      realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric
        (v : realHilbertZeroEigenspaceSupport T) := by
  symm
  exact
    realHilbertZeroEigenspaceSupportRestriction_apply_eigenvector_eq_exp_neg_logEnergy_smul
      T hPositive mu v

/-- Audit package for the actual-support logarithmic Hamiltonian stage: the
operator is self-adjoint, acts by `-log mu` on every positive support
eigenspace, and its scalar exponential reconstructs the transfer action there. -/
structure RealHilbertCompactPositiveZeroSupportLogGeneratorSelfAdjointPackage
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) : Prop where
  selfAdjoint : IsSelfAdjoint
    (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
  eigenvectorAction : ∀
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu),
    realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
        ⟨(v : realHilbertZeroEigenspaceSupport T),
          realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_domain
            T hCompact hPositive mu v⟩ =
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
        (v : realHilbertZeroEigenspaceSupport T)
  exponentialReconstructsTransfer : ∀
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu),
    Real.exp (- realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) •
        (v : realHilbertZeroEigenspaceSupport T) =
      realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric
        (v : realHilbertZeroEigenspaceSupport T)

/-- Construct the actual-support self-adjoint logarithmic Hamiltonian package. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorSelfAdjointPackage
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    RealHilbertCompactPositiveZeroSupportLogGeneratorSelfAdjointPackage
      T hCompact hPositive :=
  ⟨realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
      T hCompact hPositive,
    realHilbertCompactPositiveZeroSupportLogGenerator_apply_eigenvector
      T hCompact hPositive,
    realHilbertCompactPositiveZeroSupportLogGenerator_exp_neg_eigenvalue_smul_eq_transfer
      T hCompact hPositive⟩

end

end MathlibAnalytic
end MGAP4D
