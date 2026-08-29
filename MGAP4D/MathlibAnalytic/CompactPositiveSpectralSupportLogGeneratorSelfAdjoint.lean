import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorDenseSymmetric
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

open Classical in
/-- The adjoint of the logarithmic generator on the actual positive spectral
support has the expected logarithmic coordinate action.  This is proved
entirely on the actual support carrier: a one-eigenspace test vector is pulled
back through the canonical spectral isometry, so no adjoint is ever formed on
the specialized `lp` carrier and the `lp` module-instance diamond is avoided. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_adjoint_apply_coord
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (y : (LinearPMap.adjoint
      (realHilbertCompactPositiveZeroSupportLogGenerator
        T hCompact hPositive)).domain)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
        T hCompact hPositive)
        (LinearPMap.adjoint
          (realHilbertCompactPositiveZeroSupportLogGenerator
            T hCompact hPositive) y) mu =
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
        (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive)
          (y : realHilbertZeroEigenspaceSupport T) mu := by
  let H := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
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
  change U (LinearPMap.adjoint H y) mu =
    realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
      U (y : realHilbertZeroEigenspaceSupport T) mu
  apply
    (dense_univ : Dense
      (Set.univ : Set
        (eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu))).eq_of_inner_left ℝ
  intro a ha
  let s0 :
      lp
        (fun nu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
        2 :=
    lp.single 2 mu a
  have hs0 :
      s0 ∈
        (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive).domain := by
    rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_domain_mem_iff]
    have hsingle :
        Memℓp
          (fun nu =>
            (lp.single 2 mu
              (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • a) :
              lp
                (fun rho : Eigenvalues
                  (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                    Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
                  eigenspace
                    (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                      Module.End ℝ (realHilbertZeroEigenspaceSupport T)) rho)
                2) nu)
          2 :=
      (lp.single 2 mu
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • a) :
        lp
          (fun rho : Eigenvalues
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
            eigenspace
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) rho)
          2).property
    convert hsingle using 1
    funext nu
    by_cases hnu : nu = mu
    · subst nu
      simp [s0]
    · simp [s0, lp.single_apply, hnu]
  have hsBase : U.symm s0 ∈ H.domain := by
    change
      U (U.symm s0) ∈
        (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive).domain
    simpa using hs0
  let s : H.domain := ⟨U.symm s0, hsBase⟩
  have hsCoord : U (s : realHilbertZeroEigenspaceSupport T) = s0 := by
    simp [s]
  have hHsingle :
      U (H s) =
        lp.single 2 mu
          (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • a) := by
    apply lp.ext
    funext nu
    have hcoord := congrArg (fun z => z nu)
      (realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
        T hCompact hPositive s)
    calc
      U (H s) nu =
          realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
            T hCompact hPositive
            ⟨U (s : realHilbertZeroEigenspaceSupport T), s.property⟩ nu := by
        simpa [H, U] using hcoord
      _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu •
          U (s : realHilbertZeroEigenspaceSupport T) nu := by
        exact
          realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply
            T hCompact hPositive
            ⟨U (s : realHilbertZeroEigenspaceSupport T), s.property⟩ nu
      _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu • s0 nu := by
        rw [hsCoord]
      _ =
          (lp.single 2 mu
            (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • a) :
            lp
              (fun rho : Eigenvalues
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
                eigenspace
                  (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                    Module.End ℝ (realHilbertZeroEigenspaceSupport T)) rho)
              2) nu := by
        by_cases hnu : nu = mu
        · subst nu
          simp [s0]
        · simp [s0, lp.single_apply, hnu]
  have hAdj := hAdjH y s
  have hAdjCoord :
      inner ℝ (U (LinearPMap.adjoint H y))
          (U (s : realHilbertZeroEigenspaceSupport T)) =
        inner ℝ (U (y : realHilbertZeroEigenspaceSupport T)) (U (H s)) := by
    calc
      inner ℝ (U (LinearPMap.adjoint H y))
          (U (s : realHilbertZeroEigenspaceSupport T)) =
          inner ℝ (LinearPMap.adjoint H y)
            (s : realHilbertZeroEigenspaceSupport T) := hInner _ _
      _ = inner ℝ (y : realHilbertZeroEigenspaceSupport T) (H s) := hAdj
      _ = inner ℝ (U (y : realHilbertZeroEigenspaceSupport T)) (U (H s)) := by
        symm
        exact hInner _ _
  rw [hsCoord, hHsingle, lp.inner_single_right, lp.inner_single_right] at hAdjCoord
  simpa [real_inner_smul_left, real_inner_smul_right] using hAdjCoord

/-- Every vector in the adjoint domain of the logarithmic generator on the
actual positive spectral support already lies in its maximal logarithmic
domain.  The proof uses the actual-support adjoint coordinate formula above
and square summability of the transported adjoint vector; no coordinate-space
adjoint is instantiated. -/
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
  intro y hy
  let ya : (LinearPMap.adjoint H).domain := ⟨y, hy⟩
  change
    U y ∈
      (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive).domain
  rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_domain_mem_iff]
  have hz :
      Memℓp
        (fun mu => U (LinearPMap.adjoint H ya) mu)
        2 :=
    (U (LinearPMap.adjoint H ya)).property
  convert hz using 1
  funext mu
  exact
    (realHilbertCompactPositiveZeroSupportLogGenerator_adjoint_apply_coord
      T hCompact hPositive ya mu).symm

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
generator domain.  Instead of specializing the generic `lp.single` domain
lemma, square summability is proved from the transported vector itself; this
keeps the intrinsic `Eigenvalues` decidable-equality instance out of the
statement. -/
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
  have hUv : U (v : realHilbertZeroEigenspaceSupport T) = lp.single 2 mu v := by
    have h := congrArg (fun z => U z)
      (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
        T hCompact hPositive mu v)
    simpa [U] using h.symm
  have hzero (nu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
      (hnu : nu ≠ mu) :
      U (v : realHilbertZeroEigenspaceSupport T) nu = 0 := by
    have hpoint := congrArg (fun z => z nu) hUv
    simpa [lp.single_apply, hnu] using hpoint
  change
    U (v : realHilbertZeroEigenspaceSupport T) ∈
      (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive).domain
  rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_domain_mem_iff]
  have hmem :
      Memℓp
        (fun nu =>
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
            U (v : realHilbertZeroEigenspaceSupport T) nu)
        2 :=
    (U (v : realHilbertZeroEigenspaceSupport T)).property.const_smul
      (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
  convert hmem using 1
  funext nu
  by_cases hnu : nu = mu
  · subst nu
    rfl
  · rw [hzero nu hnu]
    simp

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
  let H := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let xv : H.domain :=
    ⟨(v : realHilbertZeroEigenspaceSupport T),
      realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_domain
        T hCompact hPositive mu v⟩
  have hUv : U (v : realHilbertZeroEigenspaceSupport T) = lp.single 2 mu v := by
    have h := congrArg (fun z => U z)
      (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
        T hCompact hPositive mu v)
    simpa [U] using h.symm
  have hzero (nu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
      (hnu : nu ≠ mu) :
      U (v : realHilbertZeroEigenspaceSupport T) nu = 0 := by
    have hpoint := congrArg (fun z => z nu) hUv
    simpa [lp.single_apply, hnu] using hpoint
  change H xv =
    realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
      (v : realHilbertZeroEigenspaceSupport T)
  apply U.injective
  rw [U.map_smul]
  apply lp.ext
  funext nu
  have hcoord := congrArg (fun z => z nu)
    (realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
      T hCompact hPositive xv)
  calc
    U (H xv) nu =
        realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive
          ⟨U (xv : realHilbertZeroEigenspaceSupport T), xv.property⟩ nu := by
      simpa [H, U] using hcoord
    _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu •
        U (xv : realHilbertZeroEigenspaceSupport T) nu := by
      exact
        realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply
          T hCompact hPositive
          ⟨U (xv : realHilbertZeroEigenspaceSupport T), xv.property⟩ nu
    _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
        U (v : realHilbertZeroEigenspaceSupport T) nu := by
      change
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu •
            U (v : realHilbertZeroEigenspaceSupport T) nu =
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
            U (v : realHilbertZeroEigenspaceSupport T) nu
      by_cases hnu : nu = mu
      · subst nu
        rfl
      · rw [hzero nu hnu]
        simp

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
      T hPositive⟩

end

end MathlibAnalytic
end MGAP4D
