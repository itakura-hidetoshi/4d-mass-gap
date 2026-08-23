import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalization
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End
open Set
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

/-- The full eigenvalue-one subspace of a bounded real Hilbert-space operator. -/
noncomputable def realHilbertTopEigenspace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E) : Submodule ℝ E :=
  Module.End.eigenspace (S : Module.End ℝ E) 1

@[simp] theorem realHilbertTopEigenspace_mem
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (x : E) :
    x ∈ realHilbertTopEigenspace S ↔ S x = x := by
  rw [realHilbertTopEigenspace, Module.End.mem_eigenspace_iff]
  simp

/-- The eigenvalue-one subspace of a bounded operator is closed. -/
theorem realHilbertTopEigenspace_isClosed
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E) :
    IsClosed ((realHilbertTopEigenspace S : Submodule ℝ E) : Set E) := by
  dsimp [realHilbertTopEigenspace]
  infer_instance

/-- Symmetry makes the orthogonal complement of the full eigenvalue-one
subspace invariant. -/
theorem realHilbertTopEigenspace_orthogonal_invariant
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    {y : E}
    (hy : y ∈ (realHilbertTopEigenspace S)ᗮ) :
    S y ∈ (realHilbertTopEigenspace S)ᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro x hx
  have hxfix : S x = x := (realHilbertTopEigenspace_mem S x).1 hx
  calc
    inner ℝ x (S y) = inner ℝ (S x) y := (hS x y).symm
    _ = inner ℝ x y := by rw [hxfix]
    _ = 0 := hy x hx

/-- Restriction of a symmetric bounded operator to the orthogonal complement
of its full eigenvalue-one subspace. -/
noncomputable def realHilbertTopEigenspaceOrthogonalRestriction
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) :
    (realHilbertTopEigenspace S)ᗮ →L[ℝ]
      (realHilbertTopEigenspace S)ᗮ :=
  ((S.comp (realHilbertTopEigenspace S)ᗮ.subtypeL).codRestrict
    (realHilbertTopEigenspace S)ᗮ
    (fun y => realHilbertTopEigenspace_orthogonal_invariant S hS y.property))

@[simp] theorem realHilbertTopEigenspaceOrthogonalRestriction_coe
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (y : (realHilbertTopEigenspace S)ᗮ) :
    ((realHilbertTopEigenspaceOrthogonalRestriction S hS y :
        (realHilbertTopEigenspace S)ᗮ) : E) = S (y : E) := rfl

/-- Positivity descends to the invariant top-eigenspace orthogonal
restriction. -/
theorem realHilbertTopEigenspaceOrthogonalRestriction_isPositive
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsPositive) :
    ((realHilbertTopEigenspaceOrthogonalRestriction S hS.isSymmetric :
        (realHilbertTopEigenspace S)ᗮ →L[ℝ]
          (realHilbertTopEigenspace S)ᗮ) :
      (realHilbertTopEigenspace S)ᗮ →ₗ[ℝ]
        (realHilbertTopEigenspace S)ᗮ).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    change inner ℝ (S (x : E)) (y : E) = inner ℝ (x : E) (S (y : E))
    exact hS.isSymmetric _ _
  · intro x
    change 0 ≤ RCLike.re (inner ℝ (S (x : E)) (x : E))
    exact hS.re_inner_nonneg_left (x : E)

/-- Compactness descends to the invariant top-eigenspace orthogonal
restriction. -/
theorem realHilbertTopEigenspaceOrthogonalRestriction_isCompact
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hCompact : IsCompactOperator S) :
    IsCompactOperator (realHilbertTopEigenspaceOrthogonalRestriction S hSymm) := by
  let K := (realHilbertTopEigenspace S)ᗮ
  have hpre : IsCompactOperator (S.comp K.subtypeL) :=
    hCompact.comp_clm K.subtypeL
  have hclosed : IsClosed (K : Set E) :=
    (realHilbertTopEigenspace S).isClosed_orthogonal
  have hcod := hpre.codRestrict
    (fun y => realHilbertTopEigenspace_orthogonal_invariant S hSymm y.property)
    hclosed
  simpa [realHilbertTopEigenspaceOrthogonalRestriction, K] using hcod

/-- If the ambient operator has norm one, its top-eigenspace orthogonal
restriction has norm at most one. -/
theorem realHilbertTopEigenspaceOrthogonalRestriction_norm_le_one
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hNorm : ‖S‖ = 1) :
    ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ≤ 1 := by
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  apply ContinuousLinearMap.opNorm_le_bound R zero_le_one
  intro y
  change ‖S (y : E)‖ ≤ 1 * ‖y‖
  rw [one_mul]
  have h := ContinuousLinearMap.le_opNorm S (y : E)
  rw [hNorm, one_mul] at h
  exact h

/-- A positive compact norm-one operator is strictly contractive on the
orthogonal complement of its entire eigenvalue-one space.  No simplicity of
the top eigenspace is assumed: if the restricted norm were one, compact
positivity would produce a unit fixed vector inside that orthogonal complement,
contradicting the trivial intersection with the full fixed-point space. -/
theorem realHilbertPositiveCompact_topEigenspaceOrthogonalRestriction_norm_lt_one
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hPositive : (S : E →ₗ[ℝ] E).IsPositive)
    (hCompact : IsCompactOperator S)
    (hNorm : ‖S‖ = 1) :
    ‖realHilbertTopEigenspaceOrthogonalRestriction S hPositive.isSymmetric‖ < 1 := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hPositive.isSymmetric
  have hle : ‖R‖ ≤ 1 := by
    simpa [R] using
      realHilbertTopEigenspaceOrthogonalRestriction_norm_le_one
        S hPositive.isSymmetric hNorm
  refine lt_of_le_of_ne hle ?_
  intro hReq
  have hReqR : ‖R‖ = 1 := by
    simpa [R] using hReq
  have hRne : R ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hReqR
    norm_num at hReqR
  have hex : ∃ u : Fᗮ, R u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hRne
    apply ContinuousLinearMap.ext
    intro u
    simpa using h u
  obtain ⟨u, huR⟩ := hex
  have hu : u ≠ 0 := by
    intro hu0
    apply huR
    rw [hu0, map_zero]
  let unit : Fᗮ := ‖u‖⁻¹ • u
  have hunit : ‖unit‖ = 1 := by
    have hunorm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    change ‖u‖⁻¹ * ‖u‖ = 1
    exact inv_mul_cancel₀ hunorm_ne
  have hRpos : ((R : Fᗮ →L[ℝ] Fᗮ) : Fᗮ →ₗ[ℝ] Fᗮ).IsPositive := by
    simpa [R, F] using
      realHilbertTopEigenspaceOrthogonalRestriction_isPositive S hPositive
  have hRcomp : IsCompactOperator R := by
    simpa [R] using
      realHilbertTopEigenspaceOrthogonalRestriction_isCompact
        S hPositive.isSymmetric hCompact
  obtain ⟨v, hvnorm, hveig⟩ :=
    realHilbertPositiveCompact_exists_unit_topEigenvector
      R unit hunit hRpos hRcomp
  have hvfixR : R v = v := by
    rw [hReqR, one_smul] at hveig
    exact hveig
  have hvfix : S (v : E) = (v : E) := by
    have h := congrArg (fun z : Fᗮ => (z : E)) hvfixR
    simpa [R, F] using h
  have hvF : (v : E) ∈ F := by
    simpa [F] using (realHilbertTopEigenspace_mem S (v : E)).2 hvfix
  have hvOrth : (v : E) ∈ Fᗮ := by
    simpa using v.property
  have hvzero : (v : E) = 0 := by
    have hbot := F.orthogonal_disjoint.le_bot ⟨hvF, hvOrth⟩
    simpa using hbot
  have hvzero' : v = 0 := Subtype.ext hvzero
  rw [hvzero', norm_zero] at hvnorm
  norm_num at hvnorm

local instance periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspace_completeSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- Full finite-volume physical eigenspace of the normalized transfer at
eigenvalue one.  It may contain more than the chosen vacuum vector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Submodule ℝ
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  realHilbertTopEigenspace
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta ↔
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta f = f := by
  exact realHilbertTopEigenspace_mem
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta) f

/-- The chosen normalized top eigenvector belongs to the full top eigenspace. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
  exact
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
      H N hN beta hbeta

/-- The full physical top eigenspace is closed. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsClosed
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta :
        Submodule ℝ
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) :
        Set (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) := by
  exact realHilbertTopEigenspace_isClosed
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

/-- Orthogonal complement of the full normalized-transfer top eigenspace. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Submodule ℝ
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta)ᗮ

/-- The normalized physical transfer remains positive. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  have hT := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isPositive
    H N hN beta hbeta
  have hc : 0 ≤ ‖T‖⁻¹ := inv_nonneg.mpr (norm_nonneg T)
  change ((‖T‖⁻¹ • T :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive
  simpa using hT.smul_of_nonneg hc

/-- The normalized physical transfer remains compact. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isCompact
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  have hT := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isCompact
    H N hN beta hbeta
  have h := hT.smul ‖T‖⁻¹
  simpa [T, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator] using h

/-- Normalized physical transfer restricted to the orthogonal complement of
its full top eigenspace. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta :=
  realHilbertTopEigenspaceOrthogonalRestriction
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta)

/-- The actual finite-volume normalized physical transfer is strictly
contractive away from its entire top eigenspace. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1 := by
  exact
    realHilbertPositiveCompact_topEigenspaceOrthogonalRestriction_norm_lt_one
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isCompact
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        H N hN beta hbeta)

/-- Positive finite-volume normalized-transfer separation from the top
eigenspace.  This is a finite-volume transfer quantity, not a continuum mass
gap. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  1 - ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta‖

/-- The finite-volume normalized-transfer separation is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  exact sub_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta)

/-- Audit-visible finite-volume top-eigenspace separation package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceContractionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  topEigenspaceClosed : IsClosed
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta :
      Submodule ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) :
      Set (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
  chosenVacuumInTopEigenspace :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta
  normalizedPositive :
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive
  normalizedCompact : IsCompactOperator
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)
  strictOrthogonalContraction :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1
  transferGapPositive :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta

/-- Construct the actual finite-volume top-eigenspace separation package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceContractionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceContractionPackage
      H N hN beta hbeta :=
  { topEigenspaceClosed :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
        H N hN beta hbeta
    chosenVacuumInTopEigenspace :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
        H N hN beta hbeta
    normalizedPositive :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta
    normalizedCompact :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isCompact
        H N hN beta hbeta
    strictOrthogonalContraction :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
    transferGapPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_pos
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
