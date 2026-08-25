import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferSpectrumIsolation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

universe u

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- The full eigenvalue-one subspace of a bounded complex Hilbert-space operator. -/
noncomputable def complexHilbertTopEigenspace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : E →L[ℂ] E) : Submodule ℂ E :=
  Module.End.eigenspace (S : Module.End ℂ E) 1

@[simp] theorem complexHilbertTopEigenspace_mem
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : E →L[ℂ] E)
    (x : E) :
    x ∈ complexHilbertTopEigenspace S ↔ S x = x := by
  rw [complexHilbertTopEigenspace, Module.End.mem_eigenspace_iff]
  simp

/-- The complex eigenvalue-one subspace is closed. -/
theorem complexHilbertTopEigenspace_isClosed
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : E →L[ℂ] E) :
    IsClosed ((complexHilbertTopEigenspace S : Submodule ℂ E) : Set E) := by
  dsimp [complexHilbertTopEigenspace]
  infer_instance

local instance complexHilbertTopEigenspace_completeSpace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E) :
    CompleteSpace (complexHilbertTopEigenspace S) :=
  (complexHilbertTopEigenspace_isClosed S).completeSpace_coe

local instance complexTopProjectionRealHilbertTopEigenspace_completeSpace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) :
    CompleteSpace (realHilbertTopEigenspace S) :=
  (realHilbertTopEigenspace_isClosed S).completeSpace_coe

/-- Canonical Mathlib orthogonal projection onto the entire complex fixed-point space. -/
noncomputable def complexHilbertTopEigenspaceProjection
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E) : E →L[ℂ] E :=
  (complexHilbertTopEigenspace S).starProjection

/-- Symmetry preserves the orthogonal complement of the full complex top eigenspace. -/
theorem complexHilbertTopEigenspace_orthogonal_invariant
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : E →L[ℂ] E)
    (hS : (S : E →ₗ[ℂ] E).IsSymmetric)
    {y : E}
    (hy : y ∈ (complexHilbertTopEigenspace S)ᗮ) :
    S y ∈ (complexHilbertTopEigenspace S)ᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro x hx
  have hxFix : S x = x := (complexHilbertTopEigenspace_mem S x).1 hx
  calc
    inner ℂ x (S y) = inner ℂ (S x) y := (hS x y).symm
    _ = inner ℂ x y := by rw [hxFix]
    _ = 0 := hy x hx

/-- Restriction of a symmetric complex operator to the orthogonal complement of its full top space. -/
noncomputable def complexHilbertTopEigenspaceOrthogonalRestriction
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : E →L[ℂ] E)
    (hS : (S : E →ₗ[ℂ] E).IsSymmetric) :
    (complexHilbertTopEigenspace S)ᗮ →L[ℂ]
      (complexHilbertTopEigenspace S)ᗮ :=
  ((S.comp (complexHilbertTopEigenspace S)ᗮ.subtypeL).codRestrict
    (complexHilbertTopEigenspace S)ᗮ
    (fun y => complexHilbertTopEigenspace_orthogonal_invariant S hS y.property))

@[simp] theorem complexHilbertTopEigenspaceOrthogonalRestriction_coe
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : E →L[ℂ] E)
    (hS : (S : E →ₗ[ℂ] E).IsSymmetric)
    (y : (complexHilbertTopEigenspace S)ᗮ) :
    ((complexHilbertTopEigenspaceOrthogonalRestriction S hS y :
        (complexHilbertTopEigenspace S)ᗮ) : E) = S (y : E) := rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_sub
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N (f - g) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f -
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g := by
  change periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPartCLM H N (f - g) =
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPartCLM H N f -
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPartCLM H N g
  exact map_sub _ _ _

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_sub
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N (f - g) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f -
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g := by
  change periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPartCLM H N (f - g) =
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPartCLM H N f -
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPartCLM H N g
  exact map_sub _ _ _

local instance periodicHypercubicEvenSpecialUnitaryComplexTopProjectionRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexTopProjectionComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- Full complex physical eigenspace at eigenvalue one for the normalized Wilson transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Submodule ℂ (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  complexHilbertTopEigenspace
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta ↔
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta f = f := by
  exact complexHilbertTopEigenspace_mem
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta) f

/-- Complex top membership is exactly top membership of both genuine real physical components. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem_iff_components
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta ↔
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
            H N hN beta hbeta ∧
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
            H N hN beta hbeta := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let SC := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  constructor
  · intro hf
    have hFix : SC f = f := by
      simpa [SC] using
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem
          H N hN beta hbeta f).1 hf
    have hre := congrArg
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N) hFix
    have him := congrArg
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N) hFix
    constructor
    · rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
      simpa [SC, S,
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply] using hre
    · rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
      simpa [SC, S,
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply] using him
  · rintro ⟨hre, him⟩
    rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem]
    apply periodicHypercubicEvenSpecialUnitaryComplexPhysical_ext_components H N
    · rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem] at hre
      simpa [periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply] using hre
    · rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem] at him
      simpa [periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply] using him

/-- Orthogonality to the whole complex top sector is exactly simultaneous real-component orthogonality. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal_mem_iff_components
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    f ∈ (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ ↔
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f ∈
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
            H N hN beta hbeta)ᗮ ∧
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f ∈
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
            H N hN beta hbeta)ᗮ := by
  let FC := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
    H N hN beta hbeta
  let FR := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta
  constructor
  · intro hf
    rw [Submodule.mem_orthogonal] at hf
    constructor
    · rw [Submodule.mem_orthogonal]
      intro x hx
      let xc := periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N x
      have hxc : xc ∈ FC := by
        apply (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem_iff_components
          H N hN beta hbeta xc).2
        constructor
        · simpa [xc, FR] using hx
        · simp [xc]
      have hinner := hf xc hxc
      rw [periodicHypercubicEvenSpecialUnitaryComplexPhysical_inner_components] at hinner
      have hre := congrArg Complex.re hinner
      simpa [xc] using hre
    · rw [Submodule.mem_orthogonal]
      intro x hx
      let xc := periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N x
      have hxc : xc ∈ FC := by
        apply (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem_iff_components
          H N hN beta hbeta xc).2
        constructor
        · simpa [xc, FR] using hx
        · simp [xc]
      have hinner := hf xc hxc
      rw [periodicHypercubicEvenSpecialUnitaryComplexPhysical_inner_components] at hinner
      have him := congrArg Complex.im hinner
      simpa [xc] using him
  · rintro ⟨hre, him⟩
    rw [Submodule.mem_orthogonal] at hre him ⊢
    intro g hg
    have hgComp :=
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem_iff_components
        H N hN beta hbeta g).1 (by simpa [FC] using hg)
    have hrr := hre
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g) hgComp.1
    have hir := hre
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g) hgComp.2
    have hri := him
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g) hgComp.1
    have hii := him
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g) hgComp.2
    have hrrC :
        ((inner ℝ
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g)
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f) : ℝ) : ℂ) = 0 :=
      congrArg (fun r : ℝ => (r : ℂ)) hrr
    have hirC :
        ((inner ℝ
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g)
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f) : ℝ) : ℂ) = 0 :=
      congrArg (fun r : ℝ => (r : ℂ)) hir
    have hriC :
        ((inner ℝ
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g)
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f) : ℝ) : ℂ) = 0 :=
      congrArg (fun r : ℝ => (r : ℂ)) hri
    have hiiC :
        ((inner ℝ
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g)
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f) : ℝ) : ℂ) = 0 :=
      congrArg (fun r : ℝ => (r : ℂ)) hii
    rw [periodicHypercubicEvenSpecialUnitaryComplexPhysical_inner_components]
    rw [hrrC, hiiC, hriC, hirC]
    norm_num

/-- Canonical complex orthogonal projection onto the full normalized-transfer top sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  complexHilbertTopEigenspaceProjection
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

/-- The canonical complex top projection is exactly the scalar extension of the canonical real top projection. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_eq_complexification
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta) := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let SC := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let FR := realHilbertTopEigenspace S
  let FC := complexHilbertTopEigenspace SC
  let PR := realHilbertTopEigenspaceProjection S
  let Q := periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N PR
  have hQre
      (x : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N (Q x) =
        PR (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N x) := by
    simp [Q, periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply]
  have hQim
      (x : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N (Q x) =
        PR (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N x) := by
    simp [Q, periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply]
  apply ContinuousLinearMap.ext
  intro f
  change FC.starProjection f = Q f
  apply FC.eq_starProjection_of_mem_orthogonal
  · apply (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem_iff_components
      H N hN beta hbeta (Q f)).2
    constructor
    · rw [hQre]
      change (realHilbertTopEigenspace S).starProjection
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f) ∈
        realHilbertTopEigenspace S
      exact (realHilbertTopEigenspace S).starProjection_apply_mem _
    · rw [hQim]
      change (realHilbertTopEigenspace S).starProjection
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f) ∈
        realHilbertTopEigenspace S
      exact (realHilbertTopEigenspace S).starProjection_apply_mem _
  · apply (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal_mem_iff_components
      H N hN beta hbeta (f - Q f)).2
    constructor
    · rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_sub, hQre]
      change periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f -
          (realHilbertTopEigenspace S).starProjection
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f) ∈
        (realHilbertTopEigenspace S)ᗮ
      exact (realHilbertTopEigenspace S).sub_starProjection_mem_orthogonal _
    · rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_sub, hQim]
      change periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f -
          (realHilbertTopEigenspace S).starProjection
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f) ∈
        (realHilbertTopEigenspace S)ᗮ
      exact (realHilbertTopEigenspace S).sub_starProjection_mem_orthogonal _

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_range
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta).range =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta := by
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace,
    complexHilbertTopEigenspaceProjection] using
    (Submodule.range_starProjection
      (complexHilbertTopEigenspace
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta)))

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_apply_eq_zero_iff
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta f = 0 ↔
      f ∈ (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ := by
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace,
    complexHilbertTopEigenspaceProjection] using
    (Submodule.starProjection_apply_eq_zero_iff
      (K := complexHilbertTopEigenspace
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta)) (v := f))

/-- Orthogonal complement of the full complex normalized-transfer top eigenspace. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Submodule ℂ (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
    H N hN beta hbeta)ᗮ

local instance periodicHypercubicEvenSpecialUnitaryComplexTopOrthogonalNormedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  Submodule.normedSpace
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

local instance periodicHypercubicEvenSpecialUnitaryRealTopOrthogonalNormedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  Submodule.normedSpace
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

/-- The normalized complex transfer restricted to its full-top orthogonal complement. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →L[ℂ]
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta :=
  complexHilbertTopEigenspaceOrthogonalRestriction
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta)

/-- The complex excited-sector restriction has exactly the same norm as the genuine real restriction. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_real
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ =
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let SC := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let hS := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
    H N hN beta hbeta
  let hSC := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isSymmetric
    H N hN beta hbeta
  let RR := realHilbertTopEigenspaceOrthogonalRestriction S hS
  let RC := complexHilbertTopEigenspaceOrthogonalRestriction SC hSC
  have hnorm : ‖RC‖ = ‖RR‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound RC (norm_nonneg RR)
      intro y
      have hyConcrete :
          (y : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) ∈
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
              H N hN beta hbeta)ᗮ := by
        simpa [SC, periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace] using
          y.property
      have hyCompConcrete :=
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal_mem_iff_components
          H N hN beta hbeta
          (y : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)).1 hyConcrete
      have hyComp :
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N y ∈
              (realHilbertTopEigenspace S)ᗮ ∧
            periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N y ∈
              (realHilbertTopEigenspace S)ᗮ := by
        simpa [S, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace] using
          hyCompConcrete
      let yr : (realHilbertTopEigenspace S)ᗮ :=
        ⟨periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N y, hyComp.1⟩
      let yi : (realHilbertTopEigenspace S)ᗮ :=
        ⟨periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N y, hyComp.2⟩
      have hIn : ‖y‖ ^ 2 = ‖yr‖ ^ 2 + ‖yi‖ ^ 2 := by
        simpa [yr, yi] using
          periodicHypercubicEvenSpecialUnitaryComplexPhysical_norm_sq H N
            (y : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
      have hReOut :
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N
            (((RC y : (complexHilbertTopEigenspace SC)ᗮ) :
              PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) =
            (((RR yr : (realHilbertTopEigenspace S)ᗮ) :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) := by
        change periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta
              (y : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) =
          periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N y)
        simp [periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
          periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply]
      have hImOut :
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N
            (((RC y : (complexHilbertTopEigenspace SC)ᗮ) :
              PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) =
            (((RR yi : (realHilbertTopEigenspace S)ᗮ) :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) := by
        change periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta
              (y : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) =
          periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N y)
        simp [periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
          periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply]
      have hOut : ‖RC y‖ ^ 2 = ‖RR yr‖ ^ 2 + ‖RR yi‖ ^ 2 := by
        have h := periodicHypercubicEvenSpecialUnitaryComplexPhysical_norm_sq H N
          (((RC y : (complexHilbertTopEigenspace SC)ᗮ) :
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N))
        rw [hReOut, hImOut] at h
        simpa using h
      have hr := ContinuousLinearMap.le_opNorm RR yr
      have hi := ContinuousLinearMap.le_opNorm RR yi
      have hr2 : ‖RR yr‖ ^ 2 ≤ (‖RR‖ * ‖yr‖) ^ 2 := by
        nlinarith [hr, norm_nonneg (RR yr), norm_nonneg RR, norm_nonneg yr]
      have hi2 : ‖RR yi‖ ^ 2 ≤ (‖RR‖ * ‖yi‖) ^ 2 := by
        nlinarith [hi, norm_nonneg (RR yi), norm_nonneg RR, norm_nonneg yi]
      have hsq : ‖RC y‖ ^ 2 ≤ (‖RR‖ * ‖y‖) ^ 2 := by
        rw [hOut]
        nlinarith [hIn, hr2, hi2, sq_nonneg ‖RR‖]
      nlinarith [hsq, norm_nonneg (RC y), norm_nonneg RR, norm_nonneg y,
        mul_nonneg (norm_nonneg RR) (norm_nonneg y)]
    · apply ContinuousLinearMap.opNorm_le_bound RR (norm_nonneg RC)
      intro y
      let yc0 := periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
        (y : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
      have hyRealConcrete :
          (y : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) ∈
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
              H N hN beta hbeta)ᗮ := by
        simpa [S, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace] using y.property
      have hycConcrete :
          yc0 ∈ (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
            H N hN beta hbeta)ᗮ := by
        apply (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal_mem_iff_components
          H N hN beta hbeta yc0).2
        constructor
        · simpa [yc0] using hyRealConcrete
        · simp [yc0]
      have hycOrth : yc0 ∈ (complexHilbertTopEigenspace SC)ᗮ := by
        simpa [SC, periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace] using
          hycConcrete
      let yc : (complexHilbertTopEigenspace SC)ᗮ := ⟨yc0, hycOrth⟩
      have hIn : ‖yc‖ = ‖y‖ := by
        simpa [yc, yc0] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm H N
            (y : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
      have hOut : ‖RC yc‖ = ‖RR y‖ := by
        change
          ‖periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta yc0‖ =
          ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta
            (y : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖
        rw [show yc0 = periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
            (y : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) by rfl,
          periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_ofReal,
          periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm]
      have h := ContinuousLinearMap.le_opNorm RC yc
      rw [hOut, hIn] at h
      exact h
  simpa [RR, RC, hS, hSC, S, SC,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator] using hnorm

/-- The genuine complex excited sector is strictly contractive by the same real quantity `q`. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_real]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
    H N hN beta hbeta

/-- Audit-visible exact real/complex top-sector identification package. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTopSpectralProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  topMembershipComponents :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta ↔
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
              H N hN beta hbeta ∧
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
              H N hN beta hbeta
  projectionComplexification :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta)
  excitedNormExact :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ =
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  excitedNormLtOne :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1

/-- Construct the exact complex top-sector identification package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTopSpectralProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTopSpectralProjectionPackage
      H N hN beta hbeta :=
  { topMembershipComponents :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem_iff_components
        H N hN beta hbeta
    projectionComplexification :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_eq_complexification
        H N hN beta hbeta
    excitedNormExact :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_real
        H N hN beta hbeta
    excitedNormLtOne :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D