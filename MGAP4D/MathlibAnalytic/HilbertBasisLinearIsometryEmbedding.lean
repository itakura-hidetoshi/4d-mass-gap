import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped lp

noncomputable section

universe u v w x

variable {ι : Type u} {κ : Type v}
variable {H : Type w} {K : Type x}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Restricting a Hilbert basis along an embedding of its index set remains
orthonormal.

This is the purely Hilbert-geometric ingredient needed to turn an injection of
Hilbert-basis indices into a genuine linear isometric embedding of Hilbert
spaces. -/
theorem hilbertBasis_comp_embedding_orthonormal
    (bK : HilbertBasis κ ℝ K)
    (e : ι ↪ κ) :
    Orthonormal ℝ (fun i : ι => bK (e i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have h :=
    (orthonormal_iff_ite.mp bK.orthonormal) (e i) (e j)
  by_cases hij : i = j
  · subst j
    simpa using h
  · have heij : e i ≠ e j := fun hEq => hij (e.injective hEq)
    simpa [hij, heij] using h

/-- The orthogonal one-dimensional family in the target Hilbert space selected
by an embedding of Hilbert-basis indices. -/
noncomputable def hilbertBasisEmbeddingOrthogonalFamily
    (bK : HilbertBasis κ ℝ K)
    (e : ι ↪ κ) :
    OrthogonalFamily ℝ (fun _ : ι => ℝ)
      (fun i =>
        LinearIsometry.toSpanSingleton ℝ K
          ((hilbertBasis_comp_embedding_orthonormal bK e).1 i)) :=
  (hilbertBasis_comp_embedding_orthonormal bK e).orthogonalFamily

/-- An embedding of Hilbert-basis index sets canonically induces a genuine
real-linear isometric embedding of the corresponding Hilbert spaces.

The construction is entirely Mathlib-native:

`H ≃ₗᵢ ℓ²(ι,ℝ) →ₗᵢ K`,

where the second arrow is `OrthogonalFamily.linearIsometry` for the target
basis vectors selected by the index embedding. -/
noncomputable def hilbertBasisLinearIsometryOfEmbedding
    (bH : HilbertBasis ι ℝ H)
    (bK : HilbertBasis κ ℝ K)
    (e : ι ↪ κ) :
    H →ₗᵢ[ℝ] K :=
  (hilbertBasisEmbeddingOrthogonalFamily bK e).linearIsometry.comp
    bH.repr.toLinearIsometry

/-- The Hilbert-basis embedding sends every source basis vector to the target
basis vector selected by the index embedding. -/
@[simp] theorem hilbertBasisLinearIsometryOfEmbedding_basis
    (bH : HilbertBasis ι ℝ H)
    (bK : HilbertBasis κ ℝ K)
    (e : ι ↪ κ)
    (i : ι) :
    hilbertBasisLinearIsometryOfEmbedding bH bK e (bH i) =
      bK (e i) := by
  classical
  change
    (hilbertBasisEmbeddingOrthogonalFamily bK e).linearIsometry
        (bH.repr (bH i)) =
      bK (e i)
  rw [bH.repr_self]
  rw [(hilbertBasisEmbeddingOrthogonalFamily bK e).linearIsometry_apply_single]
  simp [hilbertBasisEmbeddingOrthogonalFamily]

/-- Distinguished-vector version: if the source and target distinguished
vectors are basis vectors and the basis-index embedding sends the distinguished
source index to the distinguished target index, the induced Hilbert isometry
preserves the distinguished vector exactly. -/
theorem hilbertBasisLinearIsometryOfEmbedding_distinguished
    (bH : HilbertBasis ι ℝ H)
    (bK : HilbertBasis κ ℝ K)
    (e : ι ↪ κ)
    (i₀ : ι) (k₀ : κ)
    (sourceDistinguished : H)
    (targetDistinguished : K)
    (hSource : bH i₀ = sourceDistinguished)
    (hTarget : bK k₀ = targetDistinguished)
    (he : e i₀ = k₀) :
    hilbertBasisLinearIsometryOfEmbedding bH bK e sourceDistinguished =
      targetDistinguished := by
  rw [← hSource, hilbertBasisLinearIsometryOfEmbedding_basis, he, hTarget]

end

end MathlibAnalytic
end MGAP4D
