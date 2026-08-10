import MGAP4D.MathlibAnalytic.DistinguishedVectorHilbertBasis
import Mathlib.Data.Countable.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u v w x

variable {ι : Type u} {κ : Type v}
variable {H : Type w} {K : Type x}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Restrict an arbitrary orthonormal family along an index embedding. -/
theorem orthonormal_comp_embedding
    {v : κ → K}
    (hv : Orthonormal ℝ v)
    (e : ι ↪ κ) :
    Orthonormal ℝ (fun i : ι => v (e i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have h := (orthonormal_iff_ite.mp hv) (e i) (e j)
  by_cases hij : i = j
  · subst j
    simpa using h
  · have heij : e i ≠ e j := fun hEq => hij (e.injective hEq)
    simpa [hij, heij] using h

/-- The one-dimensional orthogonal family in the target selected by an
embedding of source basis indices into an orthonormal target family. -/
noncomputable def orthonormalEmbeddingOrthogonalFamily
    {v : κ → K}
    (hv : Orthonormal ℝ v)
    (e : ι ↪ κ) :
    OrthogonalFamily ℝ (fun _ : ι => ℝ)
      (fun i =>
        LinearIsometry.toSpanSingleton ℝ K
          ((orthonormal_comp_embedding hv e).1 i)) :=
  (orthonormal_comp_embedding hv e).orthogonalFamily

/-- A Hilbert basis in the source and an embedded orthonormal family in the
target canonically generate a genuine real-linear isometry.

Unlike `hilbertBasisLinearIsometryOfEmbedding`, the target family need not be a
Hilbert basis and need not be total. -/
noncomputable def hilbertBasisToOrthonormalLinearIsometryOfEmbedding
    (bH : HilbertBasis ι ℝ H)
    (v : κ → K)
    (hv : Orthonormal ℝ v)
    (e : ι ↪ κ) :
    H →ₗᵢ[ℝ] K :=
  (orthonormalEmbeddingOrthogonalFamily hv e).linearIsometry.comp
    bH.repr.toLinearIsometry

/-- The source basis vector indexed by `i` is sent exactly to the selected
target orthonormal vector `v (e i)`. -/
@[simp] theorem hilbertBasisToOrthonormalLinearIsometryOfEmbedding_basis
    (bH : HilbertBasis ι ℝ H)
    (v : κ → K)
    (hv : Orthonormal ℝ v)
    (e : ι ↪ κ)
    (i : ι) :
    hilbertBasisToOrthonormalLinearIsometryOfEmbedding bH v hv e (bH i) =
      v (e i) := by
  classical
  change
    (orthonormalEmbeddingOrthogonalFamily hv e).linearIsometry
        (bH.repr (bH i)) = v (e i)
  rw [bH.repr_self]
  rw [(orthonormalEmbeddingOrthogonalFamily hv e).linearIsometry_apply_single]
  simp [orthonormalEmbeddingOrthogonalFamily]

/-- Every countable index type admits a canonical noncomputably selected
embedding into `ℕ`. -/
noncomputable def countableIndexEmbeddingNat
    (ι : Type u) [Countable ι] : ι ↪ ℕ :=
  Classical.choice (nonempty_embedding_nat ι)

/-- If the source distinguished-vector Hilbert basis is countably indexed and
the target carries a countable orthonormal family whose zeroth vector is the
target distinguished vector, then there is a distinguished-vector-preserving
linear isometry from source to target.

The source basis index is first embedded into `ℕ`, then retargeted so the
source distinguished index maps to `0`.  No target Hilbert basis or cardinal
comparison is needed. -/
noncomputable def distinguishedVectorLinearIsometryOfCountableOrthonormal
    (source : H) (hSource : ‖source‖ = 1)
    [Countable (distinguishedVectorHilbertBasis source hSource).Index]
    (targetFamily : ℕ → K)
    (hTargetFamily : Orthonormal ℝ targetFamily) :
    H →ₗᵢ[ℝ] K :=
  let bH := distinguishedVectorHilbertBasis source hSource
  let e := retargetEmbedding
    (countableIndexEmbeddingNat bH.Index) bH.index 0
  hilbertBasisToOrthonormalLinearIsometryOfEmbedding
    bH.basis targetFamily hTargetFamily e

/-- The countable-orthonormal construction sends the source distinguished
vector to the zeroth target orthonormal vector exactly. -/
@[simp] theorem distinguishedVectorLinearIsometryOfCountableOrthonormal_apply
    (source : H) (hSource : ‖source‖ = 1)
    [Countable (distinguishedVectorHilbertBasis source hSource).Index]
    (targetFamily : ℕ → K)
    (hTargetFamily : Orthonormal ℝ targetFamily) :
    distinguishedVectorLinearIsometryOfCountableOrthonormal
        source hSource targetFamily hTargetFamily source =
      targetFamily 0 := by
  let bH := distinguishedVectorHilbertBasis source hSource
  let e := retargetEmbedding
    (countableIndexEmbeddingNat bH.Index) bH.index 0
  rw [show source = bH.basis bH.index by exact bH.basis_index.symm]
  rw [hilbertBasisToOrthonormalLinearIsometryOfEmbedding_basis]
  change targetFamily (e bH.index) = targetFamily 0
  rw [show e bH.index = 0 by
    exact retargetEmbedding_apply_distinguished
      (countableIndexEmbeddingNat bH.Index) bH.index 0]

end

end MathlibAnalytic
end MGAP4D
