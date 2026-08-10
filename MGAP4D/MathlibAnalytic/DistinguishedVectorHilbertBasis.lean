import MGAP4D.MathlibAnalytic.HilbertBasisLinearIsometryEmbedding
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A Hilbert basis together with one distinguished basis index representing a
specified vector. -/
structure DistinguishedVectorHilbertBasis (v : H) where
  Index : Type u
  basis : HilbertBasis Index ℝ H
  index : Index
  basis_index : basis index = v

/-- Every unit vector in a real Hilbert space extends to a Hilbert basis which
contains that vector exactly.

This is a direct use of Mathlib's `Orthonormal.exists_hilbertBasis_extension`
applied to the singleton orthonormal subset `{v}`. -/
theorem distinguishedVectorHilbertBasis_nonempty
    (v : H) (hv : ‖v‖ = 1) :
    Nonempty (DistinguishedVectorHilbertBasis v) := by
  classical
  have hs : Orthonormal ℝ ((↑) : ({v} : Set H) → H) := by
    rw [orthonormal_subtype_iff_ite]
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    simp [hv]
  obtain ⟨w, b, hsub, hb⟩ := hs.exists_hilbertBasis_extension
  let i₀ : w := ⟨v, hsub (by simp)⟩
  refine ⟨{
    Index := w
    basis := b
    index := i₀
    basis_index := ?_ }⟩
  have h := congr_fun hb i₀
  exact h

/-- A noncomputably selected Hilbert basis containing a specified unit vector.
Only existence from Mathlib is used; no model-facing basis is assumed. -/
noncomputable def distinguishedVectorHilbertBasis
    (v : H) (hv : ‖v‖ = 1) :
    DistinguishedVectorHilbertBasis v :=
  Classical.choice (distinguishedVectorHilbertBasis_nonempty v hv)

/-- Retarget an arbitrary embedding at one distinguished source point by
postcomposing with the target transposition which swaps its old image with the
required target point. -/
noncomputable def retargetEmbedding
    {ι : Type u} {κ : Type v}
    (e : ι ↪ κ) (i₀ : ι) (k₀ : κ) : ι ↪ κ := by
  letI := Classical.decEq κ
  exact (Equiv.swap (e i₀) k₀).toEmbedding.comp e

/-- The retargeted embedding sends the distinguished source index to the
prescribed distinguished target index exactly. -/
@[simp] theorem retargetEmbedding_apply_distinguished
    {ι : Type u} {κ : Type v}
    (e : ι ↪ κ) (i₀ : ι) (k₀ : κ) :
    retargetEmbedding e i₀ k₀ i₀ = k₀ := by
  classical
  simp [retargetEmbedding]

/-- Consequently, for two unit distinguished vectors, **any** embedding of the
noncomputably selected Hilbert-basis index sets theorem-generates a linear
isometry which preserves the distinguished vectors.  No separate
vacuum-index-preservation condition is needed. -/
noncomputable def distinguishedVectorLinearIsometryOfIndexEmbedding
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (v : H) (hv : ‖v‖ = 1)
    (w : K) (hw : ‖w‖ = 1)
    (e : (distinguishedVectorHilbertBasis v hv).Index ↪
      (distinguishedVectorHilbertBasis w hw).Index) :
    H →ₗᵢ[ℝ] K :=
  hilbertBasisLinearIsometryOfEmbedding
    (distinguishedVectorHilbertBasis v hv).basis
    (distinguishedVectorHilbertBasis w hw).basis
    (retargetEmbedding e
      (distinguishedVectorHilbertBasis v hv).index
      (distinguishedVectorHilbertBasis w hw).index)

/-- The distinguished-vector isometry generated from an arbitrary basis-index
embedding maps the source distinguished unit vector exactly to the target one. -/
@[simp] theorem distinguishedVectorLinearIsometryOfIndexEmbedding_apply
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (v : H) (hv : ‖v‖ = 1)
    (w : K) (hw : ‖w‖ = 1)
    (e : (distinguishedVectorHilbertBasis v hv).Index ↪
      (distinguishedVectorHilbertBasis w hw).Index) :
    distinguishedVectorLinearIsometryOfIndexEmbedding v hv w hw e v = w := by
  let bH := distinguishedVectorHilbertBasis v hv
  let bK := distinguishedVectorHilbertBasis w hw
  exact
    hilbertBasisLinearIsometryOfEmbedding_distinguished
      bH.basis bK.basis
      (retargetEmbedding e bH.index bK.index)
      bH.index bK.index v w
      bH.basis_index bK.basis_index
      (retargetEmbedding_apply_distinguished e bH.index bK.index)

end

end MathlibAnalytic
end MGAP4D
