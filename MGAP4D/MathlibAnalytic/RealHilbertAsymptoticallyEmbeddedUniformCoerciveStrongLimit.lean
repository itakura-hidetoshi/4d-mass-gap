import MGAP4D.MathlibAnalytic.RealHilbertUniformCoerciveSymmetricStrongLimitSpectrum
import Mathlib.Topology.Order.OrderClosed

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology

noncomputable section

/-- A family of symmetric coercive operators on varying real Hilbert spaces,
with approximation and isometric embedding maps into one common carrier.

Unlike an exact identification by continuous linear equivalences, the embedded
approximants need only converge to each target vector, while the embedded
operator images converge strongly to one limiting bounded operator. -/
structure RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
    (ι : Type*)
    (F : ι → Type*)
    (E : Type*)
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (l : Filter ι) where
  localOperator : ∀ i, F i →L[ℝ] F i
  approximate : ∀ i, E →L[ℝ] F i
  embed : ∀ i, F i →L[ℝ] E
  embed_norm : ∀ (i) (x : F i), ‖embed i x‖ = ‖x‖
  embed_inner : ∀ (i) (x y : F i),
    inner ℝ (embed i x) (embed i y) = inner ℝ x y
  limitOperator : E →L[ℝ] E
  gap : ℝ
  gap_pos : 0 < gap
  local_gap : ∀ (i) (x : F i),
    gap * ‖x‖ ^ 2 ≤ inner ℝ (localOperator i x) x
  local_symmetric : ∀ i,
    ((localOperator i : F i →L[ℝ] F i) : F i →ₗ[ℝ] F i).IsSymmetric
  approximate_tendsto : ∀ f : E,
    Tendsto (fun i => embed i (approximate i f)) l (𝓝 f)
  evolved_tendsto : ∀ f : E,
    Tendsto
      (fun i => embed i (localOperator i (approximate i f)))
      l
      (𝓝 (limitOperator f))

/-- Norms of the varying-space approximants converge to the common-carrier
norm, because the embeddings are isometric and reconstruct the target
asymptotically. -/
theorem realHilbert_asymptoticallyEmbedded_approximate_norm_tendsto
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
      ι F E l)
    (f : E) :
    Tendsto (fun i => ‖D.approximate i f‖) l (𝓝 ‖f‖) := by
  have h := (D.approximate_tendsto f).norm
  simpa only [D.embed_norm] using h

/-- The uniform local quadratic lower bound survives asymptotic embedding and
strong convergence on the common carrier. -/
theorem realHilbert_asymptoticallyEmbedded_limit_gap
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
      ι F E l)
    (f : E) :
    D.gap * ‖f‖ ^ 2 ≤ inner ℝ (D.limitOperator f) f := by
  have hNorm :=
    realHilbert_asymptoticallyEmbedded_approximate_norm_tendsto D f
  have hLeft :
      Tendsto
        (fun i => D.gap * ‖D.approximate i f‖ ^ 2)
        l
        (𝓝 (D.gap * ‖f‖ ^ 2)) :=
    tendsto_const_nhds.mul (hNorm.pow 2)
  have hRight :
      Tendsto
        (fun i =>
          inner ℝ
            (D.embed i (D.localOperator i (D.approximate i f)))
            (D.embed i (D.approximate i f)))
        l
        (𝓝 (inner ℝ (D.limitOperator f) f)) :=
    (D.evolved_tendsto f).inner (D.approximate_tendsto f)
  have hFinite : ∀ i,
      D.gap * ‖D.approximate i f‖ ^ 2 ≤
        inner ℝ
          (D.embed i (D.localOperator i (D.approximate i f)))
          (D.embed i (D.approximate i f)) := by
    intro i
    calc
      D.gap * ‖D.approximate i f‖ ^ 2 ≤
          inner ℝ
            (D.localOperator i (D.approximate i f))
            (D.approximate i f) :=
        D.local_gap i (D.approximate i f)
      _ = inner ℝ
          (D.embed i (D.localOperator i (D.approximate i f)))
          (D.embed i (D.approximate i f)) :=
        (D.embed_inner i
          (D.localOperator i (D.approximate i f))
          (D.approximate i f)).symm
  exact le_of_tendsto_of_tendsto hLeft hRight (Eventually.of_forall hFinite)

/-- Local symmetry also survives asymptotic embedding and strong convergence. -/
theorem realHilbert_asymptoticallyEmbedded_limit_symmetric
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
      ι F E l) :
    (D.limitOperator : E →ₗ[ℝ] E).IsSymmetric := by
  intro f g
  have hLeft :
      Tendsto
        (fun i =>
          inner ℝ
            (D.embed i (D.localOperator i (D.approximate i f)))
            (D.embed i (D.approximate i g)))
        l
        (𝓝 (inner ℝ (D.limitOperator f) g)) :=
    (D.evolved_tendsto f).inner (D.approximate_tendsto g)
  have hRight :
      Tendsto
        (fun i =>
          inner ℝ
            (D.embed i (D.approximate i f))
            (D.embed i (D.localOperator i (D.approximate i g))))
        l
        (𝓝 (inner ℝ f (D.limitOperator g))) :=
    (D.approximate_tendsto f).inner (D.evolved_tendsto g)
  have hFunctions :
      (fun i =>
        inner ℝ
          (D.embed i (D.localOperator i (D.approximate i f)))
          (D.embed i (D.approximate i g))) =
      (fun i =>
        inner ℝ
          (D.embed i (D.approximate i f))
          (D.embed i (D.localOperator i (D.approximate i g)))) := by
    funext i
    calc
      inner ℝ
          (D.embed i (D.localOperator i (D.approximate i f)))
          (D.embed i (D.approximate i g)) =
        inner ℝ
          (D.localOperator i (D.approximate i f))
          (D.approximate i g) :=
        D.embed_inner i
          (D.localOperator i (D.approximate i f))
          (D.approximate i g)
      _ = inner ℝ
          (D.approximate i f)
          (D.localOperator i (D.approximate i g)) :=
        D.local_symmetric i (D.approximate i f) (D.approximate i g)
      _ = inner ℝ
          (D.embed i (D.approximate i f))
          (D.embed i (D.localOperator i (D.approximate i g))) :=
        (D.embed_inner i
          (D.approximate i f)
          (D.localOperator i (D.approximate i g))).symm
  rw [hFunctions] at hLeft
  exact tendsto_nhds_unique hLeft hRight

/-- Once the limit gap and symmetry have been proved from the asymptotic
embedding data, the limiting operator itself supplies a constant common-carrier
family accepted by the existing Lax--Milgram and spectrum layers. -/
noncomputable def
    RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData.toLimitStrongLimitData
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
      ι F E l) :
    RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l :=
  { approximant := fun _ => D.limitOperator
    limitOperator := D.limitOperator
    gap := D.gap
    gap_pos := D.gap_pos
    approximant_gap := fun _ f =>
      realHilbert_asymptoticallyEmbedded_limit_gap D f
    strong_tendsto := fun _ => tendsto_const_nhds
    approximant_symmetric := fun _ =>
      realHilbert_asymptoticallyEmbedded_limit_symmetric D }

/-- The real algebra spectrum of an asymptotically embedded strong limit is
bounded below by the common positive local gap. -/
theorem realHilbert_asymptoticallyEmbedded_limit_spectrum_subset_Ici
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
      ι F E l) :
    spectrum ℝ D.limitOperator ⊆ Set.Ici D.gap :=
  realHilbert_uniformCoerciveSymmetricStrongLimit_spectrum_subset_Ici
    D.toLimitStrongLimitData

/-- Every real parameter below the common local gap lies in the resolvent set of
the asymptotically embedded limiting operator, with the sharp inherited norm
bound. -/
theorem realHilbert_asymptoticallyEmbedded_limit_resolvent_package
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
      ι F E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    lambda ∈ resolventSet ℝ D.limitOperator ∧
      ‖D.toLimitStrongLimitData.limitResolvent hlambda‖ ≤
        (D.gap - lambda)⁻¹ := by
  constructor
  · exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_mem_resolventSet
        D.toLimitStrongLimitData hlambda
  · exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        D.toLimitStrongLimitData hlambda

end

end MathlibAnalytic
end MGAP4D
