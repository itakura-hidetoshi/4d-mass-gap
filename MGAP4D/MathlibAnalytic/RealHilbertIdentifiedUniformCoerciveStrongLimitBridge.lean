import MGAP4D.MathlibAnalytic.RealHilbertUniformCoerciveSymmetricStrongLimitSpectrum

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology

noncomputable section

/-- A family of operators on varying real Hilbert spaces, together with
inner-product-preserving continuous linear identifications into one common
carrier and a strong limit there. -/
structure RealHilbertIdentifiedUniformCoerciveStrongLimitData
    (ι : Type*)
    (F : ι → Type*)
    (E : Type*)
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (l : Filter ι) where
  localOperator : ∀ i, F i →L[ℝ] F i
  identification : ∀ i, F i ≃L[ℝ] E
  identification_norm : ∀ (i) (x : F i),
    ‖identification i x‖ = ‖x‖
  identification_inner : ∀ (i) (x y : F i),
    inner ℝ (identification i x) (identification i y) = inner ℝ x y
  limitOperator : E →L[ℝ] E
  gap : ℝ
  gap_pos : 0 < gap
  local_gap : ∀ (i) (x : F i),
    gap * ‖x‖ ^ 2 ≤ inner ℝ (localOperator i x) x
  local_symmetric : ∀ i,
    ((localOperator i : F i →L[ℝ] F i) : F i →ₗ[ℝ] F i).IsSymmetric
  transported_strong_tendsto : ∀ f : E,
    Tendsto
      (fun i => identification i
        (localOperator i ((identification i).symm f)))
      l
      (𝓝 (limitOperator f))

/-- Conjugate every local operator to the common carrier. -/
noncomputable def
    RealHilbertIdentifiedUniformCoerciveStrongLimitData.transportedOperator
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l)
    (i : ι) :
    E →L[ℝ] E :=
  (D.identification i).toContinuousLinearMap.comp
    ((D.localOperator i).comp
      (D.identification i).symm.toContinuousLinearMap)

@[simp] theorem realHilbert_identified_transportedOperator_apply
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l)
    (i : ι)
    (f : E) :
    D.transportedOperator i f =
      D.identification i
        (D.localOperator i ((D.identification i).symm f)) := by
  rfl

/-- The inverse identification preserves norms. -/
theorem realHilbert_identified_symm_norm
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l)
    (i : ι)
    (f : E) :
    ‖(D.identification i).symm f‖ = ‖f‖ := by
  simpa using
    (D.identification_norm i ((D.identification i).symm f)).symm

/-- The inverse identification preserves real inner products. -/
theorem realHilbert_identified_symm_inner
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l)
    (i : ι)
    (f g : E) :
    inner ℝ ((D.identification i).symm f)
        ((D.identification i).symm g) =
      inner ℝ f g := by
  simpa using
    (D.identification_inner i
      ((D.identification i).symm f)
      ((D.identification i).symm g)).symm

/-- Conjugation by an inner-product-preserving identification transports the
uniform local quadratic gap to the common carrier. -/
theorem realHilbert_identified_transportedOperator_gap
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l)
    (i : ι)
    (f : E) :
    D.gap * ‖f‖ ^ 2 ≤ inner ℝ (D.transportedOperator i f) f := by
  let x : F i := (D.identification i).symm f
  have hNorm : ‖x‖ = ‖f‖ := by
    simpa [x] using realHilbert_identified_symm_norm D i f
  have hGap : D.gap * ‖x‖ ^ 2 ≤
      inner ℝ (D.localOperator i x) x :=
    D.local_gap i x
  calc
    D.gap * ‖f‖ ^ 2 = D.gap * ‖x‖ ^ 2 := by rw [hNorm]
    _ ≤ inner ℝ (D.localOperator i x) x := hGap
    _ = inner ℝ
        (D.identification i (D.localOperator i x))
        (D.identification i x) :=
      (D.identification_inner i (D.localOperator i x) x).symm
    _ = inner ℝ (D.transportedOperator i f) f := by
      simp [RealHilbertIdentifiedUniformCoerciveStrongLimitData.transportedOperator,
        x]

/-- Symmetry of every local operator is preserved under the Hilbert
identification. -/
theorem realHilbert_identified_transportedOperator_symmetric
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l)
    (i : ι) :
    ((D.transportedOperator i : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
  intro f g
  let x : F i := (D.identification i).symm f
  let y : F i := (D.identification i).symm g
  calc
    inner ℝ (D.transportedOperator i f) g =
        inner ℝ
          (D.identification i (D.localOperator i x))
          (D.identification i y) := by
      simp [RealHilbertIdentifiedUniformCoerciveStrongLimitData.transportedOperator,
        x, y]
    _ = inner ℝ (D.localOperator i x) y :=
      D.identification_inner i (D.localOperator i x) y
    _ = inner ℝ x (D.localOperator i y) :=
      D.local_symmetric i x y
    _ = inner ℝ
        (D.identification i x)
        (D.identification i (D.localOperator i y)) :=
      (D.identification_inner i x (D.localOperator i y)).symm
    _ = inner ℝ f (D.transportedOperator i g) := by
      simp [RealHilbertIdentifiedUniformCoerciveStrongLimitData.transportedOperator,
        x, y]

/-- Package the identified varying-space family as the common-carrier strong
limit datum consumed by the Lax--Milgram and spectrum layers. -/
noncomputable def
    RealHilbertIdentifiedUniformCoerciveStrongLimitData.toCommonCarrierStrongLimitData
    {ι : Type*}
    {F : ι → Type*}
    {E : Type*}
    [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l) :
    RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l :=
  { approximant := D.transportedOperator
    limitOperator := D.limitOperator
    gap := D.gap
    gap_pos := D.gap_pos
    approximant_gap := fun i f =>
      realHilbert_identified_transportedOperator_gap D i f
    strong_tendsto := fun f => by
      simpa [RealHilbertIdentifiedUniformCoerciveStrongLimitData.transportedOperator]
        using D.transported_strong_tendsto f
    approximant_symmetric := fun i =>
      realHilbert_identified_transportedOperator_symmetric D i }

/-- Every identified varying-space family with one positive local gap and a
strong common-carrier limit inherits the same lower real spectrum enclosure. -/
theorem realHilbert_identified_limit_spectrum_subset_Ici
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
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l) :
    spectrum ℝ D.limitOperator ⊆ Set.Ici D.gap :=
  realHilbert_uniformCoerciveSymmetricStrongLimit_spectrum_subset_Ici
    D.toCommonCarrierStrongLimitData

/-- The inherited gap also supplies the full real resolvent half-line and the
sharp inverse-distance operator-norm bound on the common carrier. -/
theorem realHilbert_identified_limit_resolvent_package
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
    (D : RealHilbertIdentifiedUniformCoerciveStrongLimitData ι F E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    lambda ∈ resolventSet ℝ D.limitOperator ∧
      ‖D.toCommonCarrierStrongLimitData.limitResolvent hlambda‖ ≤
        (D.gap - lambda)⁻¹ := by
  constructor
  · exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_mem_resolventSet
        D.toCommonCarrierStrongLimitData hlambda
  · exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        D.toCommonCarrierStrongLimitData hlambda

end

end MathlibAnalytic
end MGAP4D
