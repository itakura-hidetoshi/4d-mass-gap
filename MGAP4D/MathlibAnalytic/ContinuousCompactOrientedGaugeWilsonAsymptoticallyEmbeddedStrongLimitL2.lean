import MGAP4D.MathlibAnalytic.RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimit
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitL2

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology

noncomputable section

/-- A uniform compact Wilson Dobrushin family approximated in one common real
Hilbert carrier by continuous linear approximation maps and isometric
embeddings.  No surjectivity or exact inverse relation is required. -/
structure ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (l : Filter ι) where
  approximate : ∀ i, E →L[ℝ] (U.system i).VacuumOrthogonalL2
  embed : ∀ i, (U.system i).VacuumOrthogonalL2 →L[ℝ] E
  embed_norm : ∀ (i) (f : (U.system i).VacuumOrthogonalL2),
    ‖embed i f‖ = ‖f‖
  embed_inner : ∀ (i)
      (f g : (U.system i).VacuumOrthogonalL2),
    inner ℝ (embed i f) (embed i g) = inner ℝ f g
  limitOperator : E →L[ℝ] E
  approximate_tendsto : ∀ f : E,
    Tendsto (fun i => embed i (approximate i f)) l (𝓝 f)
  hamiltonian_tendsto : ∀ f : E,
    Tendsto
      (fun i => embed i
        ((U.system i).heatBathHamiltonianVacuumOrthogonalL2
          (approximate i f)))
      l
      (𝓝 (limitOperator f))

/-- The compact Wilson asymptotic carrier data instantiate the generic
varying-Hilbert-space coercive strong-limit theorem. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData.toAsymptoticallyEmbeddedStrongLimitData
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData
      U E l) :
    RealHilbertAsymptoticallyEmbeddedUniformCoerciveStrongLimitData
      ι
      (fun i => (U.system i).VacuumOrthogonalL2)
      E
      l :=
  { localOperator := fun i =>
      (U.system i).heatBathHamiltonianVacuumOrthogonalL2
    approximate := D.approximate
    embed := D.embed
    embed_norm := D.embed_norm
    embed_inner := D.embed_inner
    limitOperator := D.limitOperator
    gap := continuousCompactOrientedUniformDobrushinGap U
    gap_pos := continuous_compact_oriented_uniformDobrushinGap_pos U
    local_gap := fun i f =>
      continuous_compact_oriented_uniformDobrushin_restrictedEnergy_gap U i f
    local_symmetric := fun i f g =>
      continuous_compact_oriented_restrictedEnergy_inner_symm
        (U.system i) f g
    approximate_tendsto := D.approximate_tendsto
    evolved_tendsto := D.hamiltonian_tendsto }

/-- The exact identified strong-limit package from the previous layer is a
special case of asymptotic approximation and isometric embedding. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData.toAsymptoticallyEmbeddedStrongLimitData
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l) :
    ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData
      U E l :=
  { approximate := fun i =>
      (D.identification i).symm.toContinuousLinearMap
    embed := fun i =>
      (D.identification i).toContinuousLinearMap
    embed_norm := D.identification_norm
    embed_inner := D.identification_inner
    limitOperator := D.limitOperator
    approximate_tendsto := fun f => by
      simpa using
        (tendsto_const_nhds :
          Tendsto (fun _ : ι => f) l (𝓝 f))
    hamiltonian_tendsto := D.transported_strong_tendsto }

/-- The uniform compact Wilson Dobrushin lower bound survives the asymptotically
embedded Hamiltonian limit. -/
theorem continuous_compact_oriented_asymptoticallyEmbedded_limit_gap
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData
      U E l)
    (f : E) :
    continuousCompactOrientedUniformDobrushinGap U * ‖f‖ ^ 2 ≤
      inner ℝ (D.limitOperator f) f :=
  realHilbert_asymptoticallyEmbedded_limit_gap
    D.toAsymptoticallyEmbeddedStrongLimitData f

/-- The asymptotically embedded limiting compact Wilson Hamiltonian is
symmetric. -/
theorem continuous_compact_oriented_asymptoticallyEmbedded_limit_symmetric
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData
      U E l) :
    (D.limitOperator : E →ₗ[ℝ] E).IsSymmetric :=
  realHilbert_asymptoticallyEmbedded_limit_symmetric
    D.toAsymptoticallyEmbeddedStrongLimitData

/-- The common positive compact Wilson gap gives a lower real spectrum enclosure
for every asymptotically embedded bounded Hamiltonian limit. -/
theorem continuous_compact_oriented_asymptoticallyEmbedded_limit_spectrum_subset_Ici
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData
      U E l) :
    spectrum ℝ D.limitOperator ⊆
      Set.Ici (continuousCompactOrientedUniformDobrushinGap U) :=
  realHilbert_asymptoticallyEmbedded_limit_spectrum_subset_Ici
    D.toAsymptoticallyEmbeddedStrongLimitData

/-- The entire real half-line below the uniform compact Wilson gap lies in the
resolvent set of the asymptotically embedded limit. -/
theorem continuous_compact_oriented_asymptoticallyEmbedded_limit_mem_resolventSet
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData
      U E l)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    lambda ∈ resolventSet ℝ D.limitOperator :=
  (realHilbert_asymptoticallyEmbedded_limit_resolvent_package
    D.toAsymptoticallyEmbeddedStrongLimitData hlambda).1

/-- The limiting resolvent has the inherited inverse-distance operator norm
bound. -/
theorem continuous_compact_oriented_asymptoticallyEmbedded_limitResolvent_norm_le
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : ContinuousCompactOrientedGaugeWilsonAsymptoticallyEmbeddedStrongLimitData
      U E l)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    ‖D.toAsymptoticallyEmbeddedStrongLimitData.toLimitStrongLimitData.limitResolvent
        hlambda‖ ≤
      (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ :=
  (realHilbert_asymptoticallyEmbedded_limit_resolvent_package
    D.toAsymptoticallyEmbeddedStrongLimitData hlambda).2

end

end MathlibAnalytic
end MGAP4D
