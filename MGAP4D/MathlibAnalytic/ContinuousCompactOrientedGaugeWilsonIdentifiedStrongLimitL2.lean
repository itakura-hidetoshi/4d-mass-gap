import MGAP4D.MathlibAnalytic.RealHilbertIdentifiedUniformCoerciveStrongLimitBridge
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyL2

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology

noncomputable section

/-- A uniform compact Wilson Dobrushin family whose vacuum-orthogonal Hilbert
spaces are identified with one common real Hilbert carrier, and whose conjugated
Hamiltonians converge strongly there. -/
structure ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (l : Filter ι) where
  identification : ∀ i,
    (U.system i).VacuumOrthogonalL2 ≃L[ℝ] E
  identification_norm : ∀ (i) (f : (U.system i).VacuumOrthogonalL2),
    ‖identification i f‖ = ‖f‖
  identification_inner : ∀ (i)
      (f g : (U.system i).VacuumOrthogonalL2),
    inner ℝ (identification i f) (identification i g) = inner ℝ f g
  limitOperator : E →L[ℝ] E
  transported_strong_tendsto : ∀ f : E,
    Tendsto
      (fun i => identification i
        ((U.system i).heatBathHamiltonianVacuumOrthogonalL2
          ((identification i).symm f)))
      l
      (𝓝 (limitOperator f))

/-- The compact Wilson identified family instantiates the generic varying-space
strong-limit bridge with the canonical uniform Dobrushin gap. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData.toIdentifiedStrongLimitData
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l) :
    RealHilbertIdentifiedUniformCoerciveStrongLimitData
      ι
      (fun i => (U.system i).VacuumOrthogonalL2)
      E
      l :=
  { localOperator := fun i =>
      (U.system i).heatBathHamiltonianVacuumOrthogonalL2
    identification := D.identification
    identification_norm := D.identification_norm
    identification_inner := D.identification_inner
    limitOperator := D.limitOperator
    gap := continuousCompactOrientedUniformDobrushinGap U
    gap_pos := continuous_compact_oriented_uniformDobrushinGap_pos U
    local_gap := fun i f =>
      continuous_compact_oriented_uniformDobrushin_restrictedEnergy_gap U i f
    local_symmetric := fun i f g =>
      continuous_compact_oriented_restrictedEnergy_inner_symm
        (U.system i) f g
    transported_strong_tendsto := D.transported_strong_tendsto }

/-- The common-carrier transported Hamiltonian associated with a compact Wilson
scale. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData.transportedHamiltonian
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l)
    (i : ι) :
    E →L[ℝ] E :=
  D.toIdentifiedStrongLimitData.transportedOperator i

@[simp] theorem continuous_compact_oriented_identified_transportedHamiltonian_apply
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l)
    (i : ι)
    (f : E) :
    D.transportedHamiltonian i f =
      D.identification i
        ((U.system i).heatBathHamiltonianVacuumOrthogonalL2
          ((D.identification i).symm f)) := by
  rfl

/-- Every transported finite-volume compact Wilson Hamiltonian has the same
common-carrier quadratic lower bound. -/
theorem continuous_compact_oriented_identified_transportedHamiltonian_gap
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l)
    (i : ι)
    (f : E) :
    continuousCompactOrientedUniformDobrushinGap U * ‖f‖ ^ 2 ≤
      inner ℝ (D.transportedHamiltonian i f) f :=
  realHilbert_identified_transportedOperator_gap
    D.toIdentifiedStrongLimitData i f

/-- The identified compact Wilson package produces the symmetric coercive
strong-limit datum on the selected common carrier. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData.toCommonCarrierStrongLimitData
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l) :
    RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l :=
  D.toIdentifiedStrongLimitData.toCommonCarrierStrongLimitData

/-- A uniform compact Wilson Dobrushin gap survives the identified strong limit
as a lower real algebra-spectrum enclosure. -/
theorem continuous_compact_oriented_identified_limit_spectrum_subset_Ici
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l) :
    spectrum ℝ D.limitOperator ⊆
      Set.Ici (continuousCompactOrientedUniformDobrushinGap U) :=
  realHilbert_identified_limit_spectrum_subset_Ici
    D.toIdentifiedStrongLimitData

/-- Every real parameter below the uniform compact Wilson gap belongs to the
resolvent set of the identified strong-limit Hamiltonian. -/
theorem continuous_compact_oriented_identified_limit_mem_resolventSet
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    lambda ∈ resolventSet ℝ D.limitOperator :=
  realHilbert_uniformCoerciveSymmetricStrongLimit_mem_resolventSet
    D.toCommonCarrierStrongLimitData hlambda

/-- The identified limiting resolvent satisfies the inherited sharp
inverse-distance norm bound. -/
theorem continuous_compact_oriented_identified_limitResolvent_norm_le
    {ι : Type*}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : ContinuousCompactOrientedGaugeWilsonIdentifiedStrongLimitData U E l)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    ‖D.toCommonCarrierStrongLimitData.limitResolvent hlambda‖ ≤
      (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ :=
  realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
    D.toCommonCarrierStrongLimitData hlambda

end

end MathlibAnalytic
end MGAP4D
