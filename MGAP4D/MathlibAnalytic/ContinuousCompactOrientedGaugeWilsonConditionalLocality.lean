import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonFiberReplacement
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalActionOscillation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Away from the active plaquette neighborhood, the difference of two
one-link conditional exponents is constant in the inserted target value. -/
theorem continuous_compact_oriented_singleLinkExponentDifferenceOscillationBound_zero_of_not_active
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B source)
    (hNe : source ≠ target)
    (hInactive : source ∉ C.base.activePlaquetteNeighbors target) :
    C.SingleLinkExponentDifferenceOscillationBound A B target 0 := by
  classical
  have hNotNeighbor : source ∉ C.base.plaquetteNeighbors target := by
    intro hNeighbor
    apply hInactive
    exact Finset.mem_erase.mpr ⟨hNe, hNeighbor⟩
  intro u v
  have hu :=
    compact_oriented_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
      C.base A B target source u hNotNeighbor hAgree
  have hv :=
    compact_oriented_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
      C.base A B target source v hNotNeighbor hAgree
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkGibbsExponent
    CompactOrientedGaugeWilsonSystem.gibbsExponent
  rw [compact_oriented_wilsonAction_replaceLink_eq_local_add_remote,
    compact_oriented_wilsonAction_replaceLink_eq_local_add_remote,
    compact_oriented_wilsonAction_replaceLink_eq_local_add_remote,
    compact_oriented_wilsonAction_replaceLink_eq_local_add_remote,
    hu, hv]
  ring_nf
  exact le_rfl

/-- Exact compact conditional total variation vanishes away from the active
plaquette neighborhood. -/
theorem continuous_compact_oriented_singleLinkConditionalTotalVariation_eq_zero_of_not_active
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B source)
    (hNe : source ≠ target)
    (hInactive : source ∉ C.base.activePlaquetteNeighbors target) :
    C.singleLinkConditionalTotalVariation A B target = 0 := by
  have hUpper :=
    continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_exponentDifferenceOscillation
      C A B target 0 (by norm_num)
      (continuous_compact_oriented_singleLinkExponentDifferenceOscillationBound_zero_of_not_active
        C A B target source hAgree hNe hInactive)
  apply le_antisymm
  · simpa using hUpper
  · exact continuous_compact_oriented_singleLinkConditionalTotalVariation_nonneg
      C A B target

/-- On an active source-target pair, a uniform local-action oscillation bound
controls every pair of configurations differing only at the source link. -/
theorem continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_active_localActionOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (omega : ℝ)
    (hOmega : 0 ≤ omega)
    (hOsc : C.ActiveLocalActionDifferenceOscillationBound omega)
    (target source : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B source)
    (hActive : source ∈ C.base.activePlaquetteNeighbors target) :
    C.singleLinkConditionalTotalVariation A B target ≤
      (Real.exp (C.base.beta * omega) - 1) /
        (Real.exp (C.base.beta * omega) + 1) := by
  have hB := compact_oriented_replaceLink_right_of_agreeOffLink
    C.base A B source hAgree
  have hBound :=
    continuous_compact_oriented_active_singleLinkConditionalTotalVariation_le_of_localActionOscillation
      C omega hOmega hOsc target source A (B source) hActive
  simpa [hB] using hBound

end
end MathlibAnalytic
end MGAP4D
