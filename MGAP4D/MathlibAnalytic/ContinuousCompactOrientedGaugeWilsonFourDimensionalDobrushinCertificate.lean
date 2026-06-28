import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinInfluence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryIncidenceCertificate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A four-dimensional compact incidence certificate and a strict local-action
oscillation threshold generate a strict proof-relevant Dobrushin matrix. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonFourDimensionalIncidenceCertificate.dobrushinMatrixData_of_localActionOscillation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (I : ContinuousCompactOrientedGaugeWilsonFourDimensionalIncidenceCertificate C)
    (omega : ℝ)
    (hOmega : 0 ≤ omega)
    (hOsc : C.ActiveLocalActionDifferenceOscillationBound omega)
    (hThreshold :
      continuousCompactOrientedGaugeWilsonConditionalTVMajorant C omega <
        (18 : ℝ)⁻¹) :
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C := by
  let q := continuousCompactOrientedGaugeWilsonConditionalTVMajorant C omega
  refine
    { influence := continuousCompactOrientedGaugeWilsonDobrushinInfluence C omega
      influence_nonneg := ?_
      influence_diagonal_zero := ?_
      conditionalTotalVariation_le := ?_
      dobrushinCoefficient := 18 * q
      dobrushinCoefficient_nonneg := ?_
      rowSum_le_coefficient := ?_
      dobrushinCoefficient_lt_one := ?_ }
  · intro target source
    by_cases hActive : source ∈ C.base.activePlaquetteNeighbors target
    · simp [continuousCompactOrientedGaugeWilsonDobrushinInfluence,
        hActive, q,
        continuous_compact_oriented_conditionalTVMajorant_nonneg
          C omega hOmega]
    · simp [continuousCompactOrientedGaugeWilsonDobrushinInfluence, hActive]
  · intro e
    simp [continuousCompactOrientedGaugeWilsonDobrushinInfluence,
      CompactOrientedGaugeWilsonSystem.activePlaquetteNeighbors]
  · intro target source A B hAgree
    by_cases hEq : source = target
    · subst source
      have hZero :=
        continuous_compact_oriented_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
          C A B target hAgree
      rw [hZero]
      exact
        (continuous_compact_oriented_conditionalTVMajorant_nonneg
          C omega hOmega).trans
          (by
            by_cases hActive : target ∈ C.base.activePlaquetteNeighbors target
            · simp [continuousCompactOrientedGaugeWilsonDobrushinInfluence,
                hActive]
            · simp [continuousCompactOrientedGaugeWilsonDobrushinInfluence,
                hActive])
    · by_cases hActive : source ∈ C.base.activePlaquetteNeighbors target
      · simpa [continuousCompactOrientedGaugeWilsonDobrushinInfluence,
          hActive] using
          (continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_active_localActionOscillation
            C omega hOmega hOsc target source A B hAgree hActive)
      · have hZero :=
          continuous_compact_oriented_singleLinkConditionalTotalVariation_eq_zero_of_not_active
            C A B target source hAgree hEq hActive
        rw [hZero]
        simp [continuousCompactOrientedGaugeWilsonDobrushinInfluence, hActive]
  · exact mul_nonneg (by norm_num)
      (continuous_compact_oriented_conditionalTVMajorant_nonneg
        C omega hOmega)
  · intro target
    have hCardNat := I.activeNeighborCard_le_eighteen target
    have hCard :
        ((C.base.activePlaquetteNeighbors target).card : ℝ) ≤ 18 := by
      exact_mod_cast hCardNat
    calc
      (∑ source : C.base.geometry.Edge,
          continuousCompactOrientedGaugeWilsonDobrushinInfluence
            C omega target source) =
        (C.base.activePlaquetteNeighbors target).card * q := by
          simpa [q] using
            continuous_compact_oriented_dobrushinInfluence_rowSum_eq
              C omega target
      _ ≤ 18 * q :=
        mul_le_mul_of_nonneg_right hCard
          (continuous_compact_oriented_conditionalTVMajorant_nonneg
            C omega hOmega)
  · dsimp [q]
    calc
      18 * continuousCompactOrientedGaugeWilsonConditionalTVMajorant C omega <
          18 * (18 : ℝ)⁻¹ :=
        mul_lt_mul_of_pos_left hThreshold (by norm_num)
      _ = 1 := by norm_num

end
end MathlibAnalytic
end MGAP4D
