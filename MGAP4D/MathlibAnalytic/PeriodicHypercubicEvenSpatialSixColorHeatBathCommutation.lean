import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorCompactConditionalLocality
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathCommutation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Distinct spatial-slice links in one canonical six-color class have commuting
exact compact `SU(N)` Wilson heat-bath transforms.  The proof uses the actual
normalized one-link conditional laws and their same-color replacement locality;
no abstract independence hypothesis is introduced. -/
theorem periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkHeatBathTransform_commute
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (O : (PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hO : Continuous O)
    {e f : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenSpatialSliceLinkColor H f)
    (hne : e ≠ f) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    C.singleLinkHeatBathTransform
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)
        (C.singleLinkHeatBathTransform
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) O) =
      C.singleLinkHeatBathTransform
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)
        (C.singleLinkHeatBathTransform
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) O) := by
  dsimp only
  funext A
  have hNeEmbed :
      periodicHypercubicEvenSpatialSliceLinkEmbedding H f ≠
        periodicHypercubicEvenSpatialSliceLinkEmbedding H e := by
    intro h
    apply hne
    exact periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H h.symm
  apply
    continuous_compact_oriented_singleLinkHeatBathTransform_commute_at_of_measure_invariant
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      O hO A hNeEmbed
  · intro h
    exact
      periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkConditionalMeasure_replaceLink_eq
        H N hN beta hbeta hColor hne A h
  · intro g
    exact
      periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkConditionalMeasure_replaceLink_eq
        H N hN beta hbeta hColor.symm hne.symm A g

end

end MathlibAnalytic
end MGAP4D
