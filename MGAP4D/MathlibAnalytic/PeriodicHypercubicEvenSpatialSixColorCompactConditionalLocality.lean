import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorCompactLocality
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalLocality

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance periodicHypercubicEvenSpatialSixColorCompactConditionalLocalitySideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- On the actual compact periodic `SU(N)` Wilson system, changing a distinct
spatial-slice link in the same six-color class does not change the exact
normalized one-link conditional law at the target link. -/
theorem periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkConditionalMeasure_eq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    {e f : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenSpatialSliceLinkColor H f)
    (hne : e ≠ f)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.Configuration)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.AgreeOffLink
        A B (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
        A (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
        B (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) := by
  exact continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_not_neighbor
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
    A B
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)
    (periodicHypercubicEvenSpatialSliceLink_sameColor_not_mem_compactPlaquetteNeighbors
      H N hN beta hbeta hColor hne)
    hAgree

/-- Concrete replacement form of same-six-color conditional locality.  This is
the exact form needed to commute later single-link heat-bath updates at
distinct links in one color class. -/
theorem periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkConditionalMeasure_replaceLink_eq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    {e f : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenSpatialSliceLinkColor H f)
    (hne : e ≠ f)
    (A : (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.Configuration)
    (v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.replaceLink
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) v)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
        A (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) := by
  exact continuous_compact_oriented_singleLinkConditionalMeasure_replaceLink_eq_of_not_neighbor
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
    A
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)
    v
    (periodicHypercubicEvenSpatialSliceLink_sameColor_not_mem_compactPlaquetteNeighbors
      H N hN beta hbeta hColor hne)

end

end MathlibAnalytic
end MGAP4D
