import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorPlaquetteSeparation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonPlaquetteSupport
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonLocalAction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance periodicHypercubicEvenSpatialSixColorCompactLocalitySideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- On the actual compact periodic `SU(N)` Wilson system, generic oriented
plaquette incidence is definitionally the canonical periodic physical-link
incidence. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitary_touches_iff
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (p : PeriodicHypercubicEvenPlaquette H)
    (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.PlaquetteTouchesEdge p e ↔
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H) p e := by
  rfl

/-- Distinct canonical spatial-slice links in one six-color class are absent
from each other's actual compact Wilson plaquette-neighbor support. -/
theorem periodicHypercubicEvenSpatialSliceLink_sameColor_not_mem_compactPlaquetteNeighbors
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    {e f : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenSpatialSliceLinkColor H f)
    (hne : e ≠ f) :
    periodicHypercubicEvenSpatialSliceLinkEmbedding H f ∉
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.plaquetteNeighbors
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) := by
  intro hmem
  rw [compact_oriented_mem_plaquetteNeighbors_iff] at hmem
  rcases hmem with ⟨p, hpE, hpF⟩
  apply periodicHypercubicEvenSpatialSliceLink_sameColor_no_common_plaquette
    H hColor hne
  refine ⟨p, ?_, ?_⟩
  · exact (periodicHypercubicEvenSpecialUnitary_touches_iff
      H N hN beta hbeta p
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)).mp hpE
  · exact (periodicHypercubicEvenSpecialUnitary_touches_iff
      H N hN beta hbeta p
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)).mp hpF

/-- Consequently, after replacing one target link by the same `SU(N)` value,
the target-local Wilson plaquette action is insensitive to a change confined to
a distinct link of the same six-color class. -/
theorem periodicHypercubicEvenSpatialSliceLink_sameColor_targetLocalPlaquetteAction_replaceLink_eq
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
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.AgreeOffLink
        A B (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.targetLocalPlaquetteAction
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.replaceLink
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) g)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.targetLocalPlaquetteAction
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.replaceLink
            B (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) g)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) := by
  exact compact_oriented_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base
    A B
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)
    g
    (periodicHypercubicEvenSpatialSliceLink_sameColor_not_mem_compactPlaquetteNeighbors
      H N hN beta hbeta hColor hne)
    hAgree

end

end MathlibAnalytic
end MGAP4D
