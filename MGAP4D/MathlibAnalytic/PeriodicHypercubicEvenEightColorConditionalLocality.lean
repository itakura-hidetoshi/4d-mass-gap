import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorEdgeMatching
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonPlaquetteSupport
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalLocality

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two distinct positive links of the same canonical eight-color class cannot
occur in the boundary of one even-periodic coordinate plaquette. -/
theorem periodicHypercubicEven_sameColor_distinct_not_share_plaquette
    (H : ℕ)
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source) :
    ¬ ∃ p : PeriodicHypercubicEvenPlaquette H,
      periodicHypercubicPlaquetteTouchesEdge
          (PeriodicHypercubicEvenSideLength H) p target ∧
        periodicHypercubicPlaquetteTouchesEdge
          (PeriodicHypercubicEvenSideLength H) p source := by
  rintro ⟨p, ⟨k, hk⟩, ⟨l, hl⟩⟩
  have hColorBoundary :
      periodicHypercubicEvenEdgeColor H
          (periodicHypercubicPhysicalBoundaryEdge
            (PeriodicHypercubicEvenSideLength H) p k) =
        periodicHypercubicEvenEdgeColor H
          (periodicHypercubicPhysicalBoundaryEdge
            (PeriodicHypercubicEvenSideLength H) p l) := by
    rw [hk, hl]
    exact hColor
  have hkl : k = l := by
    apply periodicHypercubicEvenPlaquette_boundaryEdgeColor_injective H p
    simpa [periodicHypercubicPhysicalBoundaryEdge] using hColorBoundary
  apply hNe
  calc
    source = periodicHypercubicPhysicalBoundaryEdge
        (PeriodicHypercubicEvenSideLength H) p l := hl.symm
    _ = periodicHypercubicPhysicalBoundaryEdge
        (PeriodicHypercubicEvenSideLength H) p k := by rw [hkl]
    _ = target := hk

/-- For the actual periodic compact `SU(N)` Wilson system, generic signed
plaquette touching is exactly the concrete periodic physical-link incidence. -/
@[simp] theorem periodicHypercubicSpecialUnitaryWilsonSystem_touches_iff
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicEvenPlaquette H)
    (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).base.PlaquetteTouchesEdge
        p e ↔
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H) p e := by
  rfl

/-- Distinct same-colored links are outside each other's plaquette-neighbor
support in the actual even-periodic compact `SU(N)` Wilson model. -/
theorem periodicHypercubicEvenSpecialUnitary_not_mem_plaquetteNeighbors_of_sameColor
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source) :
    source ∉
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).base.plaquetteNeighbors
          target := by
  intro hNeighbor
  have hShared :=
    (compact_oriented_mem_plaquetteNeighbors_iff
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).base
      target source).1 hNeighbor
  rcases hShared with ⟨p, hpTarget, hpSource⟩
  exact periodicHypercubicEven_sameColor_distinct_not_share_plaquette
    H hNe hColor
    ⟨p,
      (periodicHypercubicSpecialUnitaryWilsonSystem_touches_iff
        H N hN beta hBeta p target).1 hpTarget,
      (periodicHypercubicSpecialUnitaryWilsonSystem_touches_iff
        H N hN beta hBeta p source).1 hpSource⟩

/-- The normalized target one-link conditional law is unchanged when the
background changes only at a distinct link of the same fixed eight-color
class.  This is the exact same-color conditional-independence statement needed
before commuting heat-bath updates inside a color block. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkConditionalMeasure_eq_of_sameColor
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source)
    (hAgree :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).base.AgreeOffLink
          A B source) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkConditionalMeasure
        A target =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkConditionalMeasure
          B target := by
  apply continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_not_neighbor
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
    A B target source
  · exact periodicHypercubicEvenSpecialUnitary_not_mem_plaquetteNeighbors_of_sameColor
      H N hN beta hBeta hNe hColor
  · exact hAgree

/-- Concrete replacement form: resampling one distinct same-colored source
link leaves the target one-link conditional law unchanged. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkConditionalMeasure_replaceLink_eq_of_sameColor
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    {target source : PeriodicHypercubicEvenEdge H}
    (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkConditionalMeasure
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).base.replaceLink
            A source v) target =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkConditionalMeasure
          A target := by
  apply continuous_compact_oriented_singleLinkConditionalMeasure_replaceLink_eq_of_not_neighbor
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
    A target source v
  exact periodicHypercubicEvenSpecialUnitary_not_mem_plaquetteNeighbors_of_sameColor
    H N hN beta hBeta hNe hColor

end
end MathlibAnalytic
end MGAP4D
