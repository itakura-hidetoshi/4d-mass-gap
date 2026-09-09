import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorEdgeMatching
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two physical links of the same canonical eight-color that both occur on one
coordinate plaquette are the same link.  This is the incidence-level form of
the fixed-color conflict-freeness needed for same-color Wilson heat-bath
factorization. -/
theorem periodicHypercubicEvenPlaquette_sameColor_touches_eq
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    {e f : PeriodicHypercubicEvenEdge H}
    (he : periodicHypercubicPlaquetteTouchesEdge
      (PeriodicHypercubicEvenSideLength H) p e)
    (hf : periodicHypercubicPlaquetteTouchesEdge
      (PeriodicHypercubicEvenSideLength H) p f)
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f) :
    e = f := by
  rcases he with ⟨i, hi⟩
  rcases hf with ⟨j, hj⟩
  have hi' :
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p i).edge = e := by
    simpa [periodicHypercubicPhysicalBoundaryEdge] using hi
  have hj' :
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p j).edge = f := by
    simpa [periodicHypercubicPhysicalBoundaryEdge] using hj
  have hBoundaryColor :
      periodicHypercubicEvenEdgeColor H
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p i).edge =
        periodicHypercubicEvenEdgeColor H
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p j).edge := by
    rw [hi', hj']
    exact hColor
  have hij : i = j :=
    periodicHypercubicEvenPlaquette_boundaryEdgeColor_injective H p hBoundaryColor
  subst j
  exact hi'.symm.trans hj'

/-- Distinct same-colored physical links never share a Wilson plaquette.  The
statement is independent of the finite side length and contains no analytic or
probabilistic hypothesis. -/
theorem periodicHypercubicEvenEdge_sameColor_no_common_plaquette
    (H : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f)
    (hne : e ≠ f) :
    ¬ ∃ p : PeriodicHypercubicEvenPlaquette H,
      periodicHypercubicPlaquetteTouchesEdge
          (PeriodicHypercubicEvenSideLength H) p e ∧
        periodicHypercubicPlaquetteTouchesEdge
          (PeriodicHypercubicEvenSideLength H) p f := by
  rintro ⟨p, he, hf⟩
  exact hne
    (periodicHypercubicEvenPlaquette_sameColor_touches_eq
      H p he hf hColor)

end

end MathlibAnalytic
end MGAP4D
