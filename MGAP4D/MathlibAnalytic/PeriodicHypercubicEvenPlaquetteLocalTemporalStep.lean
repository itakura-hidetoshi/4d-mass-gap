import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarMidpointPrimaryBoundaryTemporalSeparation
import Mathlib.Tactic

/-!
# Plaquette-local temporal steps for physical links

The midpoint support geometry now carries an exact Euclidean temporal
separation through the primary reflection slice.  This file introduces the
local relation that is native to the actual periodic Wilson action: two
physical positive links are local when they occur in the boundary of one
actual coordinate plaquette.

Every boundary link of one plaquette starts either at the plaquette base time
or one positive time step from that base.  Consequently two plaquette-local
physical links have source-time residues that are equal or differ by one
periodic lattice unit.

This is only the one-step local geometry needed before defining a path-length
or support-distance carrier.  It asserts no covariance decay, no Dobrushin
small-coupling condition along the factorial sequence, no positive mass, and
no Hamiltonian gap.  Markov update time is not identified with Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The four actual physical positive links occurring in the signed boundary
of one even periodic plaquette. -/
def periodicHypercubicEvenPlaquetteEdgeSupport
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H) :
    Finset (PeriodicHypercubicEvenEdge H) :=
  Finset.univ.image
    (fun k : Fin 4 =>
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).edge)

/-- Two physical positive links are Wilson-plaquette-local when they both
occur in the signed boundary of one actual periodic coordinate plaquette. -/
def periodicHypercubicEvenPlaquetteLocal
    (H : ℕ)
    (e f : PeriodicHypercubicEvenEdge H) : Prop :=
  ∃ p : PeriodicHypercubicEvenPlaquette H,
    e ∈ periodicHypercubicEvenPlaquetteEdgeSupport H p ∧
      f ∈ periodicHypercubicEvenPlaquetteEdgeSupport H p

/-- Plaquette locality is symmetric. -/
theorem periodicHypercubicEvenPlaquetteLocal_symm
    (H : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (hlocal : periodicHypercubicEvenPlaquetteLocal H e f) :
    periodicHypercubicEvenPlaquetteLocal H f e := by
  rcases hlocal with ⟨p, he, hf⟩
  exact ⟨p, hf, he⟩

/-- The source-time residue of every physical boundary link of one plaquette
is either the base residue or one positive periodic time step from it. -/
theorem periodicHypercubicEvenBoundaryStep_edge_sourceTime_eq_base_or_add_one
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (k : Fin 4) :
    (((periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p k).edge).1 0 = p.1 0) ∨
      (((periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p k).edge).1 0 = p.1 0 + 1) := by
  fin_cases k
  · exact Or.inl rfl
  · by_cases htime :
        (0 : PeriodicHypercubicAxis) = periodicHypercubicPlaquetteFirstAxis p
    · right
      simp [periodicHypercubicShift_apply, htime]
    · left
      simp [periodicHypercubicShift_apply, htime]
  · by_cases htime :
        (0 : PeriodicHypercubicAxis) = periodicHypercubicPlaquetteSecondAxis p
    · right
      simp [periodicHypercubicShift_apply, htime]
    · left
      simp [periodicHypercubicShift_apply, htime]
  · exact Or.inl rfl

/-- Source-time relation for one local Wilson plaquette step: the two residues
are equal, or one is the positive unit successor of the other. -/
def periodicHypercubicEvenTemporalUnitRelated
    (H : ℕ)
    (e f : PeriodicHypercubicEvenEdge H) : Prop :=
  e.1 0 = f.1 0 ∨
    f.1 0 = e.1 0 + 1 ∨
      e.1 0 = f.1 0 + 1

/-- The temporal unit relation is symmetric. -/
theorem periodicHypercubicEvenTemporalUnitRelated_symm
    (H : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (h : periodicHypercubicEvenTemporalUnitRelated H e f) :
    periodicHypercubicEvenTemporalUnitRelated H f e := by
  rcases h with hEq | hSucc | hPred
  · exact Or.inl hEq.symm
  · exact Or.inr (Or.inr hSucc)
  · exact Or.inr (Or.inl hPred)

/-- Actual Wilson-plaquette locality permits at most one periodic lattice-time
step between the source residues of the two physical links. -/
theorem periodicHypercubicEvenPlaquetteLocal_temporalUnitRelated
    (H : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (hlocal : periodicHypercubicEvenPlaquetteLocal H e f) :
    periodicHypercubicEvenTemporalUnitRelated H e f := by
  classical
  rcases hlocal with ⟨p, he, hf⟩
  simp only [periodicHypercubicEvenPlaquetteEdgeSupport,
    Finset.mem_image, Finset.mem_univ, true_and] at he hf
  rcases he with ⟨k, rfl⟩
  rcases hf with ⟨l, rfl⟩
  have hk :=
    periodicHypercubicEvenBoundaryStep_edge_sourceTime_eq_base_or_add_one H p k
  have hl :=
    periodicHypercubicEvenBoundaryStep_edge_sourceTime_eq_base_or_add_one H p l
  rcases hk with hk | hk <;> rcases hl with hl | hl
  · exact Or.inl (hk.trans hl.symm)
  · exact Or.inr (Or.inl (hl.trans (congrArg (fun t => t + 1) hk.symm)))
  · exact Or.inr (Or.inr (hk.trans (congrArg (fun t => t + 1) hl.symm)))
  · exact Or.inl (hk.trans hl.symm)

end

end MathlibAnalytic
end MGAP4D
