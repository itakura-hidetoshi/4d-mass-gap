import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathFellerCarrier
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Physical positive links belonging to one fixed member of the canonical
eight-color decomposition. -/
abbrev PeriodicHypercubicEvenFixedColorEdge
    (H : ℕ) (color : PeriodicHypercubicEvenEdgeColor) : Type :=
  {e : PeriodicHypercubicEvenEdge H //
    periodicHypercubicEvenEdgeColor H e = color}

/-- One exact heat-bath update, restricted to a link in one fixed color class,
on the canonical bounded-continuous Feller carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenEdgeColor)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (e : PeriodicHypercubicEvenFixedColorEdge H color) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
  C.singleLinkConditionalExpectationContinuousBCF e.1 O

/-- On one fixed color class, the one-link Feller updates are right-commutative.
The equal-link case is tautological; the distinct-link case is exactly the
same-color commutation theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep_rightCommutative
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenEdgeColor) :
    RightCommutative
      (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep
        H N hN beta hBeta color) := by
  constructor
  intro O e f
  by_cases hEq : f.1 = e.1
  · have hef : f = e := Subtype.ext hEq
    subst f
    rfl
  · have hColor :
      periodicHypercubicEvenEdgeColor H e.1 =
        periodicHypercubicEvenEdgeColor H f.1 :=
      e.property.trans f.property.symm
    simpa [periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep] using
      (periodicHypercubicEvenSpecialUnitary_singleLinkConditionalExpectationContinuousBCF_commute_of_sameColor
        H N hN beta hBeta O hEq hColor)

/-- Folding the fixed-color one-link updates depends only on the edge-list
order class.  In particular, any permutation gives the same bounded-continuous
observable. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathFold_eq_of_perm
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenEdgeColor)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    {l₁ l₂ : List (PeriodicHypercubicEvenFixedColorEdge H color)}
    (hPerm : List.Perm l₁ l₂) :
    l₁.foldl
        (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep
          H N hN beta hBeta color) O =
      l₂.foldl
        (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep
          H N hN beta hBeta color) O := by
  letI : RightCommutative
      (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep
        H N hN beta hBeta color) :=
    periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep_rightCommutative
      H N hN beta hBeta color
  exact hPerm.foldl_eq O

/-- Canonical fixed-color heat-bath block.  It applies every physical link in
one color class exactly once.  Since all those one-link updates commute, the
particular `Finset.univ.toList` presentation is only a representative of an
order-independent parallel block. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlock
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenEdgeColor)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
  ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedColorEdge H color)).toList).foldl
    (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep
      H N hN beta hBeta color) O

/-- Any list that enumerates the fixed color class in a permuted order computes
exactly the canonical parallel color block. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlock_eq_fold_of_perm
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenEdgeColor)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (l : List (PeriodicHypercubicEvenFixedColorEdge H color))
    (hPerm :
      List.Perm l
        (Finset.univ :
          Finset (PeriodicHypercubicEvenFixedColorEdge H color)).toList) :
    l.foldl
        (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathStep
          H N hN beta hBeta color) O =
      periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlock
        H N hN beta hBeta color O := by
  unfold periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlock
  exact
    periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathFold_eq_of_perm
      H N hN beta hBeta color O hPerm

end

end MathlibAnalytic
end MGAP4D
