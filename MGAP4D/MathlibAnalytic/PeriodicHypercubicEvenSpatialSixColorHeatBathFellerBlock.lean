import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorHeatBathCommutation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathFellerCarrier
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance periodicHypercubicEvenSpatialSixColorHeatBathFellerBlockFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Spatial-slice links belonging to one fixed member of the canonical
six-color decomposition. -/
abbrev PeriodicHypercubicEvenFixedSpatialColorLink
    (H : ℕ) (color : PeriodicHypercubicEvenSpatialBoundaryColor) : Type :=
  {e : PeriodicHypercubicEvenSpatialSliceLink H //
    periodicHypercubicEvenSpatialSliceLinkColor H e = color}

/-- The Feller-closed one-link conditional expectations at distinct
spatial-slice links in one canonical six-color class commute exactly.  This is
just the bounded-continuous presentation of the already-canonical raw
heat-bath commutation theorem; no new independence hypothesis is introduced. -/
theorem
    periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkConditionalExpectationContinuousBCF_commute
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    {e f : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenSpatialSliceLinkColor H f)
    (hne : e ≠ f) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    C.singleLinkConditionalExpectationContinuousBCF
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)
        (C.singleLinkConditionalExpectationContinuousBCF
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) O) =
      C.singleLinkConditionalExpectationContinuousBCF
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)
        (C.singleLinkConditionalExpectationContinuousBCF
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) O) := by
  dsimp only
  ext A
  change
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkHeatBathTransform
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkHeatBathTransform
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) O) A =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkHeatBathTransform
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkHeatBathTransform
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) O) A
  exact congrFun
    (periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkHeatBathTransform_commute
      H N hN beta hbeta O O.continuous hColor hne) A

/-- One exact Feller heat-bath update restricted to a spatial link in one fixed
six-color class. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenSpatialBoundaryColor)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  C.singleLinkConditionalExpectationContinuousBCF
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H e.1) O

/-- Within one spatial six-color class, exact one-link Feller updates are
right-commutative.  The equal-link case is tautological; the distinct-link case
is the six-color commutation theorem above. -/
theorem
    periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep_rightCommutative
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenSpatialBoundaryColor) :
    RightCommutative
      (periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep
        H N hN beta hbeta color) := by
  constructor
  intro O e f
  by_cases hEq : f.1 = e.1
  · have hef : f = e := Subtype.ext hEq
    subst f
    rfl
  · have hColor :
      periodicHypercubicEvenSpatialSliceLinkColor H e.1 =
        periodicHypercubicEvenSpatialSliceLinkColor H f.1 :=
      e.property.trans f.property.symm
    simpa [periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep] using
      (periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkConditionalExpectationContinuousBCF_commute
        H N hN beta hbeta O hColor hEq.symm)

/-- Folding one fixed spatial six-color class is invariant under permutation of
the link list. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathFold_eq_of_perm
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenSpatialBoundaryColor)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    {l₁ l₂ : List (PeriodicHypercubicEvenFixedSpatialColorLink H color)}
    (hPerm : List.Perm l₁ l₂) :
    l₁.foldl
        (periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep
          H N hN beta hbeta color) O =
      l₂.foldl
        (periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep
          H N hN beta hbeta color) O := by
  letI : RightCommutative
      (periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep
        H N hN beta hbeta color) :=
    periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep_rightCommutative
      H N hN beta hbeta color
  exact hPerm.foldl_eq O

/-- Canonical parallel heat-bath block for one spatial six-color class.  Every
link in the color class is updated exactly once; permutation invariance makes
the `Finset.univ.toList` order only a presentation choice. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathBlock
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenSpatialBoundaryColor)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
  ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).foldl
    (periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep
      H N hN beta hbeta color) O

/-- Any permutation of a complete enumeration of one spatial six-color class
computes exactly the canonical parallel block. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathBlock_eq_fold_of_perm
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenSpatialBoundaryColor)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (l : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (hPerm :
      List.Perm l
        (Finset.univ :
          Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList) :
    l.foldl
        (periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathStep
          H N hN beta hbeta color) O =
      periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathBlock
        H N hN beta hbeta color O := by
  unfold periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathBlock
  exact
    periodicHypercubicEvenSpecialUnitaryFixedSpatialColorHeatBathFold_eq_of_perm
      H N hN beta hbeta color O hPerm

end

end MathlibAnalytic
end MGAP4D
