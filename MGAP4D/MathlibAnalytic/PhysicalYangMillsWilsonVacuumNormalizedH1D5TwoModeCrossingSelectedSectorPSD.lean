import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModePositiveDensityCrossingGram
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonFiniteSelectedSectorPSD
import Mathlib.Tactic

/-!
# H1-D5 crossing residual: protected selected Fock sector

#5048 rewrites the remaining two-mode obstruction as the bare temporal-gauge
crossing kernel integrated against the strictly positive spatial half-weight
density.

The crossing kernel is a finite product of exact one-link Wilson relative
kernels.  This file applies the generic finite-product selected-sector theorem
to that literal spatial-link product.

For the canonical primary spatial plaquette we mark exactly its four links.
Those four links may carry one common Taylor/Fock degree, while every other
spatial link is kept in the genuine degree-zero Wilson sector.  The full exact
crossing kernel minus this selected product is symmetric positive semidefinite.

No scalar sign is assigned to the omitted higher degrees, and no residual link
is deleted or replaced by one.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The four intrinsic primary-spatial plaquette links form an embedding into
the complete one-slice link carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeEmbedding
    (H : ℕ) :
    Fin 4 ↪ PeriodicHypercubicEvenSpatialSliceLink H where
  toFun := periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H
  inj' := by
    intro i j hij
    apply
      (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H).injective
    simpa only [
      periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding_eq_primarySliceLink
    ] using
      congrArg
        (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H)
        hij

/-- The actual four-link block of the canonical primary spatial plaquette. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet
    (H : ℕ) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Finset.univ.map
    (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeEmbedding H)

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge_mem_edgeSet
    (H : ℕ)
    (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k ∈
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet H := by
  classical
  simp [
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet,
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeEmbedding
  ]

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet_card
    (H : ℕ) :
    (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet H).card = 4 := by
  classical
  simp [periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet]

/-- The exact finite carrier already used by the literal crossing-kernel list. -/
noncomputable def
    periodicHypercubicEvenSpatialSliceLinkSet
    (H : ℕ) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact (periodicHypercubicEvenSpatialSliceLinkList H).toFinset

/-- The canonical crossing-kernel link list has no duplicate coordinates. -/
theorem periodicHypercubicEvenSpatialSliceLinkList_nodup
    (H : ℕ) :
    (periodicHypercubicEvenSpatialSliceLinkList H).Nodup := by
  classical
  unfold periodicHypercubicEvenSpatialSliceLinkList
  exact Finset.nodup_toList Finset.univ

/-- All one-slice links outside the canonical primary plaquette. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet
    (H : ℕ) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
  periodicHypercubicEvenSpatialSliceLinkSet H \
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet H

/-- The four canonical plaquette links carry the selected common degree;
every residual spatial link carries the genuine degree-zero Wilson component. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
    (H : ℕ)
    (selected : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℕ := by
  classical
  exact
    if e ∈ periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet H then
      selected
    else
      0

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment_primary
    (H : ℕ)
    (selected : ℕ)
    (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
        H selected
        (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k) =
      selected := by
  classical
  simp [
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
  ]

/-- Every literal residual spatial link is assigned degree zero. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment_eq_zero_of_mem_residual
    (H : ℕ)
    (selected : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (he :
      e ∈ periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H) :
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
        H selected e = 0 := by
  classical
  have hnot :
      e ∉ periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet H :=
    (Finset.mem_sdiff.mp he).2
  simp [
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment,
    hnot
  ]

/-- The literal list-product definition of the temporal crossing kernel is the
same product over the exact finite carrier obtained from that list. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_linkSet_prod
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta A B =
      ∏ e ∈ periodicHypercubicEvenSpatialSliceLinkSet H,
        specialUnitaryWilsonRelativeKernel N beta (A e) (B e) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  unfold periodicHypercubicEvenSpatialSliceLinkSet
  exact
    (List.prod_toFinset
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        specialUnitaryWilsonRelativeKernel N beta (A e) (B e))
      (periodicHypercubicEvenSpatialSliceLinkList_nodup H)).symm

/-- Exact cancellation-free selected-sector domination for the actual SU(2)
temporal crossing kernel.

The four primary-plaquette links carry the common selected degree.  Every
remaining spatial link contributes its actual degree-zero Wilson term. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_sub_primarySelectedDegreeProduct_positiveSemidefiniteCertificate
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (selected : ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
      (fun A B =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A B -
          ∏ e ∈ periodicHypercubicEvenSpatialSliceLinkSet H,
            specialUnitaryWilsonRelativeSelectedDegreeKernel
              2 beta
              (periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
                H selected e)
              (A e) (B e)) := by
  have C :=
    specialUnitaryWilsonRelativeKernel_finsetProd_sub_selectedDegreeProd_positiveSemidefiniteCertificate
      2 (by norm_num : 0 < (2 : ℕ)) beta hbeta
      (periodicHypercubicEvenSpatialSliceLinkSet H)
      (periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
        H selected)
  simpa only [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_linkSet_prod
  ] using C

/-- Pointwise exact decomposition corresponding to the preceding PSD
certificate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_eq_selectedRemainder_add_primarySelectedDegreeProduct
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 beta A B =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
          H 2 beta A B -
        ∏ e ∈ periodicHypercubicEvenSpatialSliceLinkSet H,
          specialUnitaryWilsonRelativeSelectedDegreeKernel
            2 beta
            (periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
              H selected e)
            (A e) (B e)) +
      ∏ e ∈ periodicHypercubicEvenSpatialSliceLinkSet H,
        specialUnitaryWilsonRelativeSelectedDegreeKernel
          2 beta
          (periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
            H selected e)
          (A e) (B e) := by
  ring

end

end MathlibAnalytic
end MGAP4D
