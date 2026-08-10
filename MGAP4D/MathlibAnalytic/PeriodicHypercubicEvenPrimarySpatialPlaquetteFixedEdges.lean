import MGAP4D.MathlibAnalytic.FiniteProductProbabilityRestrictionL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeSideClassification
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedHaarPlaquetteWordL2Orthonormal

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical plaquette on the primary reflection-fixed time slice, based
at the zero vertex and spanning spatial axes `1` and `2`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquette
    (H : ℕ) : PeriodicHypercubicEvenPlaquette H :=
  ((0 : PeriodicHypercubicEvenVertex H),
    ⟨((1 : PeriodicHypercubicAxis), (2 : PeriodicHypercubicAxis)), by decide⟩)

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquette_firstAxis
    (H : ℕ) :
    periodicHypercubicPlaquetteFirstAxis
        (periodicHypercubicEvenPrimarySpatialPlaquette H) =
      (1 : PeriodicHypercubicAxis) := by
  rfl

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquette_secondAxis
    (H : ℕ) :
    periodicHypercubicPlaquetteSecondAxis
        (periodicHypercubicEvenPrimarySpatialPlaquette H) =
      (2 : PeriodicHypercubicAxis) := by
  rfl

/-- The physical positive link underlying the `k`-th signed boundary incidence
of the canonical primary spatial plaquette. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteEdge
    (H : ℕ) (k : Fin 4) : PeriodicHypercubicEvenEdge H :=
  (periodicHypercubicBoundaryStep
    (PeriodicHypercubicEvenSideLength H)
    (periodicHypercubicEvenPrimarySpatialPlaquette H) k).edge

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteEdge_zero
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0 =
      ((0 : PeriodicHypercubicEvenVertex H), (1 : PeriodicHypercubicAxis)) := by
  rfl

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteEdge_one
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 1 =
      (periodicHypercubicShift
          (PeriodicHypercubicEvenSideLength H)
          (0 : PeriodicHypercubicEvenVertex H) (1 : PeriodicHypercubicAxis),
        (2 : PeriodicHypercubicAxis)) := by
  rfl

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteEdge_two
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 2 =
      (periodicHypercubicShift
          (PeriodicHypercubicEvenSideLength H)
          (0 : PeriodicHypercubicEvenVertex H) (2 : PeriodicHypercubicAxis),
        (1 : PeriodicHypercubicAxis)) := by
  rfl

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteEdge_three
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 3 =
      ((0 : PeriodicHypercubicEvenVertex H), (2 : PeriodicHypercubicAxis)) := by
  rfl

/-- A unit spatial shift of the zero vertex is nonzero on every even periodic
lattice.  The only arithmetic input is that the side length `2(H+1)` is at
least two. -/
theorem periodicHypercubicEvenShift_zero_ne_zero
    (H : ℕ) (mu : PeriodicHypercubicAxis) :
    periodicHypercubicShift
        (PeriodicHypercubicEvenSideLength H)
        (0 : PeriodicHypercubicEvenVertex H) mu ≠ 0 := by
  intro h
  have hmu := congrFun h mu
  have hone :
      (1 : ZMod (PeriodicHypercubicEvenSideLength H)) = 0 := by
    simpa [periodicHypercubicShift_apply] using hmu
  have hval := congrArg ZMod.val hone
  simpa [periodicHypercubicEven_one_val H] using hval

/-- Every physical edge of the canonical spatial plaquette lies in the
reflection-fixed edge sector: both directions are spatial and all four source
time coordinates are zero. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteEdge_side_fixed
    (H : ℕ) (k : Fin 4) :
    periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k) =
        ReflectionEdgeSide.fixed := by
  fin_cases k <;>
    apply periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero <;>
    simp [periodicHypercubicEvenPrimarySpatialPlaquetteEdge,
      periodicHypercubicEvenPrimarySpatialPlaquette,
      periodicHypercubicPlaquetteFirstAxis,
      periodicHypercubicPlaquetteSecondAxis,
      periodicHypercubicShift_apply]

/-- The four physical edges of the canonical spatial plaquette are pairwise
distinct.  In the two equal-direction comparisons, distinctness reduces to a
nonzero unit spatial shift. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteEdge_injective
    (H : ℕ) :
    Function.Injective (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [periodicHypercubicEvenPrimarySpatialPlaquetteEdge,
      periodicHypercubicEvenPrimarySpatialPlaquette,
      periodicHypercubicPlaquetteFirstAxis,
      periodicHypercubicPlaquetteSecondAxis,
      periodicHypercubicEvenShift_zero_ne_zero H] at hij ⊢

/-- The canonical four plaquette edges as an embedding into the actual
reflection-fixed boundary edge index. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding
    (H : ℕ) :
    Fin 4 ↪ (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge where
  toFun k :=
    ⟨periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k,
      periodicHypercubicEvenPrimarySpatialPlaquetteEdge_side_fixed H k⟩
  inj' := by
    intro i j h
    apply periodicHypercubicEvenPrimarySpatialPlaquetteEdge_injective H
    exact Subtype.ext_iff.mp h

/-- The actual selected boundary-edge block occupied by the canonical primary
spatial plaquette. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeSet
    (H : ℕ) :
    Finset (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge :=
  Finset.univ.map
    (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H)

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeSet_card
    (H : ℕ) :
    (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeSet H).card = 4 := by
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeSet]

end

end MathlibAnalytic
end MGAP4D
