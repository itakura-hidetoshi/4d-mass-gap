import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpatialSignedPermutationShiftCovariance

/-!
# Signed image of a positive physical edge as a boundary step

The abstract signed-coordinate group acts on periodic vertices and its effect on unit shifts is now
canonical.  A general signed spatial symmetry does not preserve the positive-link carrier literally:
a reflected positive link becomes a negatively traversed link.  The right geometric object is
therefore a signed `PeriodicHypercubicBoundaryStep` whose underlying edge is always represented by
the canonical positive-link carrier.

For a positive edge `(x, μ)`:

* the Euclidean-time edge stays forward at the transformed source;
* a spatial edge with positive image sign stays forward along the permuted image axis;
* a spatial edge with negative image sign is represented by the positive edge whose source is one
  unit behind the transformed source, traversed backward.

The main theorems prove that the signed image has exactly the transformed source and transformed
target.  This is the incidence-level geometric receipt needed before defining a general transformed
gauge configuration.  No gauge value, plaquette holonomy, cubic irrep, continuum spin, or spectral
claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Signed geometric image of one positively oriented physical edge under an abstract signed spatial
permutation.  The underlying edge always lies in the canonical positive-link carrier; orientation
records whether the geometric image is traversed forward or backward. -/
def periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (e : PeriodicHypercubicEdge n) :
    PeriodicHypercubicBoundaryStep n :=
  Fin.cases
    { edge :=
        (periodicHypercubicVertexSpatialSignedPermutation n g e.1, 0)
      orientation := .forward }
    (fun k : Fin 3 =>
      let μ' := periodicHypercubicSpatialSignedPermutationAxis g k
      if g.left (g.right k) = 1 then
        { edge :=
            (periodicHypercubicVertexSpatialSignedPermutation n g e.1, μ')
          orientation := .forward }
      else
        { edge :=
            (periodicHypercubicUnshift n
              (periodicHypercubicVertexSpatialSignedPermutation n g e.1) μ', μ')
          orientation := .backward })
    e.2

/-- The signed image of a time-directed positive edge remains a forward time-directed edge. -/
@[simp]
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_time
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n) :
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n g (x, 0) =
      { edge :=
          (periodicHypercubicVertexSpatialSignedPermutation n g x, 0)
        orientation := .forward } := by
  rfl

/-- With positive image sign, a spatial positive edge remains a forward positive edge along the
permuted image axis. -/
@[simp]
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_spatial_of_pos
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n)
    (k : Fin 3)
    (hpos : g.left (g.right k) = 1) :
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n g (x, Fin.succ k) =
      { edge :=
          (periodicHypercubicVertexSpatialSignedPermutation n g x,
            periodicHypercubicSpatialSignedPermutationAxis g k)
        orientation := .forward } := by
  simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep, hpos]

/-- With negative image sign, a spatial positive edge is represented by one positive edge starting
one step behind the transformed source and traversed backward. -/
@[simp]
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_spatial_of_neg
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n)
    (k : Fin 3)
    (hneg : g.left (g.right k) ≠ 1) :
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n g (x, Fin.succ k) =
      { edge :=
          (periodicHypercubicUnshift n
            (periodicHypercubicVertexSpatialSignedPermutation n g x)
            (periodicHypercubicSpatialSignedPermutationAxis g k),
            periodicHypercubicSpatialSignedPermutationAxis g k)
        orientation := .backward } := by
  simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep, hneg]

/-- The source of the signed image is exactly the image of the original positive-edge source. -/
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_source
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n g e).source =
      periodicHypercubicVertexSpatialSignedPermutation n g
        (periodicHypercubicEdgeSource n e) := by
  rcases e with ⟨x, μ⟩
  refine Fin.cases ?_ (fun k => ?_) μ
  · rfl
  · by_cases hpos : g.left (g.right k) = 1
    · simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep,
        hpos, PeriodicHypercubicBoundaryStep.source,
        periodicHypercubicEdgeSource]
    · simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep,
        hpos, PeriodicHypercubicBoundaryStep.source,
        periodicHypercubicEdgeSource, periodicHypercubicEdgeTarget]

/-- The target of the signed image is exactly the image of the original positive-edge target. -/
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_target
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n g e).target =
      periodicHypercubicVertexSpatialSignedPermutation n g
        (periodicHypercubicEdgeTarget n e) := by
  rcases e with ⟨x, μ⟩
  refine Fin.cases ?_ (fun k => ?_) μ
  · change
      periodicHypercubicShift n
          (periodicHypercubicVertexSpatialSignedPermutation n g x) 0 =
        periodicHypercubicVertexSpatialSignedPermutation n g
          (periodicHypercubicShift n x 0)
    exact
      (periodicHypercubicVertexSpatialSignedPermutation_shift_time n g x).symm
  · by_cases hpos : g.left (g.right k) = 1
    · rw [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_spatial_of_pos
        n g x k hpos]
      change
        periodicHypercubicShift n
            (periodicHypercubicVertexSpatialSignedPermutation n g x)
            (periodicHypercubicSpatialSignedPermutationAxis g k) =
          periodicHypercubicVertexSpatialSignedPermutation n g
            (periodicHypercubicShift n x (Fin.succ k))
      exact
        (periodicHypercubicVertexSpatialSignedPermutation_shift_spatial_of_pos
          n g x k hpos).symm
    · rw [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_spatial_of_neg
        n g x k hpos]
      change
        periodicHypercubicUnshift n
            (periodicHypercubicVertexSpatialSignedPermutation n g x)
            (periodicHypercubicSpatialSignedPermutationAxis g k) =
          periodicHypercubicVertexSpatialSignedPermutation n g
            (periodicHypercubicShift n x (Fin.succ k))
      have h :=
        periodicHypercubicVertexSpatialSignedPermutation_shift_spatial n g x k
      rw [if_neg hpos] at h
      exact h.symm

end

end MathlibAnalytic
end MGAP4D
