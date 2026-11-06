import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnconditionalFineHaarGridV5_PZ37AGT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGU — requested precision carried by the chosen original grid

AGT proves genuine rational spatial grids exist at every positive radius.
Its later unindexed `Nonempty (AGP_gridData H)` result does not retain the
requested radius or mass-width predicates. Choosing from that unindexed
proposition therefore provides valid original data, but does not export
those quantitative specifications for the selected object.

This append-only leaf keeps the original AGP data inside a Type indexed by
the requested rational radius R and total mass-width budget eps. Its fields
certify the actual grid radius, each actual cell radius, and the sum of the
actual original-Haar mass interval widths. Classical choice now selects
that indexed package, so every projection retains its requested bounds.

The same selected data enters the original AGP signed-transfer evaluator,
and intersection preserves the previous verified interval. No final
transfer-interval width estimate, evaluated Haar table, nonzero physical
sign, H-uniform coercivity, or continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AGU_links : Fintype Link := Fintype.ofFinite _

/-- Proof irrelevance identifies all proofs of the same unindexed
`Nonempty` proposition. The old selected AGP data is consequently
independent of the requested budgets. This does not invalidate its
verified-interval membership; it identifies the missing quantitative
specification in that choice interface. -/
theorem p4Q2PZ37AGU_unindexedChoice_budget_independent
    (R eps S eta : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (hS : 0 < S) (heta : 0 < eta) :
    p4Q2PZ37AGT_fineOriginalGridData H R eps hR heps =
      p4Q2PZ37AGT_fineOriginalGridData H S eta hS heta := by
  rfl

/-- The requested geometry and mass accuracy belong to the chosen Type,
together with the SAME genuine original AGP data. In particular, the mass
budget concerns the intervals attached to this very grid. -/
structure p4Q2PZ37AGU_precisionGridData (H : ℕ) (R eps : ℚ) where
  data : p4Q2PZ37AGP_gridData H
  hGridRadius : data.grid.radius ≤ (R : ℝ)
  hCellRadius : ∀ i : Fin data.grid.n, data.radii.radius i = R
  hTotalMassWidth :
    (∑ i : Fin data.grid.n, (data.masses.upper i - data.masses.lower i)) ≤ eps

/-- Retain a supplied genuine rational grid and AGQ's exact original-Haar
interval object, while carrying all requested accuracy witnesses in the
result Type. The per-cell radius is exactly the supplied rational R. -/
def p4Q2PZ37AGU_precisionDataOfRationalGrid
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (centers : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e))
    (R eps : ℚ) (hR : 0 ≤ R) (hRadius : grid.radius ≤ (R : ℝ))
    (heps : 0 < eps) :
    p4Q2PZ37AGU_precisionGridData H R eps where
  data := p4Q2PZ37AGQ_gridDataOfRationalCenters H grid centers R hR hRadius eps heps
  hGridRadius := hRadius
  hCellRadius := by
    intro i
    rfl
  hTotalMassWidth := p4Q2PZ37AGQ_totalMassWidth_le H grid eps heps

/-- The indexed constructor preserves the exact supplied spatial grid. -/
theorem p4Q2PZ37AGU_precisionDataOfRationalGrid_grid_eq
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (centers : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e))
    (R eps : ℚ) (hR : 0 ≤ R) (hRadius : grid.radius ≤ (R : ℝ))
    (heps : 0 < eps) :
    (p4Q2PZ37AGU_precisionDataOfRationalGrid H grid centers
      R eps hR hRadius heps).data.grid = grid := by
  rfl

/-- The indexed constructor preserves the precise AGQ interval object
whose widths were proved to satisfy the requested total Haar budget. -/
theorem p4Q2PZ37AGU_precisionDataOfRationalGrid_masses_eq
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (centers : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e))
    (R eps : ℚ) (hR : 0 ≤ R) (hRadius : grid.radius ≤ (R : ℝ))
    (heps : 0 < eps) :
    (p4Q2PZ37AGU_precisionDataOfRationalGrid H grid centers
      R eps hR hRadius heps).data.masses =
        p4Q2PZ37AGQ_originalMassIntervalsOfBudget H grid eps heps := by
  rfl

/-- First select genuine rational geometry using AGT, then choose true
Haar intervals using AGQ after the finite grid is known. The conclusion
retains BOTH requested budgets, rather than erasing them to bare data. -/
theorem p4Q2PZ37AGU_exists_precisionGridData
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps) :
    Nonempty (p4Q2PZ37AGU_precisionGridData H R eps) := by
  obtain ⟨grid, hCenters, hRadius⟩ :=
    p4Q2PZ37AGT_exists_fineOriginalRationalSpatialGrid H R hR
  exact ⟨p4Q2PZ37AGU_precisionDataOfRationalGrid H grid
    (Classical.choice hCenters) R eps hR.le hRadius heps⟩

/-- Classical choice of precision-indexed original data. Its Type fields
retain the specifications, though its finite data are not numerically
evaluated by this construction. -/
def p4Q2PZ37AGU_fineOriginalGridData
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps) :
    p4Q2PZ37AGU_precisionGridData H R eps :=
  Classical.choice (p4Q2PZ37AGU_exists_precisionGridData H R eps hR heps)

/-- Radius guarantee for the actual selected spatial grid. -/
theorem p4Q2PZ37AGU_fineOriginalGridData_radius_le
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps) :
    (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data.grid.radius ≤
      (R : ℝ) :=
  (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).hGridRadius

/-- Every cell of the actual selected grid has the requested rational
radius in its original AGP pointwise geometry certificate. -/
theorem p4Q2PZ37AGU_fineOriginalGridData_cellRadius_eq
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (i : Fin (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data.grid.n) :
    (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data.radii.radius i = R :=
  (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).hCellRadius i

/-- Total true-Haar mass interval accuracy for the SAME selected grid.
The finite cell count is retained in AGQ's post-grid budget construction. -/
theorem p4Q2PZ37AGU_fineOriginalGridData_totalMassWidth_le
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps) :
    (∑ i : Fin (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data.grid.n,
      ((p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data.masses.upper i -
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data.masses.lower i)) ≤
      eps :=
  (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).hTotalMassWidth

/-- Evaluate the very same precision-carrying data with the unchanged
AGP original signed-transfer certificate, intersecting any earlier
verified interval of this exact same physical value. -/
def p4Q2PZ37AGU_originalTightenedInterval
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (previous : p4Q2PZ37AFV_verifiedInterval (t B)) :
    p4Q2PZ37AFV_verifiedInterval (t B) :=
  p4Q2PZ37AGP_originalTightenedInterval H d.data B b m n hn previous

theorem p4Q2PZ37AGU_originalTightenedInterval_subset
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (previous : p4Q2PZ37AFV_verifiedInterval (t B)) :
    previous.lower ≤
        (p4Q2PZ37AGU_originalTightenedInterval H d B b m n hn previous).lower ∧
      (p4Q2PZ37AGU_originalTightenedInterval H d B b m n hn previous).upper ≤
        previous.upper :=
  p4Q2PZ37AGP_originalTightenedInterval_subset H d.data B b m n hn previous

/-- A verified interval for the original physical signed transfer using
the selected indexed data and the independently proved global interval.
The geometry and mass guarantees are those of that exact selected data. -/
def p4Q2PZ37AGU_fineOriginalTransferInterval
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (t B) :=
  p4Q2PZ37AGU_originalTightenedInterval H
    (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps)
    B b m n hn (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)

/-- The selected transfer interval uses the exact original data whose
radius and mass-width projections were proved above. -/
theorem p4Q2PZ37AGU_fineOriginalTransferInterval_eq_sameData
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn =
      p4Q2PZ37AGP_originalTightenedInterval H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
        B b m n hn (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn) := by
  rfl

/-- The new selected interval retains the earlier genuine global bound.
No convergence rate or strict improvement of the endpoints is asserted. -/
theorem p4Q2PZ37AGU_fineOriginalTransferInterval_subset_global
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn).lower ≤
        (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).lower ∧
      (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).upper ≤
        (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn).upper :=
  p4Q2PZ37AGU_originalTightenedInterval_subset H
    (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps)
    B b m n hn (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)

end GroundStatePosteriorJoint

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_unindexedChoice_budget_independent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_precisionDataOfRationalGrid
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_precisionDataOfRationalGrid_grid_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_precisionDataOfRationalGrid_masses_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_exists_precisionGridData
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_fineOriginalGridData
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_fineOriginalGridData_radius_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_fineOriginalGridData_cellRadius_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_fineOriginalGridData_totalMassWidth_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_originalTightenedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_originalTightenedInterval_subset
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_fineOriginalTransferInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_fineOriginalTransferInterval_eq_sameData
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGU_fineOriginalTransferInterval_subset_global
