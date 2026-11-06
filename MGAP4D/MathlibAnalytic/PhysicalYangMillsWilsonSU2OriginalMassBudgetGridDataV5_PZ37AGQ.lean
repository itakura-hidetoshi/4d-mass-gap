import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceAdaptedCellwiseV5_PZ37AGP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGQ — original Haar mass accuracy after genuine grid selection

For any genuine original AGH spatial Borel grid and positive rational mass
budget eps, choose genuine cell masses first, use AFN rational density to
enclose each real mass, and set a per-cell radius only AFTER the number of
cells is known. Prove the summed rational interval widths are at most eps.

This does not assume that rational Haar endpoints sum to one, introduce a
proxy Haar law, or evaluate noncomputable finite enumerations. The original
physical signed transfer remains the same. For source-adapted AGP cellwise
intervals, the center-rationality condition remains an explicit input;
the existence of arbitrarily fine *rational-center* nets is not silently
deduced from the existence of arbitrary real-center finite nets.

The fixed 24-center AGO obstruction is unchanged. No physical nonzero
transfer sign, H-uniform coercivity, Hamiltonian or continuum mass gap
is claimed here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGQ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0
  (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AGQ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGQ_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A rational approximation to one ACTUAL Haar mass, not a surrogate
probability. The choice is noncomputable as in AFN, but its enclosure
is proved for the original probability measure. -/
def p4Q2PZ37AGQ_originalMassCenter
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (delta : ℚ) (hdelta : 0 < delta) (i : Fin grid.n) : ℚ :=
  p4Q2PZ37AFN_rationalEnclosure
    (Measure.real muH (grid.cell i)) (delta : ℝ)
    (by exact_mod_cast hdelta)

theorem p4Q2PZ37AGQ_originalMassCenter_accuracy
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (delta : ℚ) (hdelta : 0 < delta) (i : Fin grid.n) :
    |Measure.real muH (grid.cell i) -
      (p4Q2PZ37AGQ_originalMassCenter H grid delta hdelta i : ℝ)| ≤
        (delta : ℝ) := by
  exact p4Q2PZ37AFN_rationalEnclosure_error _
    (delta : ℝ) (by exact_mod_cast hdelta)

/-- Genuine mass endpoints with true per-cell error <= delta. -/
def p4Q2PZ37AGQ_originalMassIntervals
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (delta : ℚ) (hdelta : 0 < delta) :
    p4Q2PZ37AGN_massIntervals grid where
  lower := fun i => p4Q2PZ37AGQ_originalMassCenter H grid delta hdelta i - delta
  upper := fun i => p4Q2PZ37AGQ_originalMassCenter H grid delta hdelta i + delta
  hLower := by
    intro i
    have h := (abs_le.mp
      (p4Q2PZ37AGQ_originalMassCenter_accuracy H grid delta hdelta i)).1
    push_cast
    linarith only [h]
  hUpper := by
    intro i
    have h := (abs_le.mp
      (p4Q2PZ37AGQ_originalMassCenter_accuracy H grid delta hdelta i)).2
    push_cast
    linarith only [h]

/-- The width of every rational true-mass enclosure is EXACTLY 2delta. -/
theorem p4Q2PZ37AGQ_massWidth_exact
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (delta : ℚ) (hdelta : 0 < delta) (i : Fin grid.n) :
    (p4Q2PZ37AGQ_originalMassIntervals H grid delta hdelta).upper i -
      (p4Q2PZ37AGQ_originalMassIntervals H grid delta hdelta).lower i =
        2 * delta := by
  change (p4Q2PZ37AGQ_originalMassCenter H grid delta hdelta i + delta) -
    (p4Q2PZ37AGQ_originalMassCenter H grid delta hdelta i - delta) =
      2 * delta
  ring

/-- The finite number of ORIGINAL spatial Borel cells is included in
the total mass accuracy budget, not discarded by a dimension-free bound. -/
theorem p4Q2PZ37AGQ_massWidths_sum_exact
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (delta : ℚ) (hdelta : 0 < delta) :
    (∑ i : Fin grid.n,
        ((p4Q2PZ37AGQ_originalMassIntervals H grid delta hdelta).upper i -
          (p4Q2PZ37AGQ_originalMassIntervals H grid delta hdelta).lower i)) =
      (grid.n : ℚ) * (2 * delta) := by
  calc
    (∑ i : Fin grid.n,
        ((p4Q2PZ37AGQ_originalMassIntervals H grid delta hdelta).upper i -
          (p4Q2PZ37AGQ_originalMassIntervals H grid delta hdelta).lower i)) =
      ∑ _i : Fin grid.n, (2 * delta) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact p4Q2PZ37AGQ_massWidth_exact H grid delta hdelta i
    _ = (grid.n : ℚ) * (2 * delta) := by
      simp [nsmul_eq_mul]

/-- Mass precision is fixed only AFTER the genuine finite grid size n
has been determined, avoiding the uncontrolled n * delta trap. -/
def p4Q2PZ37AGQ_deltaOfTotalBudget
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) (eps : ℚ) : ℚ :=
  (eps / ((grid.n : ℚ) + 1)) / 2

theorem p4Q2PZ37AGQ_deltaOfTotalBudget_pos
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (eps : ℚ) (heps : 0 < eps) :
    0 < p4Q2PZ37AGQ_deltaOfTotalBudget H grid eps := by
  unfold p4Q2PZ37AGQ_deltaOfTotalBudget
  positivity

def p4Q2PZ37AGQ_originalMassIntervalsOfBudget
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (eps : ℚ) (heps : 0 < eps) :
    p4Q2PZ37AGN_massIntervals grid :=
  p4Q2PZ37AGQ_originalMassIntervals H grid
    (p4Q2PZ37AGQ_deltaOfTotalBudget H grid eps)
    (p4Q2PZ37AGQ_deltaOfTotalBudget_pos H grid eps heps)

/-- Arbitrarily small certified TOTAL rational mass interval width for
the true original product Haar cells, without an unknown mass oracle. -/
theorem p4Q2PZ37AGQ_totalMassWidth_le
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (eps : ℚ) (heps : 0 < eps) :
    (∑ i : Fin grid.n,
      ((p4Q2PZ37AGQ_originalMassIntervalsOfBudget H grid eps heps).upper i -
      (p4Q2PZ37AGQ_originalMassIntervalsOfBudget H grid eps heps).lower i)) ≤
        eps := by
  have h := (p4Q2PZ37AGP_radiusBudget
    (grid.n : ℚ) (grid.n : ℚ) eps (by positivity) le_rfl heps).2
  rw [show
    (∑ i : Fin grid.n,
      ((p4Q2PZ37AGQ_originalMassIntervalsOfBudget H grid eps heps).upper i -
      (p4Q2PZ37AGQ_originalMassIntervalsOfBudget H grid eps heps).lower i)) =
        (grid.n : ℚ) * (2 * p4Q2PZ37AGQ_deltaOfTotalBudget H grid eps) from
    p4Q2PZ37AGQ_massWidths_sum_exact H grid
      (p4Q2PZ37AGQ_deltaOfTotalBudget H grid eps)
      (p4Q2PZ37AGQ_deltaOfTotalBudget_pos H grid eps heps)]
  calc
    (grid.n : ℚ) * (2 * p4Q2PZ37AGQ_deltaOfTotalBudget H grid eps) =
      (grid.n : ℚ) * (eps / ((grid.n : ℚ) + 1)) := by
        unfold p4Q2PZ37AGQ_deltaOfTotalBudget
        ring
    _ ≤ eps := h

/-- The AGP proof-carrying data no longer requests ANY rational Haar
mass bounds: choose verified ones from the genuine cells at any precision.
Only the rationality of the selected centers and a radius cover remain. -/
def p4Q2PZ37AGQ_gridDataOfRationalCenters
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (centers : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e))
    (r : ℚ) (hr : 0 ≤ r) (hCover : grid.radius ≤ (r : ℝ))
    (eps : ℚ) (heps : 0 < eps) :
    p4Q2PZ37AGP_gridData H where
  grid := grid
  centerCoordinates := centers
  radii := p4Q2PZ37AGP_cellRadii_ofUniform H grid r hr hCover
  masses := p4Q2PZ37AGQ_originalMassIntervalsOfBudget H grid eps heps

/-- The mass-budget data are certified against the unchanged original
signed transfer and may be tightened by the genuine original global range. -/
def p4Q2PZ37AGQ_originalTransferInterval
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (centers : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e))
    (r : ℚ) (hr : 0 ≤ r) (hCover : grid.radius ≤ (r : ℝ))
    (eps : ℚ) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (t B) :=
  p4Q2PZ37AGP_originalTightenedInterval H
    (p4Q2PZ37AGQ_gridDataOfRationalCenters H grid centers r hr hCover eps heps)
    B b m n hn (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_originalMassCenter_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_originalMassIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_massWidth_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_massWidths_sum_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_deltaOfTotalBudget_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_originalMassIntervalsOfBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_totalMassWidth_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_gridDataOfRationalCenters
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGQ_originalTransferInterval
