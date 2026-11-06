import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRationalDensityV5_PZ37AGS
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGT — unconditional original spatial rational-Haar grid

AGS's actual two-chart rational SU(2) finite cover is now used on all
genuine spatial links, with original AGH Borel cells, AGQ true product-Haar
mass precision and AGP source-sensitive signed-transfer intervals.

All choices are existence-level, not evaluated finite numerical data.
No new physical nonzero signed transfer, H-uniform coercivity, or mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1

/-- Both stereographic chart signs retain exact rational coordinates in
the existing original SU(2) convention of AGL/ADR. -/
def p4Q2PZ37AGT_originalSignedCenter_rational
    (b : Bool) (t : Fin 3 → ℚ) :
    p4Q2PZ37AGL_rationalCoordinates
      (p4Q2PZ37AGS_originalSignedCenter b t) where
  value := fun j =>
    if b then -(p4Q2PZ37AGR_rationalSphereCoordinates t j)
      else p4Q2PZ37AGR_rationalSphereCoordinates t j
  hValue := by
    intro j
    have h := congrArg (fun z : S3 => (z : E4) j)
      (p4Q2PZ37ADS_sphere_roundtrip
        (p4Q2PZ37AGS_signedRationalSphere b t))
    have hOriginal :
        p4Q2PZ37ADR_originalFourCoordinates
          (p4Q2PZ37AGS_originalSignedCenter b t) j =
            (p4Q2PZ37AGS_signedRationalSphere b t : E4) j := by
      simpa [p4Q2PZ37ADR_originalSU2ToSphere,
        p4Q2PZ37AGS_originalSignedCenter] using h
    cases b with
    | false =>
        simpa [p4Q2PZ37AGS_signedRationalSphere,
          p4Q2PZ37AGR_rationalSphere] using hOriginal
    | true =>
        simpa [p4Q2PZ37AGS_signedRationalSphere,
          p4Q2PZ37AGS_antipode_apply,
          p4Q2PZ37AGR_rationalSphere] using hOriginal

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AGT_links : Fintype Link := Fintype.ofFinite _

/-- Arbitrarily fine AUTHENTIC original Borel spatial grids with
pointwise rational evidence on all original SU(2) links, constructed
without any supplied external finite-net covering certificate. -/
theorem p4Q2PZ37AGT_exists_fineOriginalRationalSpatialGrid
    (R : ℚ) (hR : 0 < R) :
    ∃ grid : p4Q2PZ37AGH_originalSpatialGrid H,
      Nonempty (∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e)) ∧
      grid.radius ≤ (R : ℝ) := by
  let L : ℝ := (Fintype.card Link : ℝ)
  let rho : ℝ := (R : ℝ) / (L + 1)
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hrho : 0 < rho := div_pos hRreal (by dsimp [L]; positivity)
  obtain ⟨n, parameters, hCover⟩ :=
    p4Q2PZ37AGS_exists_originalFiniteRationalCover rho hrho
  let centers : Fin n → G := fun i =>
    p4Q2PZ37AGS_originalSignedCenter (parameters i).1 (parameters i).2
  let grid := p4Q2PZ37AGH_gridOfCover H n centers rho hrho hCover
  have hCoordinates : ∀ i : Fin grid.n, ∀ e : Link,
      p4Q2PZ37AGL_rationalCoordinates (grid.center i e) := by
    intro i e
    change p4Q2PZ37AGL_rationalCoordinates
      (p4Q2PZ37AGS_originalSignedCenter
        (parameters ((Fintype.equivFin (Link → Fin n)).symm i e)).1
        (parameters ((Fintype.equivFin (Link → Fin n)).symm i e)).2)
    exact p4Q2PZ37AGT_originalSignedCenter_rational _ _
  have hRadius : grid.radius ≤ (R : ℝ) := by
    change (Fintype.card Link : ℝ) * rho ≤ (R : ℝ)
    exact p4Q2PZ37AGH_normalizedBudget_le L (R : ℝ) hL hRreal.le
  exact ⟨grid, ⟨hCoordinates⟩, hRadius⟩

/-- No external grid, mass oracle, radius proof or rational-center
assumption remains. Choose true product Haar mass intervals with any
positive total rational width budget AFTER the finite grid is selected. -/
theorem p4Q2PZ37AGT_exists_fineOriginalGridData
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps) :
    Nonempty (p4Q2PZ37AGP_gridData H) := by
  obtain ⟨grid, hCenters, hRadius⟩ :=
    p4Q2PZ37AGT_exists_fineOriginalRationalSpatialGrid H R hR
  exact ⟨p4Q2PZ37AGQ_gridDataOfRationalCenters
    H grid (Classical.choice hCenters) R hR.le hRadius eps heps⟩

/-- A proof-carrying original spatial grid at any requested rational
geometry/mass accuracy; noncomputable choice is NOT numeric computation. -/
def p4Q2PZ37AGT_fineOriginalGridData
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps) :
    p4Q2PZ37AGP_gridData H :=
  Classical.choice (p4Q2PZ37AGT_exists_fineOriginalGridData H R eps hR heps)

/-- The UNCHANGED original physical signed transfer is now enclosed by
arbitrarily fine genuine rational-center spatial Borel grids with true
Haar mass accuracy, and the previous bound is retained by intersection.
No actual nonzero sign is claimed. -/
def p4Q2PZ37AGT_fineOriginalTransferInterval
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (t B) :=
  p4Q2PZ37AGP_originalTightenedInterval H
    (p4Q2PZ37AGT_fineOriginalGridData H R eps hR heps)
    B b m n hn (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)

end GroundStatePosteriorJoint

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGT_originalSignedCenter_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGT_exists_fineOriginalRationalSpatialGrid
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGT_exists_fineOriginalGridData
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGT_fineOriginalGridData
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGT_fineOriginalTransferInterval
