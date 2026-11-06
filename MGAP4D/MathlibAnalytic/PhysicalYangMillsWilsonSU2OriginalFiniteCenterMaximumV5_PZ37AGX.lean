import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenterWidthFactorizationV5_PZ37AGW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGX — original finite-center maximum is a genuine eta witness

AGW identifies the exact source-dependent width at each actual AGN rational
center. The finite original AGU grid is nonempty because its Borel
partition covers the genuine original spatial configuration space.
Consequently the *maximum* of those exact widths is a rational quantity
defined on the SAME selected precision-bearing grid.

AGX substitutes this automatically certified quantity for AGV's supplied
uniform center-width hypothesis. No finite sum factor, no fake normalized
rational Haar endpoints, and no hypothesis about unknown physical signs.
The selected grid is in general noncomputable: this finite maximum is
a type-correct exact rational expression, not an evaluated numerical table.
No uniform convergence or arbitrary eta precision is claimed here.
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
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AGX_links : Fintype Link := Fintype.ofFinite _

/-- The genuine spatial grid cannot be empty: apply its own partition
witness to the constant identity original SU(2) configuration. -/
def p4Q2PZ37AGX_univNonempty
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps) :
    (Finset.univ : Finset (Fin d.data.grid.n)).Nonempty := by
  let A : Cfg := fun _ => 1
  obtain ⟨i, _, _⟩ := d.data.grid.hPartition A
  exact ⟨i, Finset.mem_univ i⟩

/-- The exact rational maximum of the true AGN center interval widths
on the SAME original AGU grid and right boundary. No new eta oracle. -/
def p4Q2PZ37AGX_actualCenterMax
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : ℚ :=
  (Finset.univ : Finset (Fin d.data.grid.n)).sup'
    (p4Q2PZ37AGX_univNonempty H d)
    (fun i => p4Q2PZ37AGW_centerWidthFormula H
      (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn)

/-- Every actual center's original AGN interval width is bounded by
the MAXIMUM on the SAME chosen genuine grid. -/
theorem p4Q2PZ37AGX_actualCenterMax_certifies
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.data.grid.n) :
    (p4Q2PZ37AGN_originalIntegrandInterval H
      (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn).upper -
      (p4Q2PZ37AGN_originalIntegrandInterval H
        (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn).lower ≤
      p4Q2PZ37AGX_actualCenterMax H d B b m n hn := by
  rw [p4Q2PZ37AGW_originalCenterWidth_exact H
    (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn]
  exact Finset.le_sup'
    (s := (Finset.univ : Finset (Fin d.data.grid.n)))
    (f := fun j => p4Q2PZ37AGW_centerWidthFormula H
      (d.data.grid.center j) B (d.data.centerCoordinates j) b m n hn)
    (Finset.mem_univ i)

/-- This maximum is nonnegative because every AGN center interval
contains the genuine original real integrand value. -/
theorem p4Q2PZ37AGX_actualCenterMax_nonneg
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AGX_actualCenterMax H d B b m n hn := by
  let A : Cfg := fun _ => 1
  obtain ⟨i, _, _⟩ := d.data.grid.hPartition A
  have hWidth :=
    p4Q2PZ37AGW_originalCenterWidth_nonneg H
      (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn
  exact hWidth.trans
    (p4Q2PZ37AGX_actualCenterMax_certifies H d B b m n hn i)

/-- No external eta premise remains: feed the automatically defined
actual center-width maximum into the unchanged genuine AGV theorem.
The result still explicitly depends on that maximum, so the radius and
Haar precision alone do not establish arbitrarily narrow intervals. -/
theorem p4Q2PZ37AGX_originalRawWidth_le
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (hR : 0 ≤ R)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGP_originalRawInterval H d.data B b m n hn).upper -
      (p4Q2PZ37AGP_originalRawInterval H d.data B b m n hn).lower ≤
      p4Q2PZ37AGX_actualCenterMax H d B b m n hn +
        2 * p4Q2PZ37AGV_uniformSlope H m * R +
        2 * p4Q2PZ37AGN_transferRadius H m n hn * eps := by
  exact p4Q2PZ37AGV_originalRawTransferWidth_le H
    d hR B b m n hn
    (p4Q2PZ37AGX_actualCenterMax H d B b m n hn)
    (p4Q2PZ37AGX_actualCenterMax_nonneg H d B b m n hn)
    (p4Q2PZ37AGX_actualCenterMax_certifies H d B b m n hn)

/-- The final original signed transfer uses precisely the classically
selected AGU precision package. Its center error is the exact finite
maximum of the original AGN values on THAT very package, rather than
an independently asserted bound. -/
theorem p4Q2PZ37AGX_fineOriginalTransferWidth_le
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).upper -
      (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).lower ≤
      p4Q2PZ37AGX_actualCenterMax H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps) B b m n hn +
        2 * p4Q2PZ37AGV_uniformSlope H m * R +
        2 * p4Q2PZ37AGN_transferRadius H m n hn * eps := by
  let d := p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps
  exact p4Q2PZ37AGV_fineTransferWidth_le H
    R eps hR heps B b m n hn
    (p4Q2PZ37AGX_actualCenterMax H d B b m n hn)
    (p4Q2PZ37AGX_actualCenterMax_nonneg H d B b m n hn)
    (p4Q2PZ37AGX_actualCenterMax_certifies H d B b m n hn)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGX_univNonempty
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGX_actualCenterMax
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGX_actualCenterMax_certifies
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGX_actualCenterMax_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGX_originalRawWidth_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGX_fineOriginalTransferWidth_le
