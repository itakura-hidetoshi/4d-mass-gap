import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalAverageMinorBoundV5_LP
import Mathlib.Tactic

/-!
# P4-Q2-LQ — exact original spatial plaquette-cardinality and a squared minor
# lower bound for the REAL local physical Gauss-law GI detector coercivity.

LP has proved, unconditionally at every finite H and b > 0, that the
original complete interacting SU(2) Wilson spatial action's authentic
two-context GI determinant can be detected by one original plaquette
with |Δ_p| ≥ |Δ_total| / N_H, N_H the exact original spatial
plaquette-list length.

LO/LN prove that the genuine two-context physical Hilbert GI detector
applied to x U + y W_p U has coercivity constant
  κ_p = Δ_p² / ||M_p||_F² > 0.

The present file proves using pinned mathlib and REAL Wilson objects:
  κ_p ≥ Δ_total² / (N_H² * ||M_p||_F²).
Here N_H is proved equal to Fintype.card of the ORIGINAL actual spatial
plaquette carrier, not a hypothetical or rescaled volume.

The selected plaquette and full original two interacting-posterior
boundary contexts are EXACTLY the LP witnesses; all physical sources are
Gauss-law invariant. There is NO uniform lower bound over H because
neither the total authentic Wilson GI minor nor the genuine local
Frobenius response denominator has yet been uniformly controlled.
No independent-Haar posterior, synthetic rank, Dobrushin, sorry/admit
or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- The geometric average minor lower bound squares and passes through
the TRUE positive Frobenius denominator, without any rank assumption. -/
private theorem p4Q2LQ_squared_average_over_frobenius
    (total local count frob : ℝ)
    (hcount : 0 < count) (hfrob : 0 < frob)
    (hAvg : |total| / count ≤ |local|) :
    total^2 / (count^2 * frob) ≤ local^2 / frob := by
  have hnonneg : 0 ≤ |total| / count :=
    div_nonneg (abs_nonneg _) hcount.le
  have hsq : (|total| / count)^2 ≤ |local|^2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hAvg)
      (add_nonneg (abs_nonneg local) hnonneg)]
  have hsq' : (|total| / count)^2 ≤ local^2 := by
    simpa only [sq_abs] using hsq
  have hEq : (|total| / count)^2 / frob =
      total^2 / (count^2 * frob) := by
    rw [div_pow, sq_abs, div_div_eq_div_mul]
  calc
    total^2 / (count^2 * frob) =
        (|total| / count)^2 / frob := hEq.symm
    _ ≤ local^2 / frob :=
        (div_le_div_iff_of_pos_right hfrob).2 hsq'

end GroundStatePosteriorJoint

local instance p4Q2LQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H

/-- The actual Wilson-action plaquette-list length is literally the
cardinality of the same genuine modern spatial plaquette carrier. -/
theorem p4Q2LQ_originalSpatialPlaquetteCount_eq_card :
    p4Q2LP_originalSpatialPlaquetteCount H = Fintype.card Plaq := by
  classical
  simp [p4Q2LP_originalSpatialPlaquetteCount,
    periodicHypercubicEvenSpatialSlicePlaquetteList]

/-- Explicit physical local GI Frobenius denominator positivity:
the authentic nonzero GI minor and LO coercivity force its four
original interacting-Wilson GI response squares to have positive sum. -/
theorem p4Q2LQ_originalLocalGIFrobeniusSq_pos_of_minor_ne
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    0 < p4Q2LO_originalLocalGIFrobeniusSq
      H b hb e e' z z' p := by
  have hκ :=
    (p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hminor).1
  have hFnonneg :
      0 ≤ p4Q2LO_originalLocalGIFrobeniusSq
        H b hb e e' z z' p := by
    unfold p4Q2LO_originalLocalGIFrobeniusSq
    positivity
  by_contra hnot
  have hzero :
      p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p = 0 :=
    le_antisymm (le_of_not_gt hnot) hFnonneg
  have hbad : 0 <
      (p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p)^2 /
      p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p := hκ
  rw [hzero] at hbad
  norm_num at hbad

/-- LQ's central finite-volume quantitative inequality at ANY actual
LP-selected plaquette and the SAME two genuine boundary contexts:
the true physical GI detector Frobenius coercivity coefficient has
a geometric squared-count denominator times the genuine local response
Frobenius denominator, with the ORIGINAL global GI minor numerator. -/
theorem p4Q2LQ_originalLocalGI_coercivity_ge_global_squared_floor
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq)
    (hlocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0)
    (hcount : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ))
    (hAvg :
      |p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'| /
          (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ≤
        |p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p|) :
    (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
        ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
          p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p) ≤
      p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p := by
  have hF :=
    p4Q2LQ_originalLocalGIFrobeniusSq_pos_of_minor_ne
      H b hb e e' z z' p hlocal
  change
    (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
      ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
        p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p) ≤
    (p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p)^2 /
      p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p
  exact p4Q2LQ_squared_average_over_frobenius
    (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')
    (p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p)
    (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
    (p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p)
    hcount hF hAvg

/-- Quantitative fully physical original Wilson finite-volume theorem:
for all H, beta>0, and any actual spatial links, two true interacting
Wilson boundary contexts and a genuinely local spatial plaquette exist,
with a strictly positive local detector coefficient that controls EVERY
physical Gauss-law pair x U + y W_p U, AND obeys a sharp explicit lower
bound involving the original GLOBAL GI minor, squared ACTUAL spatial
plaquette count, and the local original GI Frobenius norm.

This is not an H-uniform estimate, strong-limit closure, continuum
Yang-Mills reconstruction or a proven mass gap. -/
theorem p4Q2LQ_originalPhysicalLocalGI_exists_global_squared_floor
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
      0 < p4Q2LO_originalLocalGIFrobeniusSq H b hb.le e e' z z' p ∧
      0 < p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb.le e e' z z' p ∧
      (p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z')^2 /
          ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
            p4Q2LO_originalLocalGIFrobeniusSq H b hb.le e e' z z' p) ≤
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb.le e e' z z' p ∧
      ∀ x y : ℝ,
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb.le e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb.le
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb.le
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hb e e' left₀ right₀
  have hlocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb.le e e' z z' p ≠ 0 := by
    intro hz
    simp [hz] at hpPos
  have hF :=
    p4Q2LQ_originalLocalGIFrobeniusSq_pos_of_minor_ne
      H b hb.le e e' z z' p hlocal
  obtain ⟨hκ, hBound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb.le e e' z z' p hlocal
  have hFloor :=
    p4Q2LQ_originalLocalGI_coercivity_ge_global_squared_floor
      H b hb.le e e' z z' p hlocal hn hAvg
  exact ⟨z, z', p, hp, hn, hF, hκ, hFloor, hBound⟩

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LQ_originalSpatialPlaquetteCount_eq_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LQ_originalLocalGIFrobeniusSq_pos_of_minor_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LQ_originalLocalGI_coercivity_ge_global_squared_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LQ_originalPhysicalLocalGI_exists_global_squared_floor