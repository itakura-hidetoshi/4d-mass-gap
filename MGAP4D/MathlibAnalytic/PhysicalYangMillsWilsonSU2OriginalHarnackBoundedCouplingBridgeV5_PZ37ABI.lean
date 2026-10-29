import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPairHaarSignedTailCertificateV5_PZ37ABH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABI — derive the original Wilson Harnack coefficient ceiling
# from a genuine bounded-above positive coupling schedule

LW's actual transfer-compensated physical response scale is
  E_b = exp(8*b) * (exp(16*b) - exp(-16*b)).
It is increasing for nonnegative b. We prove with pinned real
exponential monotonicity that 0 <= b <= B implies E_b <= E_B,
with no independent assumed scale envelope. We then specialize ABG/ABH's
true original pair-Haar GI lower bound to every genuine volume at
0 < b(H) <= B, preserving the actual volume-varying transfer t.

The sole remaining independent all-volume inputs in the combined
criterion are the ORIGINAL Wilson event mass and compensated
physical full/local GI amplitude versus its ENTIRE negative signed
pair-Haar tail. Their required uniform values are NOT constructed here.

No synthetic independent Haar posterior, altered Perron/source,
Dobrushin, normalization t=1, new axioms, sorry/admit/native_decide,
all-physical-Hilbert coercivity, common fine interval, E/F, H1-H4,
OS/Wightman, or continuum 4D Yang-Mills mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Actual original Wilson contrast scale E_b is monotone for
nonnegative coupling. No volume H or true-transfer approximation
occurs in the original LW definition. -/
theorem p4Q2PZ37ABI_originalHarnackContrastScale_mono
    (b B : ℝ) (hb : 0 ≤ b) (hBound : b ≤ B) :
    p4Q2LW_originalHarnackContrastScale b ≤
      p4Q2LW_originalHarnackContrastScale B := by
  have hE8 :
      Real.exp (8 * b) ≤ Real.exp (8 * B) :=
    Real.exp_le_exp.mpr (by linarith)
  have hE16 :
      Real.exp (16 * b) ≤ Real.exp (16 * B) :=
    Real.exp_le_exp.mpr (by linarith)
  have hEMinus16 :
      Real.exp (-16 * B) ≤ Real.exp (-16 * b) :=
    Real.exp_le_exp.mpr (by linarith)
  have hCNonneg :
      0 ≤ Real.exp (16 * b) - Real.exp (-16 * b) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_exp.mpr (by linarith)
  have hCLe :
      Real.exp (16 * b) - Real.exp (-16 * b) ≤
        Real.exp (16 * B) - Real.exp (-16 * B) := by
    linarith
  change
    Real.exp (8 * b) *
        (Real.exp (16 * b) - Real.exp (-16 * b)) ≤
      Real.exp (8 * B) *
        (Real.exp (16 * B) - Real.exp (-16 * B))
  calc
    Real.exp (8 * b) * (Real.exp (16 * b) - Real.exp (-16 * b)) ≤
        Real.exp (8 * B) * (Real.exp (16 * b) - Real.exp (-16 * b)) :=
      mul_le_mul_of_nonneg_right hE8 hCNonneg
    _ ≤ Real.exp (8 * B) *
          (Real.exp (16 * B) - Real.exp (-16 * B)) :=
      mul_le_mul_of_nonneg_left hCLe (Real.exp_pos _).le

/-- The abstract ABH coupling-scale hypothesis is automatically
satisfied in the genuine ORIGINAL Wilson theory when 0<b(H)<=B.
The all-volume physically transferred genuine K lower witness is
STILL a separate input and is not inferred from finite-H K>0. -/
theorem p4Q2PZ37ABI_allVolumes_fullGIfloor_of_trueCross_boundedCoupling
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ H, b H ≤ B)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hCross : ∀ H,
      ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
        kappa ≤ p4Q2LW_originalPhysicalTransferNorm H (b H) (hb H).le *
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
            H (b H) (hb H) e p) :
    0 < kappa^2 /
        (p4Q2LW_originalHarnackContrastScale B / 2)^2 ∧
    ∀ H, ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (_p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      kappa^2 / (p4Q2LW_originalHarnackContrastScale B / 2)^2 ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
          H (b H) (hb H) e := by
  have hEmax : 0 < p4Q2LW_originalHarnackContrastScale B :=
    p4Q2LW_originalHarnackContrastScale_pos B hB
  have hScale : ∀ H,
      p4Q2LW_originalHarnackContrastScale (b H) ≤
        p4Q2LW_originalHarnackContrastScale B := by
    intro H
    exact p4Q2PZ37ABI_originalHarnackContrastScale_mono
      (b H) B (hb H).le (hBound H)
  exact p4Q2PZ37ABH_allVolumes_fullGIfloor_of_trueCross_and_scaleCap
    b hb kappa (p4Q2LW_originalHarnackContrastScale B)
    hkappa hEmax hScale hCross

/-- A single noncircular ORIGINAL-Wilson event/tail witness criterion
at a bounded positive coupling schedule; combines ABH with the
model-derived E_B scale without an independent Harnack hypothesis.
Existence of the H-uniform event/tail witnesses is explicitly OPEN. -/
theorem p4Q2PZ37ABI_allVolumes_fullGIfloor_of_eventsAndTail_boundedCoupling
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ H, b H ≤ B)
    (rho delta eta : ℝ) (hdelta : 0 ≤ delta)
    (hMargin : 0 < rho * delta - eta)
    (hWitness : ∀ H,
      ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
        (E : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)),
        MeasurableSet E ∧
        rho ≤
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).real E ∧
        (∀ z ∈ E,
          delta ≤ p4Q2PZ37ABH_originalCompensatedSignedCrossDensity
            H (b H) (hb H) e p z) ∧
        (∫ z, max
          (-p4Q2PZ37ABH_originalCompensatedSignedCrossDensity
            H (b H) (hb H) e p z) 0
          ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) ≤
            eta) :
    0 < (rho * delta - eta)^2 /
        (p4Q2LW_originalHarnackContrastScale B / 2)^2 ∧
    ∀ H, ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (_p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      (rho * delta - eta)^2 /
        (p4Q2LW_originalHarnackContrastScale B / 2)^2 ≤
          p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
            H (b H) (hb H) e := by
  have hCross : ∀ H,
      ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
        rho * delta - eta ≤
          p4Q2LW_originalPhysicalTransferNorm H (b H) (hb H).le *
            p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
              H (b H) (hb H) e p := by
    exact p4Q2PZ37ABH_allVolumes_uniformTrueCross_of_eventsAndSignedTail
      b hb rho delta eta (rho * delta - eta) hdelta (le_refl _) hWitness
  exact p4Q2PZ37ABI_allVolumes_fullGIfloor_of_trueCross_boundedCoupling
    b hb B hB hBound (rho * delta - eta) hMargin hCross

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABI_originalHarnackContrastScale_mono
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABI_allVolumes_fullGIfloor_of_trueCross_boundedCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABI_allVolumes_fullGIfloor_of_eventsAndTail_boundedCoupling
