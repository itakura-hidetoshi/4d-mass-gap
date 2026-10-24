import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalThreeCrossingWardV5_PY3C
import Mathlib.Tactic

/-!
# P4-Q2-PY4 — authentic two-slab Wilson fourth moment inner-Haar split

The original SU(2) two-slab action is EXACTLY
  Q(X,A,B)=S(X,A)+S(A,B),
with the complete middle spatial slice Wilson contribution retained.
The full original fourth power under the INNER spatial Haar is
  ∫ Q^4(X,A,B) dμ(X)
    = u(A)-4 S(A,B)c(A)+6 S(A,B)^2 b(A)
      -4 S(A,B)^3 a(A)+S(A,B)^4.

Here a=-∫S, b=∫S², c=-∫S³ and u=∫S⁴ are genuine original
one-slab action Haar moments, not independent posterior replacements.
This step is a direct quartic analogue of PR's proved cubic expansion.
No rank claim, new axiom, sorry, admit, or spectral surrogate.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY4_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY4_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY4_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY4_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY4_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalQuarticActionHaarSplit
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H

/-- Exact quartic binomial integral under the ORIGINAL normalized
spatial SU(2) Haar; the constant term integrates with mass one. -/
private theorem p4Q2PY4_shiftedQuartic_integral
    (f : Cfg → ℝ) (hf : Continuous f) (w : ℝ) :
    (∫ X : Cfg, (f X + w) ^ 4 ∂haar) =
      (∫ X : Cfg, f X ^ 4 ∂haar) +
      4 * w * (∫ X : Cfg, f X ^ 3 ∂haar) +
      6 * w ^ 2 * (∫ X : Cfg, f X ^ 2 ∂haar) +
      4 * w ^ 3 * (∫ X : Cfg, f X ∂haar) + w ^ 4 := by
  have h1 : Integrable f haar :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun X : Cfg => f X ^ 2) haar :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h3 : Integrable (fun X : Cfg => f X ^ 3) haar :=
    (hf.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h4 : Integrable (fun X : Cfg => f X ^ 4) haar :=
    (hf.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLeft : Integrable (fun X : Cfg =>
      f X ^ 4 + (4 * w) * f X ^ 3) haar :=
    h4.add (h3.const_mul _)
  have hRight : Integrable (fun X : Cfg =>
      (6 * w ^ 2) * f X ^ 2 + (4 * w ^ 3) * f X) haar :=
    (h2.const_mul _).add (h1.const_mul _)
  have hPair : Integrable (fun X : Cfg =>
      (f X ^ 4 + (4 * w) * f X ^ 3) +
      ((6 * w ^ 2) * f X ^ 2 + (4 * w ^ 3) * f X)) haar :=
    hLeft.add hRight
  calc
    (∫ X : Cfg, (f X + w) ^ 4 ∂haar) =
        ∫ X : Cfg,
          ((f X ^ 4 + (4 * w) * f X ^ 3) +
            ((6 * w ^ 2) * f X ^ 2 + (4 * w ^ 3) * f X)) + w ^ 4 ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      ring
    _ = ((∫ X : Cfg, f X ^ 4 ∂haar) +
          4 * w * (∫ X : Cfg, f X ^ 3 ∂haar)) +
        (6 * w ^ 2 * (∫ X : Cfg, f X ^ 2 ∂haar) +
          4 * w ^ 3 * (∫ X : Cfg, f X ∂haar)) + w ^ 4 := by
      rw [integral_add hPair (integrable_const _)]
      rw [integral_add hLeft hRight]
      rw [integral_add h4 (h3.const_mul _)]
      rw [integral_add (h2.const_mul _) (h1.const_mul _)]
      simp only [integral_const_mul]
      simp
    _ = _ := by ring

/-- Unmodified physical one-slab full SU(2) Wilson action is
continuous in its original Haar source configuration. -/
private theorem p4Q2PY4_oneSlabAction_row_continuous (A : Cfg) :
    Continuous (fun X : Cfg => S X A) := by
  have hPair : Continuous (fun X : Cfg => (X, A)) :=
    continuous_id.prodMk continuous_const
  have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using h

/-- Authentic interacting two-slab Wilson fourth moment, after
the original INNER Haar only. The fourth action contribution u(A)
and ALL middle spatial-plaquette effects survive. -/
theorem p4Q2PY4_originalTwoSlabInnerQuartic_expansion
    (A B : Cfg) :
    (∫ X : Cfg, (Q X A B) ^ 4 ∂haar) =
      u A - 4 * S A B * c A +
      6 * (S A B) ^ 2 * b A -
      4 * (S A B) ^ 3 * a A + (S A B) ^ 4 := by
  have h := p4Q2PY4_shiftedQuartic_integral H
    (fun X : Cfg => S X A)
    (p4Q2PY4_oneSlabAction_row_continuous H A) (S A B)
  change (∫ X : Cfg, (S X A + S A B) ^ 4 ∂haar) = _
  rw [h]
  unfold p4Q2PX_originalOneSlabFourthActionMoment
    p4Q2PP2_originalOneSlabThirdActionMoment
    p4Q2PK_originalOneSlabSecondActionMoment
    p4Q2PK_originalOneSlabFirstActionMoment
  ring

end OriginalQuarticActionHaarSplit
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY4_originalTwoSlabInnerQuartic_expansion
