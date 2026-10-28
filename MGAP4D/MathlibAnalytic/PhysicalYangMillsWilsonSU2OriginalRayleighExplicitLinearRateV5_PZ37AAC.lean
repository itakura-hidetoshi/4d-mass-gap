import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTangentExplicitVolumeRateV5_PZ37AAA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAC — explicit linear fine-rate for TRUE physical Wilson GL Rayleigh

From the genuine PZ37AAA normalized Gauss-law physical tangent,
  ||F_(H,t)/t - V_H|| <= A_H t   for t>0 and B_H t<=1/4,
and the original PZ37ZZ full-link, complete pair-Haar, TWO interacting
posterior positive GL Rayleigh continuity, obtain the quantitative
physical-source-normalized convergence estimate

 |R_(H,b)(F_(H,t)) - R_(H,b)(V_H)|
      <= [5 C_(H,b) A_H / ||V_H||] t

under A_H t <= ||V_H||/2. C_(H,b) is the ORIGINAL physical GL
Rayleigh cap from all genuine links, not an invented coefficient
Gram or posterior. The original ZW3 represented sources retain the
same Gauss-law Hilbert metric.

Moreover a TRUE centered Wilson Gram floor c*||V_H||²<=G_(H,b)(V_H),
combined with the explicit smallness of the right-hand side, implies
R_(H,b)(F_(H,t))>=c/2.

These results are FINITE-H and have no unproved all-volume or
scale-uniform positive fine interval. The original global action
budget is extensive and the AAB obstruction is preserved. No new
axioms, sorry, admit, native_decide, modified Wilson posterior,
endpoint E/F, H1-H4, or continuum Yang-Mills gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAC_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuine continuous-represented physical Wilson center has
exactly its original Gauss-law Hilbert source norm, with no change
of carrier or artificial coefficient weighting. -/
theorem p4Q2PZ37AAC_originalCenteredLift_norm_eq_physical
    (H : ℕ) :
    ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ =
      ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖ := by
  rfl

/-- Genuine Wilson physical tangent error in the ZZZ represented source
carrier is controlled by the literal AAA action-budget first variation.
This is a quantitative bound on the ACTUAL full physical vector. -/
theorem p4Q2PZ37AAC_originalRepresentedTangentDisplacement_le_rate
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (hBudget :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ) ≤ (1/4 : ℝ)) :
    p4Q2PZ37ZZ_originalTangentDisplacement H t ≤
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H * (t : ℝ) := by
  change ‖p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H t -
      p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖ ≤
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H * (t : ℝ)
  exact p4Q2PZ37AAA_originalPhysicalTangent_error_le_linear H t ht hBudget

/-- Explicit fixed-H Rayleigh modulus from genuine original
two-Wilson-posterior full-link GL cap and normalized-tangent rate.
The denominator is the true physical Wilson Hilbert norm. -/
noncomputable def p4Q2PZ37AAC_originalPhysicalRayleighLinearRate
    (H : ℕ) (b : ℝ) : ℝ :=
  (5 * p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
       p4Q2PZ37AAA_originalPhysicalTangentRateBudget H) /
    ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖

/-- Explicit true physical Rayleigh error: O_(H,b)(t) with a LITERAL,
finite-volume-dependent Wilson action and integrated-posterior GL
constant. No global/continuum uniformity is inferred. -/
theorem p4Q2PZ37AAC_originalPositiveFine_RayleighError_le_linear
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (hBudget :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ) ≤ (1/4 : ℝ))
    (hNear :
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H * (t : ℝ) ≤
        ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ / 2) :
    |p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZE_originalPhysicalCancellation H t) -
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)| ≤
        p4Q2PZ37AAC_originalPhysicalRayleighLinearRate H b * (t : ℝ) := by
  let C : ℝ := p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b
  let A : ℝ := p4Q2PZ37AAA_originalPhysicalTangentRateBudget H
  let N : ℝ := ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖
  let D : ℝ := p4Q2PZ37ZZ_originalTangentDisplacement H t
  have hC : 0 ≤ C := by
    dsimp [C, p4Q2PZ37ZG_originalFullLinkGL_RayleighCap]
    positivity
  have hN : 0 < N := by
    change 0 < ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖
    apply norm_pos_iff.mpr
    intro hv
    apply p4Q2PZ37ZW_originalCenteredDirection_ne_zero H
    have hh := congrArg (fun z :
      p4Q2PZ37ZW2_originalContinuousPhysicalSources H =>
      (z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) hv
    simpa only [p4Q2PZ37ZW3_originalCenteredPhysicalLift, Submodule.coe_zero]
      using hh
  have hDelta : D ≤ A * (t : ℝ) :=
    p4Q2PZ37AAC_originalRepresentedTangentDisplacement_le_rate
      H t ht hBudget
  have hClose : D ≤ N / 2 := hDelta.trans hNear
  have hBase :=
    p4Q2PZ37ZZ_originalPositiveFine_RayleighError_le
      H b hb t ht hClose
  change
    |p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZE_originalPhysicalCancellation H t) -
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)| ≤
      ((5*C*A)/N) * (t : ℝ)
  calc
    |p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZE_originalPhysicalCancellation H t) -
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)| ≤
        (5*C*D)/N := hBase
    _ ≤ (5*C*(A*(t : ℝ)))/N := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact mul_le_mul_of_nonneg_left hDelta (by positivity)
    _ = ((5*C*A)/N)*(t : ℝ) := by ring

/-- A TRUE finite-H original two-mode Wilson Gram floor produces a
positive physical Rayleigh lower bound at fine t, with the explicitly
calculated original normalized physical tangent convergence rate.
All smallness conditions here are volume-indexed and must be proved. -/
theorem p4Q2PZ37AAC_originalPositiveFine_Rayleigh_ge_halfGramFloor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (c : ℝ) (hc : 0 < c)
    (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (hBudget :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ) ≤ (1/4 : ℝ))
    (hGram :
      c * ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H b hb)
    (hNear :
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H * (t : ℝ) ≤
        ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ / 2)
    (hRate :
      p4Q2PZ37AAC_originalPhysicalRayleighLinearRate H b * (t : ℝ) ≤ c/2) :
    0 < c/2 ∧ c/2 ≤
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  refine ⟨half_pos hc, ?_⟩
  have hNorm :
      0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
    pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
  have hLimit : c ≤
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) := by
    rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
    exact (le_div_iff₀ hNorm).mpr hGram
  have hError :=
    p4Q2PZ37AAC_originalPositiveFine_RayleighError_le_linear
      H b hb t ht hBudget hNear
  have hDifference := (abs_le.mp (hError.trans hRate)).1
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAC_originalCenteredLift_norm_eq_physical
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAC_originalRepresentedTangentDisplacement_le_rate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAC_originalPositiveFine_RayleighError_le_linear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAC_originalPositiveFine_Rayleigh_ge_halfGramFloor
