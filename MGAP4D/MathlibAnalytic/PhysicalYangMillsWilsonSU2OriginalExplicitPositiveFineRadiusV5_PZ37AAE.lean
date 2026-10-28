import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRayleighExplicitLinearRateV5_PZ37AAC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTangentBudgetVolumeGrowthV5_PZ37AAD
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAE — explicit genuine Wilson positive-fine Rayleigh radius

AAC's original physical-Gauss-law Rayleigh bound and the original
two-interacting-Wilson-posterior full-link/full-boundary-Haar GL Gram
give the following explicit finite-H fine interval, with NO compactness
choice or imported rate premise.

For B_H = literal original global one-slab Wilson action budget,
A_H = AAA's explicitly constructed true normalized physical tangent
upper rate, K_(H,b) = AAC's literal original integrated-posterior GL
Rayleigh linear rate, N_H = ||V_H|| in the ORIGINAL physical Hilbert,
and any *actually proved* centered original Gram floor c>0, define

 rho_(H,b,c) = min {1/[4(B_H+1)], N_H/[2(A_H+1)], c/[2(K_(H,b)+1)]}.

Then rho_(H,b,c)>0 and for every genuine fine 0<t<rho,
  B_H*t <= 1/4, A_H*t <= N_H/2, K_(H,b)*t <= c/2,
so the unchanged original physical Rayleigh satisfies
  R_(H,b)(F_t) >= c/2 > 0.

The radius is explicit, ORIGINAL and finite-H. It is NOT a shared
all-volume radius. AAB/AAD show why globally assembled budgets
are intrinsically volume-dependent; no surrogate posterior, new
axiom, sorry/admit/native_decide, E/F, H1-H4 or continuum gap.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Elementary *numerical* finite-radius gate with honest positive
denominators. Reusable independently of any particular presentation. -/
noncomputable def p4Q2PZ37AAE_basicPositiveFineRadius
    (B A K N c : ℝ) : ℝ :=
  min (1 / (4 * (B+1))) (min (N / (2*(A+1))) (c / (2*(K+1))))

/-- A single explicit positive number enforces all THREE independent
genuine smallness inequalities, with no arbitrary eventual filters. -/
theorem p4Q2PZ37AAE_basicPositiveFineRadius_controls
    (B A K N c : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hN : 0 < N) (hc : 0 < c) :
    0 < p4Q2PZ37AAE_basicPositiveFineRadius B A K N c ∧
      ∀ t : ℝ, 0 < t →
        t < p4Q2PZ37AAE_basicPositiveFineRadius B A K N c →
        B*t ≤ 1/4 ∧ A*t ≤ N/2 ∧ K*t ≤ c/2 := by
  let rB : ℝ := 1 / (4 * (B+1))
  let rA : ℝ := N / (2 * (A+1))
  let rK : ℝ := c / (2 * (K+1))
  have hBden : 0 < 4*(B+1) := by positivity
  have hAden : 0 < 2*(A+1) := by positivity
  have hKden : 0 < 2*(K+1) := by positivity
  have hrB : 0 < rB := div_pos (by norm_num) hBden
  have hrA : 0 < rA := div_pos hN hAden
  have hrK : 0 < rK := div_pos hc hKden
  change 0 < min rB (min rA rK) ∧
    ∀ t : ℝ, 0 < t → t < min rB (min rA rK) →
      B*t ≤ 1/4 ∧ A*t ≤ N/2 ∧ K*t ≤ c/2
  refine ⟨lt_min hrB (lt_min hrA hrK), ?_⟩
  intro t ht hδ
  have htB : t < rB :=
    lt_of_lt_of_le hδ (min_le_left _ _)
  have htA : t < rA := by
    exact lt_of_lt_of_le
      (lt_of_lt_of_le hδ (min_le_right _ _)) (min_le_left _ _)
  have htK : t < rK := by
    exact lt_of_lt_of_le
      (lt_of_lt_of_le hδ (min_le_right _ _)) (min_le_right _ _)
  have hBudgetProd : t * (4*(B+1)) < 1 := by
    exact (lt_div_iff₀ hBden).mp htB
  have hTangentProd : t * (2*(A+1)) < N := by
    exact (lt_div_iff₀ hAden).mp htA
  have hRayleighProd : t * (2*(K+1)) < c := by
    exact (lt_div_iff₀ hKden).mp htK
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

local instance p4Q2PZ37AAE_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAE_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAE_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAE_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAE_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAE_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Literal explicit positive fine-radius certificate built entirely
from existing original Wilson/action/posterior/physical-Hilbert data. -/
noncomputable def p4Q2PZ37AAE_originalCertifiedPositiveFineRadius
    (H : ℕ) (b c : ℝ) : ℝ :=
  p4Q2PZ37AAE_basicPositiveFineRadius
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)
    (p4Q2PZ37AAA_originalPhysicalTangentRateBudget H)
    (p4Q2PZ37AAC_originalPhysicalRayleighLinearRate H b)
    ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ c

/-- Every *actual* original finite-volume centered Wilson Gram floor
c>0 has a numerically specified, strictly positive fine interval
carrying the original full-link physical Rayleigh floor c/2.
No volume-independent choice, posterior replacement, or hidden
uniform convergence premise is made. -/
theorem p4Q2PZ37AAE_originalCertifiedRadius_positiveRayleighFloor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (c : ℝ) (hc : 0 < c)
    (hGram :
      c * ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H b hb) :
    0 < p4Q2PZ37AAE_originalCertifiedPositiveFineRadius H b c ∧
    ∀ t : Set.Ici (0 : ℝ),
      0 < (t : ℝ) →
      (t : ℝ) < p4Q2PZ37AAE_originalCertifiedPositiveFineRadius H b c →
      0 < c/2 ∧ c/2 ≤
        p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
          (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let A : ℝ := p4Q2PZ37AAA_originalPhysicalTangentRateBudget H
  let K : ℝ := p4Q2PZ37AAC_originalPhysicalRayleighLinearRate H b
  let N : ℝ := ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hA : 0 ≤ A := by
    have hLower : 20 * B^2 ≤ A :=
      p4Q2PZ37AAD_originalTangentErrorBudget_ge_twenty_actionBudget_sq H
    exact (by positivity : 0 ≤ 20*B^2).trans hLower
  have hN : 0 < N := by
    change 0 < ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖
    rw [p4Q2PZ37AAC_originalCenteredLift_norm_eq_physical]
    exact norm_pos_iff.mpr (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)
  have hK : 0 ≤ K := by
    change 0 ≤
      (5 * p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
        p4Q2PZ37AAA_originalPhysicalTangentRateBudget H) /
        ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖
    have hC : 0 ≤ p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b := by
      dsimp [p4Q2PZ37ZG_originalFullLinkGL_RayleighCap]
      positivity
    positivity
  have hNumeric :=
    p4Q2PZ37AAE_basicPositiveFineRadius_controls B A K N c
      hB hA hK hN hc
  change 0 < p4Q2PZ37AAE_basicPositiveFineRadius B A K N c ∧
    ∀ t : Set.Ici (0 : ℝ), 0 < (t : ℝ) →
      (t : ℝ) < p4Q2PZ37AAE_basicPositiveFineRadius B A K N c →
      0 < c/2 ∧ c/2 ≤
        p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
          (p4Q2PZ37ZE_originalPhysicalCancellation H t)
  refine ⟨hNumeric.1, ?_⟩
  intro t ht hδ
  obtain ⟨hBudget, hNear, hRate⟩ :=
    hNumeric.2 (t : ℝ) ht hδ
  exact p4Q2PZ37AAC_originalPositiveFine_Rayleigh_ge_halfGramFloor
    H b hb c hc t ht hBudget hGram hNear hRate

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AAE_basicPositiveFineRadius_controls
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAE_originalCertifiedRadius_positiveRayleighFloor
