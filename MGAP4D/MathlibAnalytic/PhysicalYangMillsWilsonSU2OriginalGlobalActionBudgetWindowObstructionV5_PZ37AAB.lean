import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPlaquetteOverlapBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAB — actual Wilson global-budget window obstruction

The original SU(2) one-slab global action budget is literally
  B_H = 2 (number of actual spatial plaquettes + spatial links).
The existing PZ37ZA injective original spatial-plaquette family proves
  number of actual spatial plaquettes >= 2(H+1).
Therefore B_H >= 4(H+1), and the ORIGINAL crude global action budget
is unbounded as the finite periodic spatial volume grows.

For EVERY positive fine interval (0,rho), one finds a genuine finite
volume H and positive fine t<rho for which B_H*t > 1/4.
Consequently, the ZV/AAA sufficient perturbative smallness assumption
B_H*t<=1/4 CANNOT have a single all-volume positive-fine interval.

This is a NO-GO only for this volume-extensive GLOBAL-ACTION-BUDGET
perturbation gate, not a no-go for the true physical Wilson GL Rayleigh
floor, centered-source-local error, gauge-locality based estimates,
endpoint E/F, H1-H4, or continuum Yang-Mills gap.
No new axiom, sorry/admit/native_decide or surrogate posterior/source.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- This is a lower bound for the ACTUAL original Wilson one-slab
action-budget count, from ZA's genuine injective plaquette family. -/
theorem p4Q2PZ37AAB_originalGlobalActionBudget_ge_four_sideParameter
    (H : ℕ) :
    (4 : ℝ) * ((H+1 : ℕ) : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
  classical
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    change 2 * (H+1) ≠ 0
    omega⟩
  have hPlaquetteCount :=
    pz37zaOriginalSpatialPlaquetteCount_ge_sideLength H
  rw [GroundStatePosteriorJoint.p4Q2LQ_originalSpatialPlaquetteCount_eq_card]
    at hPlaquetteCount
  have hList :
      (periodicHypercubicEvenSpatialSlicePlaquetteList H).length =
        Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
    simp [periodicHypercubicEvenSpatialSlicePlaquetteList]
  have hPlaq :
      2 * (H+1) ≤
        (periodicHypercubicEvenSpatialSlicePlaquetteList H).length := by
    simpa only [hList] using hPlaquetteCount
  have hReal :
      (2 : ℝ) * ((H+1 : ℕ) : ℝ) ≤
        ((periodicHypercubicEvenSpatialSlicePlaquetteList H).length : ℝ) := by
    exact_mod_cast hPlaq
  have hLink :
      0 ≤ ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) :=
    Nat.cast_nonneg _
  dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume]
  push_cast
  linarith

/-- The true original Wilson one-slab GLOBAL budget is unbounded.
No arbitrary volume proxy is used: both counts are canonical lists. -/
theorem p4Q2PZ37AAB_originalGlobalActionBudget_unbounded :
    ∀ K : ℝ, ∃ H : ℕ, K <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
  intro K
  obtain ⟨H, hH⟩ := exists_nat_gt K
  refine ⟨H, ?_⟩
  have hBudget :=
    p4Q2PZ37AAB_originalGlobalActionBudget_ge_four_sideParameter H
  have hH' :
      (H : ℝ) ≤ (4 : ℝ) * ((H+1 : ℕ) : ℝ) := by
    push_cast
    have hn : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
    nlinarith
  exact lt_of_lt_of_le hH (hH'.trans hBudget)

/-- Every positive-fine interval contains a TRUE Wilson finite
volume beyond the original GLOBAL budget-controlled smallness gate. -/
theorem p4Q2PZ37AAB_everyPositiveFineWindow_exits_globalBudgetGate
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (H : ℕ) (t : Set.Ici (0 : ℝ)),
      0 < (t : ℝ) ∧ (t : ℝ) < ρ ∧
      (1/4 : ℝ) <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          (t : ℝ) := by
  obtain ⟨H, hLarge⟩ :=
    p4Q2PZ37AAB_originalGlobalActionBudget_unbounded (1/ρ)
  let t : Set.Ici (0 : ℝ) := ⟨ρ/2, le_of_lt (half_pos hρ)⟩
  refine ⟨H, t, half_pos hρ, half_lt_self hρ, ?_⟩
  have hMul :
      (1/ρ)*ρ <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * ρ :=
    mul_lt_mul_of_pos_right hLarge hρ
  have hOne : (1/ρ)*ρ = 1 := by
    field_simp [ne_of_gt hρ]
  rw [hOne] at hMul
  change (1/4 : ℝ) <
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * (ρ/2)
  nlinarith only [hMul]

/-- In particular, the original GLOBAL-B_H perturbation criterion
cannot be imposed for ALL volumes on ANY common positive-fine interval.
This does NOT disprove the physical Rayleigh or mass gap itself. -/
theorem p4Q2PZ37AAB_no_allVolume_positiveFine_globalBudgetWindow :
    ¬ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (H : ℕ) (t : Set.Ici (0 : ℝ)),
        0 < (t : ℝ) → (t : ℝ) < ρ →
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          (t : ℝ) ≤ (1/4 : ℝ) := by
  rintro ⟨ρ, hρ, hSmall⟩
  obtain ⟨H, t, ht, htρ, hOut⟩ :=
    p4Q2PZ37AAB_everyPositiveFineWindow_exits_globalBudgetGate ρ hρ
  exact (not_lt_of_ge (hSmall H t ht htρ)) hOut

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AAB_originalGlobalActionBudget_ge_four_sideParameter
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AAB_originalGlobalActionBudget_unbounded
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AAB_everyPositiveFineWindow_exits_globalBudgetGate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AAB_no_allVolume_positiveFine_globalBudgetWindow
