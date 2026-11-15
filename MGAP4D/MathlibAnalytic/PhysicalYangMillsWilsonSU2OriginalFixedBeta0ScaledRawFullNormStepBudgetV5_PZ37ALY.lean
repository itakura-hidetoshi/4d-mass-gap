import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0RawSectorNormRatioV5_PZ37ALX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALY — scale-covariant raw/full Wilson two-volume error budget

The original genuine SU(2) Wilson P_H, its raw restriction A_H to the
full top-eigenspace orthogonal carrier K_H, and the normalized R_H are
unchanged at the ORIGINAL prescribed beta0=log(3/2)/64.

ALX proved the exact same-H identity
    ||A_H|| = ||P_H|| * ||R_H||.
The operators at H and H+1 act on DIFFERENT Hilbert spaces: we never
subtract or identify them. Scalar norms are real-valued and can be compared.

A simple unscaled difference of full raw norms is not naturally small
when a lattice volume grows. To avoid imposing that artificial feature,
introduce a separate real volume-renormalization scale s_H, selected
before comparing the two true scalar norms. Assume physical estimates
    ||A_(H+1)|| <= s_H * ||A_H|| + eta_H,
    ||P_(H+1)|| >= s_H * ||P_H|| - xi_H > 0,
    eta_H >= 0, xi_H >= 0.
The common positive baseline allows the same-volume raw/full relation
to cancel the extensive scale. The exact, NONNEGATIVE scalar cost
  t_H = (eta_H + xi_H)/(s_H*||P_H||-xi_H)
then proves
  ||R_(H+1)|| <= ||R_H|| + t_H,
  Q_(H+1) <= Q_H + (2*t_H+t_H^2), Q_H=||R_H||^2.

This is a mathematically nontrivial *conditional* two-volume bridge:
the scalar estimates on true original Wilson norms must be provided
INDEPENDENTLY. No physical size-decay of eta_H,xi_H, summable total,
fixed-beta0 all-H gap, or continuum 4D Yang-Mills mass gap is proved here.

If true model estimates produce a nonnegative total cost B<delta_0,
ALU yields a uniform positive finite-volume beta0 gap. ALV also accepts
a geometric upper budget. The s=1 case recovers the earlier additive
step comparator; introducing s does NOT silently rescale the model.

Append-only: no existing model, P/R/K, Haar/AJA, beta0, Lean/mathlib
pins, public roots, theorem statements, or workflows are changed.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace GroundStatePosteriorJoint

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "Q" => p4Q2PZ37ALV_originalFixedExcitedNormSq
local notation "D" => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
local notation "Gap" => p4Q2PZ37ALT_originalFixedGapAt
local notation "Full" => p4Q2PZ37ALX_originalFixedFullNorm
local notation "Raw" => p4Q2PZ37ALX_originalFixedRawExcitationNorm

/-- A purely real inequality allowing the SAME arbitrary positive
volume-scale factor in the physical raw and full norm comparisons.
No operator difference across nonidentical Hilbert spaces occurs. -/
theorem p4Q2PZ37ALY_generic_scaledRatio_linearStep
    (p pn r rn s eta xi t : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hpn : 0 < pn)
    (hxi : 0 ≤ xi) (ht : 0 ≤ t)
    (hRaw : pn * rn ≤ s * (p * r) + eta)
    (hFull : s * p - xi ≤ pn)
    (hCost : eta + xi ≤ t * (s * p - xi)) :
    rn ≤ r + t := by
  have hrxi : r * xi ≤ xi := by
    have h : 0 ≤ (1 - r) * xi :=
      mul_nonneg (sub_nonneg.mpr hr1) hxi
    nlinarith only [h]
  have hStep : pn * rn ≤ (r + t) * (s * p - xi) := by
    calc
      pn * rn ≤ s * (p * r) + eta := hRaw
      _ ≤ s * (p * r) + (t * (s * p - xi) - xi) := by
        linarith only [hCost]
      _ ≤ s * (p * r) + (t * (s * p - xi) - r * xi) := by
        linarith only [hrxi]
      _ = (r + t) * (s * p - xi) := by ring
  have hRight :
      (r + t) * (s * p - xi) ≤ (r + t) * pn :=
    mul_le_mul_of_nonneg_left hFull (add_nonneg hr0 ht)
  have hBound : pn * rn ≤ pn * (r + t) := by
    calc
      pn * rn ≤ (r + t) * (s * p - xi) := hStep
      _ ≤ (r + t) * pn := hRight
      _ = pn * (r + t) := by ring
  exact (mul_le_mul_iff_of_pos_left hpn).mp hBound

/-- Purely scalar conversion from a linear bound to the sharp
nonnegative squared norm loss 2t+t² when the original norm r≤1. -/
theorem p4Q2PZ37ALY_generic_scaledRatio_squaredStep
    (r rn t : ℝ)
    (hr1 : r ≤ 1) (hrn : 0 ≤ rn) (ht : 0 ≤ t)
    (hStep : rn ≤ r + t) :
    rn ^ 2 ≤ r ^ 2 + (2 * t + t ^ 2) := by
  have hMul : rn * rn ≤ (r + t) * (r + t) :=
    mul_self_le_mul_self hrn hStep
  have hCorr : 0 ≤ (1 - r) * t :=
    mul_nonneg (sub_nonneg.mpr hr1) ht
  nlinarith only [hMul, hCorr]

/-- Norm of the UNCHANGED genuine beta0 normalized full-top-orthogonal
transfer restriction. Only a scalar, not a new transfer operator. -/
noncomputable def p4Q2PZ37ALY_originalFixedExcitedNorm (H : ℕ) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖

theorem p4Q2PZ37ALY_originalFixedExcitedNorm_nonneg (H : ℕ) :
    0 ≤ p4Q2PZ37ALY_originalFixedExcitedNorm H := by
  unfold p4Q2PZ37ALY_originalFixedExcitedNorm
  exact norm_nonneg
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)

theorem p4Q2PZ37ALY_originalFixedExcitedNorm_le_one (H : ℕ) :
    p4Q2PZ37ALY_originalFixedExcitedNorm H ≤ 1 := by
  unfold p4Q2PZ37ALY_originalFixedExcitedNorm
  exact le_of_lt
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)

theorem p4Q2PZ37ALY_originalFixedExcitedNorm_sq_eq_Q (H : ℕ) :
    p4Q2PZ37ALY_originalFixedExcitedNorm H ^ 2 = Q H := by
  rfl

/-- Relative cost of raw and full operator norm perturbations around a
single chosen positive two-volume scale. Well-defined as a REAL scalar,
but its positivity requires the displayed denominator condition. -/
noncomputable def p4Q2PZ37ALY_originalFixedRelativeStepError
    (H : ℕ) (s eta xi : ℝ) : ℝ :=
  (eta + xi) / (s * Full H - xi)

theorem p4Q2PZ37ALY_originalFixedRelativeStepError_nonneg
    (H : ℕ) (s eta xi : ℝ)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * Full H - xi) :
    0 ≤ p4Q2PZ37ALY_originalFixedRelativeStepError H s eta xi := by
  unfold p4Q2PZ37ALY_originalFixedRelativeStepError
  exact div_nonneg (add_nonneg heta hxi) hden.le

/-- The ACTUAL scalar (not operator) growth in normalized excited norm
follows from paired volume-rescaled estimates on genuine raw and full
Wilson norms. The two physical estimates remain explicit hypotheses. -/
theorem p4Q2PZ37ALY_originalFixedExcitedNorm_scaledStep_le
    (H : ℕ) (s eta xi : ℝ)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * Full H - xi)
    (hRaw : Raw (H + 1) ≤ s * Raw H + eta)
    (hFull : s * Full H - xi ≤ Full (H + 1)) :
    p4Q2PZ37ALY_originalFixedExcitedNorm (H + 1) ≤
      p4Q2PZ37ALY_originalFixedExcitedNorm H +
        p4Q2PZ37ALY_originalFixedRelativeStepError H s eta xi := by
  let t := p4Q2PZ37ALY_originalFixedRelativeStepError H s eta xi
  have ht : 0 ≤ t :=
    p4Q2PZ37ALY_originalFixedRelativeStepError_nonneg H s eta xi
      heta hxi hden
  have hCostEq : t * (s * Full H - xi) = eta + xi := by
    dsimp [t, p4Q2PZ37ALY_originalFixedRelativeStepError]
    exact div_mul_cancel₀ (eta + xi) (ne_of_gt hden)
  have hRawEq : Full (H + 1) *
      p4Q2PZ37ALY_originalFixedExcitedNorm (H + 1) ≤
        s * (Full H * p4Q2PZ37ALY_originalFixedExcitedNorm H) + eta := by
    have h := hRaw
    rw [p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq (H + 1),
      p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq H] at h
    change Full (H + 1) *
      p4Q2PZ37ALY_originalFixedExcitedNorm (H + 1) ≤
        s * (Full H * p4Q2PZ37ALY_originalFixedExcitedNorm H) + eta at h
    exact h
  exact p4Q2PZ37ALY_generic_scaledRatio_linearStep
    (Full H) (Full (H + 1))
    (p4Q2PZ37ALY_originalFixedExcitedNorm H)
    (p4Q2PZ37ALY_originalFixedExcitedNorm (H + 1))
    s eta xi t
    (p4Q2PZ37ALY_originalFixedExcitedNorm_nonneg H)
    (p4Q2PZ37ALY_originalFixedExcitedNorm_le_one H)
    (p4Q2PZ37ALX_originalFixedFullNorm_pos (H + 1))
    hxi ht hRawEq hFull (le_of_eq hCostEq.symm)

/-- The NONNEGATIVE real scalar budget predicted by the paired relative
raw/full Wilson volume-step errors; no physical smallness is asserted. -/
noncomputable def p4Q2PZ37ALY_originalFixedSquaredStepBudget
    (H : ℕ) (s eta xi : ℝ) : ℝ :=
  2 * p4Q2PZ37ALY_originalFixedRelativeStepError H s eta xi +
    p4Q2PZ37ALY_originalFixedRelativeStepError H s eta xi ^ 2

theorem p4Q2PZ37ALY_originalFixedSquaredStepBudget_nonneg
    (H : ℕ) (s eta xi : ℝ)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * Full H - xi) :
    0 ≤ p4Q2PZ37ALY_originalFixedSquaredStepBudget H s eta xi := by
  have ht := p4Q2PZ37ALY_originalFixedRelativeStepError_nonneg
    H s eta xi heta hxi hden
  unfold p4Q2PZ37ALY_originalFixedSquaredStepBudget
  nlinarith only [ht, sq_nonneg
    (p4Q2PZ37ALY_originalFixedRelativeStepError H s eta xi)]

/-- The true squared excited norm on the unmodified fixed-beta0 Wilson
transfer at H+1 is bounded by the actual H norm and the explicit
relative raw/full operator-norm variation, with no cross-H subtraction. -/
theorem p4Q2PZ37ALY_originalFixedSquaredNorm_scaledStep_le
    (H : ℕ) (s eta xi : ℝ)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * Full H - xi)
    (hRaw : Raw (H + 1) ≤ s * Raw H + eta)
    (hFull : s * Full H - xi ≤ Full (H + 1)) :
    Q (H + 1) ≤ Q H +
      p4Q2PZ37ALY_originalFixedSquaredStepBudget H s eta xi := by
  let t := p4Q2PZ37ALY_originalFixedRelativeStepError H s eta xi
  have ht : 0 ≤ t :=
    p4Q2PZ37ALY_originalFixedRelativeStepError_nonneg H s eta xi
      heta hxi hden
  have hStep := p4Q2PZ37ALY_originalFixedExcitedNorm_scaledStep_le
    H s eta xi heta hxi hden hRaw hFull
  have hSq := p4Q2PZ37ALY_generic_scaledRatio_squaredStep
    (p4Q2PZ37ALY_originalFixedExcitedNorm H)
    (p4Q2PZ37ALY_originalFixedExcitedNorm (H + 1)) t
    (p4Q2PZ37ALY_originalFixedExcitedNorm_le_one H)
    (p4Q2PZ37ALY_originalFixedExcitedNorm_nonneg (H + 1))
    ht hStep
  rw [p4Q2PZ37ALY_originalFixedExcitedNorm_sq_eq_Q H,
    p4Q2PZ37ALY_originalFixedExcitedNorm_sq_eq_Q (H + 1)] at hSq
  simpa [p4Q2PZ37ALY_originalFixedSquaredStepBudget, t] using hSq

/-- Exact ALU downward loss is bounded by the true scaled raw/full
Wilson scalar comparison budget, whenever the stated hypotheses hold. -/
theorem p4Q2PZ37ALY_originalFixedLoss_le_scaledStepBudget
    (H : ℕ) (s eta xi : ℝ)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * Full H - xi)
    (hRaw : Raw (H + 1) ≤ s * Raw H + eta)
    (hFull : s * Full H - xi ≤ Full (H + 1)) :
    p4Q2PZ37ALU_originalFixedOneStepDownwardLoss H ≤
      p4Q2PZ37ALY_originalFixedSquaredStepBudget H s eta xi := by
  exact p4Q2PZ37ALV_oneStepLoss_le_of_normSqIncrease H
    (p4Q2PZ37ALY_originalFixedSquaredStepBudget H s eta xi)
    (p4Q2PZ37ALY_originalFixedSquaredStepBudget_nonneg
      H s eta xi heta hxi hden)
    (p4Q2PZ37ALY_originalFixedSquaredNorm_scaledStep_le
      H s eta xi heta hxi hden hRaw hFull)

/-- A summable sequence of REAL relative error costs derived from
independent genuine Wilson two-volume raw/full norm estimates suffices
for a strictly positive all-finite-volume original-beta0 transfer gap.
NO such independent physical estimates are established here. -/
theorem p4Q2PZ37ALY_uniformGap_of_scaledRawFullErrorBudget
    (s eta xi : ℕ → ℝ) (B : ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1))
    (htotal : ∀ H : ℕ,
      (Finset.range H).sum
        (fun i : ℕ => p4Q2PZ37ALY_originalFixedSquaredStepBudget
          i (s i) (eta i) (xi i)) ≤ B)
    (hstrict : B < D 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  let b : ℕ → ℝ := fun i =>
    p4Q2PZ37ALY_originalFixedSquaredStepBudget i (s i) (eta i) (xi i)
  have hb : ∀ H : ℕ, 0 ≤ b H := by
    intro H
    exact p4Q2PZ37ALY_originalFixedSquaredStepBudget_nonneg
      H (s H) (eta H) (xi H) (heta H) (hxi H) (hden H)
  have hstep : ∀ H : ℕ, D H ≤ D (H + 1) + b H := by
    intro H
    have hq := p4Q2PZ37ALY_originalFixedSquaredNorm_scaledStep_le
      H (s H) (eta H) (xi H) (heta H) (hxi H)
      (hden H) (hRaw H) (hFull H)
    rw [p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq H,
      p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq (H + 1)]
    dsimp [b]
    linarith
  have hsums : ∀ H : ℕ, (Finset.range H).sum b ≤ B := by
    intro H
    simpa [b] using htotal H
  exact p4Q2PZ37ALU_originalFixedUniformGap_of_stepwiseBudget
    b B hb hstep hsums hstrict

/-- A geometric MAJORANT of the physically derived squared error
cost also suffices. The true Wilson mixing/decay majorant is STILL
a separate unproved physical premise. -/
theorem p4Q2PZ37ALY_uniformGap_of_scaledRawFullGeometricBudget
    (s eta xi : ℕ → ℝ) (C rho : ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1))
    (hC : 0 ≤ C) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hSmall : C < (1 - rho) * D 0)
    (hGeom : ∀ H : ℕ,
      p4Q2PZ37ALY_originalFixedSquaredStepBudget
        H (s H) (eta H) (xi H) ≤ C * rho ^ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  apply p4Q2PZ37ALV_uniformGap_of_global_geometricNormSqStep
    C rho hC hrho0 hrho1 hSmall
  intro H
  have hq := p4Q2PZ37ALY_originalFixedSquaredNorm_scaledStep_le
    H (s H) (eta H) (xi H) (heta H) (hxi H)
    (hden H) (hRaw H) (hFull H)
  have hc := hGeom H
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_generic_scaledRatio_linearStep
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_generic_scaledRatio_squaredStep
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedExcitedNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedExcitedNorm_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedExcitedNorm_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedExcitedNorm_sq_eq_Q
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedRelativeStepError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedRelativeStepError_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedExcitedNorm_scaledStep_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedSquaredStepBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedSquaredStepBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedSquaredNorm_scaledStep_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_originalFixedLoss_le_scaledStepBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_uniformGap_of_scaledRawFullErrorBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALY_uniformGap_of_scaledRawFullGeometricBudget
