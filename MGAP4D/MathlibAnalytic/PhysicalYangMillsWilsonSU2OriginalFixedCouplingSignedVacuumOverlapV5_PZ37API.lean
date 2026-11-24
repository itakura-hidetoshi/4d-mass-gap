import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalVacuumRelativeFirstSlopeV5_PZ37APD
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSignedMixedKernelRowLowerV5_PZ37APH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingCertificateV5_PZ37ADC
import Mathlib.Tactic

/-!
# P4-Q2-PZ37API — signed original physical overlap at fixed coupling

STAGED ONLY. Requires certified APH on Formal. The sign-sensitive row estimate
is transported through the actual Haar integral representatives to the real
physical L2 inner product with the genuine nonnegative top eigenvector.
The operator norm cancels via symmetry and the true eigenvalue equation.
The existing positive fixed coupling from ADC lies in the APH interval.
No volume-independent positive constant-mode amplitude, full-sector contraction
or continuum conclusion is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "P" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
local notation "Rep" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
local notation "Tr" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
local notation "C" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
local notation "V" => p4Q2PZ37AMU_actualPhysicalGaussMode
local notation "Vac" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy

local instance p4Q2PZ37API_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37API_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37API_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37API_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37API_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37API_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37API_firstRep
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (A : Cfg H 2) :
    Rep H 2 beta ((V H 1 : P H 2) : Lp ℝ 2 (Mu H 2)) A =
      (-2 : ℝ) * (∫ B, K H 2 beta A B * Chi (Hol H 2 B) ∂(Mu H 2)) := by
  let mu := Mu H 2
  let v : Lp ℝ 2 mu := ((V H 1 : P H 2) : Lp ℝ 2 mu)
  have hMode : v =ᵐ[mu] (fun B => (-2 : ℝ) * Chi (Hol H 2 B)) :=
    p4Q2PZ37ANV_actualPhysicalFirstGaussMode_haarRepresentative H
  change (∫ B : Cfg H 2, v B * K H 2 beta B A ∂mu) = _
  calc
    _ = ∫ B : Cfg H 2, (-2 : ℝ) *
        (K H 2 beta A B * Chi (Hol H 2 B)) ∂mu := by
      apply integral_congr_ae
      filter_upwards [hMode] with B hB
      calc
        _ = ((-2 : ℝ) * Chi (Hol H 2 B)) * K H 2 beta A B :=
          congrArg₂ (fun a b : ℝ => a * b) hB
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
              H 2 (by norm_num) beta hbeta B A)
        _ = _ := by ring
    _ = _ := integral_const_mul (-2 : ℝ) _

private theorem p4Q2PZ37API_constantRep
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (A : Cfg H 2) :
    Rep H 2 beta ((C H 2 : P H 2) : Lp ℝ 2 (Mu H 2)) A =
      (∫ B, K H 2 beta A B ∂(Mu H 2)) := by
  let mu := Mu H 2
  let c : Lp ℝ 2 mu := ((C H 2 : P H 2) : Lp ℝ 2 mu)
  have hConst : c =ᵐ[mu] (fun _ : Cfg H 2 => (1 : ℝ)) := by
    change (Lp.const 2 mu (1 : ℝ)) =ᵐ[mu] _
    simpa only [Function.const_apply] using
      (Lp.coeFn_const (μ := mu) (p := (2 : ENNReal)) (c := (1 : ℝ)))
  change (∫ B : Cfg H 2, c B * K H 2 beta B A ∂mu) = _
  apply integral_congr_ae
  filter_upwards [hConst] with B hB
  rw [hB, one_mul]
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H 2 (by norm_num) beta hbeta B A

private theorem p4Q2PZ37API_transfer_ae
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (u : P H 2) :
    ((Tr H 2 (by norm_num) beta hbeta u : P H 2) : Lp ℝ 2 (Mu H 2)) =ᵐ[Mu H 2]
      Rep H 2 beta (u : Lp ℝ 2 (Mu H 2)) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe]
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
    H 2 (by norm_num) beta hbeta (u : Lp ℝ 2 (Mu H 2))

/-- Signed relative estimate in the original integral representatives. -/
theorem p4Q2PZ37API_originalPhysicalFirstMode_signedRelativeTransfer_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 128 * beta ≤ 1)
    (A : Cfg H 2) :
    Rep H 2 beta ((V H 1 : P H 2) : Lp ℝ 2 (Mu H 2)) A ≤
      -(beta / 64) * Rep H 2 beta ((C H 2 : P H 2) : Lp ℝ 2 (Mu H 2)) A := by
  rw [p4Q2PZ37API_firstRep H beta hbeta A, p4Q2PZ37API_constantRep H beta hbeta A]
  let i : ℝ := ∫ B, K H 2 beta A B * Chi (Hol H 2 B) ∂(Mu H 2)
  let z : ℝ := ∫ B, K H 2 beta A B ∂(Mu H 2)
  have h : beta * z / 128 ≤ i :=
    p4Q2PZ37APH_originalFirstRow_ge_beta_rowMass_div128 H beta hbeta hsmall A
  change (-2 : ℝ) * i ≤ -(beta / 64) * z
  linarith only [h]

/-- The original physical transfer inequality holds on actual L2 representatives. -/
theorem p4Q2PZ37API_originalPhysicalFirstMode_signedRelativeTransfer_ae
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 128 * beta ≤ 1) :
    ∀ᵐ A ∂(Mu H 2),
      ((Tr H 2 (by norm_num) beta hbeta (V H 1) : P H 2) : Lp ℝ 2 (Mu H 2)) A ≤
      -(beta / 64) *
        ((Tr H 2 (by norm_num) beta hbeta (C H 2) : P H 2) : Lp ℝ 2 (Mu H 2)) A := by
  let mu := Mu H 2
  let t := Tr H 2 (by norm_num) beta hbeta
  let v : P H 2 := V H 1
  let c : P H 2 := C H 2
  let f : Lp ℝ 2 mu := ((t v : P H 2) : Lp ℝ 2 mu)
  let g : Lp ℝ 2 mu := ((t c : P H 2) : Lp ℝ 2 mu)
  have hf : f =ᵐ[mu] Rep H 2 beta (v : Lp ℝ 2 mu) :=
    p4Q2PZ37API_transfer_ae H beta hbeta v
  have hg : g =ᵐ[mu] Rep H 2 beta (c : Lp ℝ 2 mu) :=
    p4Q2PZ37API_transfer_ae H beta hbeta c
  change ∀ᵐ A ∂mu, f A ≤ -(beta / 64) * g A
  filter_upwards [hf, hg] with A hA hB
  rw [hA, hB]
  exact p4Q2PZ37API_originalPhysicalFirstMode_signedRelativeTransfer_le H beta hbeta hsmall A

private theorem p4Q2PZ37API_relativeOrder_inner
    {α : Type*} [MeasurableSpace α] {mu : Measure α}
    (w f g : Lp ℝ 2 mu) (a : ℝ)
    (hw : ∀ᵐ x ∂mu, 0 ≤ w x)
    (h : ∀ᵐ x ∂mu, f x ≤ a * g x) :
    inner ℝ w f ≤ a * inner ℝ w g := by
  have hf : Integrable (fun x => w x * f x) mu := by
    simpa only [periodicHypercubicEven_real_inner_eq_mul] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) w f)
  have hg : Integrable (fun x => w x * g x) mu := by
    simpa only [periodicHypercubicEven_real_inner_eq_mul] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) w g)
  have hPoint : ∀ᵐ x ∂mu, w x * f x ≤ a * (w x * g x) := by
    filter_upwards [hw, h] with x hx hErr
    calc
      _ ≤ w x * (a * g x) := mul_le_mul_of_nonneg_left hErr hx
      _ = _ := by ring
  have hInt :
      (∫ x, w x * f x ∂mu) ≤ ∫ x, a * (w x * g x) ∂mu :=
    integral_mono_ae hf (hg.const_mul a) hPoint
  rw [integral_const_mul] at hInt
  simpa only [MeasureTheory.L2.inner_def, periodicHypercubicEven_real_inner_eq_mul] using hInt

/-- The genuine physical vacuum obeys the signed row bound with the exact
constant-mode amplitude and no extensive action-budget hypothesis. -/
theorem p4Q2PZ37API_originalPhysicalVacuumFirst_signedRelativeOverlap_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 128 * beta ≤ 1) :
    inner ℝ (Vac H 2 (by norm_num) beta hbeta) (V H 1) ≤
      -(beta / 64) * inner ℝ (Vac H 2 (by norm_num) beta hbeta) (C H 2) := by
  let mu := Mu H 2
  let t := Tr H 2 (by norm_num) beta hbeta
  let omega : P H 2 := Vac H 2 (by norm_num) beta hbeta
  let v : P H 2 := V H 1
  let c : P H 2 := C H 2
  let w : Lp ℝ 2 mu := (omega : Lp ℝ 2 mu)
  let f : Lp ℝ 2 mu := ((t v : P H 2) : Lp ℝ 2 mu)
  let g : Lp ℝ 2 mu := ((t c : P H 2) : Lp ℝ 2 mu)
  have hw : ∀ᵐ A ∂mu, 0 ≤ w A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta
  have hOrder : ∀ᵐ A ∂mu, f A ≤ -(beta / 64) * g A :=
    p4Q2PZ37API_originalPhysicalFirstMode_signedRelativeTransfer_ae H beta hbeta hsmall
  have h := p4Q2PZ37API_relativeOrder_inner w f g (-(beta / 64)) hw hOrder
  change inner ℝ omega (t v) ≤ -(beta / 64) * inner ℝ omega (t c) at h
  have hEigen : t omega = ‖t‖ • omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta
  have hMove (u : P H 2) : inner ℝ omega (t u) = ‖t‖ * inner ℝ omega u := by
    calc
      _ = inner ℝ (t omega) u :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
          H 2 (by norm_num) beta hbeta omega u).symm
      _ = _ := by
        rw [hEigen]
        exact real_inner_smul_left omega u ‖t‖
  rw [hMove v, hMove c] at h
  have hPos : 0 < ‖t‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  have hEq : -(beta / 64) * (‖t‖ * inner ℝ omega c) =
      ‖t‖ * (-(beta / 64) * inner ℝ omega c) := by ring
  rw [hEq] at h
  exact (mul_le_mul_iff_of_pos_left hPos).mp h

/-- The already frozen positive ADC coupling lies in the APH interval.
At every finite volume the genuine physical vacuum first overlap is negative. -/
theorem p4Q2PZ37API_originalPhysicalVacuumFirst_fixedCoupling_neg
    (H : ℕ) :
    inner ℝ
      (Vac H 2 (by norm_num) GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_pos.le)
      (V H 1) < 0 := by
  let beta := GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling
  have hb : 0 < beta := GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_pos
  have hExp : Real.exp (64 * beta) = (3 / 2 : ℝ) :=
    GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_exp_eq
  have hSmall : 128 * beta ≤ 1 := by
    have h := Real.add_one_le_exp (64 * beta)
    rw [hExp] at h
    linarith only [h]
  have h := p4Q2PZ37API_originalPhysicalVacuumFirst_signedRelativeOverlap_le
    H beta hb.le hSmall
  have ha := p4Q2PZ37ANM_originalPhysicalTop_inner_modeZero_pos H beta hb.le
  rw [p4Q2PZ37ANM_actualModeZero_eq_physicalConstant] at ha
  exact lt_of_le_of_lt h (mul_neg_of_neg_of_pos (by linarith only [hb]) ha)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37API_originalPhysicalFirstMode_signedRelativeTransfer_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37API_originalPhysicalFirstMode_signedRelativeTransfer_ae
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37API_originalPhysicalVacuumFirst_signedRelativeOverlap_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37API_originalPhysicalVacuumFirst_fixedCoupling_neg
