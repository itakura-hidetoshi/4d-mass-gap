import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalVacuumRelativeFirstSlopeV5_PZ37APD
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APF — uniform signed relative first-mode slope of the physical vacuum

STAGED ONLY. APD must pass sandbox, independent CI and postmerge
certification before this candidate is tested. The actual unit vacuum
has positive constant-mode amplitude by the existing nonnegative L2
integral lemma. APD implies an H-uniform signed relative slope and an
H-uniform strict negativity interval, even along arbitrarily moving H.
No positive volume-independent lower bound on the amplitude is claimed.
This is not a continuum scaling limit or a mass-gap theorem.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct
open scoped NNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "P" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "C" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
local notation "V" => p4Q2PZ37AMU_actualPhysicalGaussMode
local notation "Vac" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector

local instance p4Q2PZ37APF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APF_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APF_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APF_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APF_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APF_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37APF_constantAmplitude_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < inner ℝ (Vac H 2 (by norm_num) beta hbeta) (C H 2) := by
  let mu := Mu H 2
  let omega : P H 2 := Vac H 2 (by norm_num) beta hbeta
  let c : P H 2 := C H 2
  let w : Lp ℝ 2 mu := (omega : Lp ℝ 2 mu)
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hw : ∀ᵐ A ∂mu, 0 ≤ w A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta
  have hnorm : ‖w‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hbeta
  have hInt := realL2_integral_pos_of_ae_nonnegative_norm_one w hw hnorm
  have hEq : inner ℝ c omega = ∫ A, w A ∂mu := by
    change inner ℝ (Lp.const 2 mu (1 : ℝ)) w = _
    exact realL2_inner_const_one_eq_integral w
  change 0 < inner ℝ omega c
  calc
    0 < ∫ A, w A ∂mu := hInt
    _ = inner ℝ c omega := hEq.symm
    _ = inner ℝ omega c := real_inner_comm _ _

/-- The exact first-mode slope relative to the actual positive
constant amplitude has a volume-independent quantitative error. -/
theorem p4Q2PZ37APF_originalPhysicalVacuumFirst_normalizedRelativeSlopeError_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hsmall : 16 * beta ≤ 1) :
    |inner ℝ (Vac H 2 (by norm_num) beta hbeta.le) (V H 1) /
      (beta * inner ℝ (Vac H 2 (by norm_num) beta hbeta.le) (C H 2)) +
      (1 / 4 : ℝ)| ≤ 195 * beta := by
  let x : ℝ := inner ℝ (Vac H 2 (by norm_num) beta hbeta.le) (V H 1)
  let a : ℝ := inner ℝ (Vac H 2 (by norm_num) beta hbeta.le) (C H 2)
  have ha : 0 < a := p4Q2PZ37APF_constantAmplitude_pos H beta hbeta.le
  have h := p4Q2PZ37APD_originalPhysicalVacuumFirst_relativeSlopeError_le
    H beta hbeta.le hsmall
  change |x + beta / 4 * a| ≤ 195 * beta^2 * a at h
  have hEq : x / (beta * a) + (1 / 4 : ℝ) =
      (x + beta / 4 * a) / (beta * a) := by
    field_simp [ne_of_gt hbeta, ne_of_gt ha]
  change |x / (beta * a) + (1 / 4 : ℝ)| ≤ 195 * beta
  rw [hEq, abs_div, abs_of_pos (mul_pos hbeta ha)]
  apply (div_le_iff₀ (mul_pos hbeta ha)).2
  calc
    _ ≤ 195 * beta^2 * a := h
    _ = _ := by ring

/-- A strict sign interval for the genuine first Gauss-law overlap,
uniformly for every finite volume and the actual selected unit vacuum. -/
theorem p4Q2PZ37APF_originalPhysicalVacuumFirst_neg_of_uniform_small_beta
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hcut : beta < (1 / 780 : ℝ)) :
    inner ℝ (Vac H 2 (by norm_num) beta hbeta.le) (V H 1) < 0 := by
  have hsmall : 16 * beta ≤ 1 := by linarith only [hcut]
  let x : ℝ := inner ℝ (Vac H 2 (by norm_num) beta hbeta.le) (V H 1)
  let a : ℝ := inner ℝ (Vac H 2 (by norm_num) beta hbeta.le) (C H 2)
  have ha : 0 < a := p4Q2PZ37APF_constantAmplitude_pos H beta hbeta.le
  have h := p4Q2PZ37APD_originalPhysicalVacuumFirst_relativeSlopeError_le
    H beta hbeta.le hsmall
  change |x + beta / 4 * a| ≤ 195 * beta^2 * a at h
  have hlt : 195 * beta < (1 / 4 : ℝ) := by linarith only [hcut]
  have hlt2 : 195 * beta^2 < beta / 4 := by
    have hh := mul_lt_mul_of_pos_right hlt hbeta
    nlinarith only [hh]
  have hh := mul_lt_mul_of_pos_right hlt2 ha
  change x < 0
  linarith only [(abs_le.mp h).2, hh]

/-- No extensive action-budget smallness is required in this moving-volume
relative slope limit. The normalization is the actual positive amplitude,
not a uniform lower bound for it. -/
theorem p4Q2PZ37APF_originalPhysicalVacuumFirst_movingRelativeSlope_tendsto
    {ι : Type*} (l : Filter ι) (H : ι → ℕ) (beta : ι → ℝ≥0)
    (hzero : Tendsto (fun i => (beta i : ℝ)) l (𝓝 (0 : ℝ)))
    (hpos : ∀ᶠ i in l, 0 < (beta i : ℝ)) :
    Tendsto (fun i =>
      inner ℝ (Vac (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property) (V (H i) 1) /
      ((beta i : ℝ) *
        inner ℝ (Vac (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property) (C (H i) 2)))
      l (𝓝 (-(1 / 4 : ℝ))) := by
  let q : ι → ℝ := fun i =>
    inner ℝ (Vac (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property) (V (H i) 1) /
      ((beta i : ℝ) *
        inner ℝ (Vac (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property) (C (H i) 2))
  have h16 : Tendsto (fun i => (16 : ℝ) * (beta i : ℝ)) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hzero.const_mul (16 : ℝ)
  have hsmall : ∀ᶠ i in l, 16 * (beta i : ℝ) < (1 : ℝ) :=
    h16.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hUpper : Tendsto (fun i => (195 : ℝ) * (beta i : ℝ)) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hzero.const_mul (195 : ℝ)
  have hBound : ∀ᶠ i in l, |q i + (1 / 4 : ℝ)| ≤ 195 * (beta i : ℝ) := by
    filter_upwards [hpos, hsmall] with i hi hs
    exact p4Q2PZ37APF_originalPhysicalVacuumFirst_normalizedRelativeSlopeError_le
      (H i) (beta i : ℝ) hi hs.le
  have hError : Tendsto (fun i => |q i + (1 / 4 : ℝ)|) l (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
      (Eventually.of_forall fun i => abs_nonneg _) hBound
  change Tendsto q l (𝓝 (-(1 / 4 : ℝ)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs, sub_neg_eq_add] using hError

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APF_originalPhysicalVacuumFirst_normalizedRelativeSlopeError_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APF_originalPhysicalVacuumFirst_neg_of_uniform_small_beta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APF_originalPhysicalVacuumFirst_movingRelativeSlope_tendsto
