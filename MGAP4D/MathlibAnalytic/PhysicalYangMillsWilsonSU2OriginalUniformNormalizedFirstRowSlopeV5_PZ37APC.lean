import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoOriginKernelRelativeTaylorV5_PZ37AOZ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSingleOriginWeightedCharacterSecondMomentV5_PZ37APA
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDoubleCenterHaarRelativeIntegralV5_PZ37APB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APC — volume-uniform original normalized first row response

Candidate staged against the exact AOZ/APA/APB source bytes.
AOZ supplies the pointwise mixed Taylor residual, APB transports it
to the actual Haar integral, and APA controls its weighted second
moment with one genuine link resampling. Their proposed combination
is |I - beta Z/8| <= (195/2) beta^2 Z and, for positive beta,
|I/(beta Z) - 1/8| <= (195/2) beta, independently of finite H and A.
The row mass is positive for each finite volume; no uniform lower
bound on its size or any new hypothesis is introduced. The row
normalized response is not a physical top state, a transfer spectral
gap or the continuum 4D Yang-Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy

local instance p4Q2PZ37APC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APC_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APC_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37APC_kernel_continuous
    (H : ℕ) (beta : ℝ) (A : Cfg H 2) :
    Continuous (fun B : Cfg H 2 => K H 2 beta A B) := by
  have hPair : Continuous (fun B : Cfg H 2 => (A, B)) :=
    (continuous_const : Continuous (fun _ : Cfg H 2 => A)).prodMk
      (continuous_id : Continuous (fun B : Cfg H 2 => B))
  change Continuous ((fun p : Cfg H 2 × Cfg H 2 => K H 2 beta p.1 p.2) ∘
    (fun B : Cfg H 2 => (A, B)))
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta).comp hPair

private theorem p4Q2PZ37APC_rowMass_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (A : Cfg H 2) :
    0 < (∫ B, K H 2 beta A B ∂(Mu H 2)) := by
  let mu := Mu H 2
  let k : Cfg H 2 → ℝ := fun B => K H 2 beta A B
  let floor : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hKInt : Integrable k mu :=
    (p4Q2PZ37APC_kernel_continuous H beta A).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (B : Cfg H 2) : floor ≤ k B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
      H 2 (by norm_num) beta hbeta A B
  have hFloor : (∫ _ : Cfg H 2, floor ∂mu) = floor := by
    exact integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
  have hBound : floor ≤ (∫ B : Cfg H 2, k B ∂mu) := by
    calc
      floor = (∫ _ : Cfg H 2, floor ∂mu) := hFloor.symm
      _ ≤ (∫ B : Cfg H 2, k B ∂mu) := by
        apply integral_mono_ae (integrable_const floor) hKInt
        filter_upwards [] with B
        exact hPoint B
  change 0 < (∫ B : Cfg H 2, k B ∂mu)
  exact lt_of_lt_of_le
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H beta)
    hBound

/-- Instantiate APB on the literal original Wilson kernel, using the
already source-bound AOZ pointwise estimate. -/
theorem p4Q2PZ37APC_originalFirstRow_mixedRelativeIntegralError_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 16 * beta ≤ 1)
    (A : Cfg H 2) :
    |4 * (∫ B, K H 2 beta A B * Chi (Hol H 2 B) ∂(Mu H 2)) -
        2 * beta * (∫ B, K H 2 beta A B * (Chi (Hol H 2 B))^2 ∂(Mu H 2))| ≤
      384 * beta^2 * (∫ B, K H 2 beta A B ∂(Mu H 2)) := by
  let k : Cfg H 2 → ℝ := fun B => K H 2 beta A B
  have hk : Continuous k := p4Q2PZ37APC_kernel_continuous H beta A
  have hn (B : Cfg H 2) : 0 ≤ k B := by
    dsimp [k]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    exact Real.exp_nonneg _
  exact p4Q2PZ37APB_originalHaarPrimaryCharacter_mixedRelativeIntegral_abs_le
    H k hk (2 * beta) (384 * beta^2) (by positivity) hn
    (fun B => p4Q2PZ37AOZ_originalKernel_twoOriginMixedRelativeTaylor_abs_le H beta hbeta hsmall A B)

/-- Combine the exact relative integral estimate and the one-link
weighted Haar second moment, without normalizing by a volume-dependent
bound or assuming a product law for the interacting row. -/
theorem p4Q2PZ37APC_originalFirstRow_linearError_le_rowMass
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 16 * beta ≤ 1)
    (A : Cfg H 2) :
    |(∫ B, K H 2 beta A B * Chi (Hol H 2 B) ∂(Mu H 2)) -
        beta * (∫ B, K H 2 beta A B ∂(Mu H 2)) / 8| ≤
      (195 / 2 : ℝ) * beta^2 * (∫ B, K H 2 beta A B ∂(Mu H 2)) := by
  let i : ℝ := ∫ B, K H 2 beta A B * Chi (Hol H 2 B) ∂(Mu H 2)
  let m : ℝ := ∫ B, K H 2 beta A B * (Chi (Hol H 2 B))^2 ∂(Mu H 2)
  let z : ℝ := ∫ B, K H 2 beta A B ∂(Mu H 2)
  have hMixed : |4 * i - 2 * beta * m| ≤ 384 * beta^2 * z :=
    p4Q2PZ37APC_originalFirstRow_mixedRelativeIntegralError_le H beta hbeta hsmall A
  have hMoment : |m - z / 4| ≤ 3 * beta * z :=
    p4Q2PZ37APA_originalWeightedCharacterSquare_error_le H beta hbeta hsmall A
  have hScaled : |(2 * beta) * (m - z / 4)| ≤ 6 * beta^2 * z := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * beta)]
    calc
      _ ≤ (2 * beta) * (3 * beta * z) :=
        mul_le_mul_of_nonneg_left hMoment (by positivity)
      _ = _ := by ring
  have hEq : 4 * (i - beta * z / 8) =
      (4 * i - 2 * beta * m) + (2 * beta) * (m - z / 4) := by ring
  have hAbs : |4 * (i - beta * z / 8)| ≤ 390 * beta^2 * z := by
    rw [hEq]
    calc
      _ ≤ |4 * i - 2 * beta * m| + |(2 * beta) * (m - z / 4)| := abs_add_le _ _
      _ ≤ 384 * beta^2 * z + 6 * beta^2 * z := add_le_add hMixed hScaled
      _ = _ := by ring
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hAbs
  change |i - beta * z / 8| ≤ (195 / 2 : ℝ) * beta^2 * z
  linarith only [hAbs]

/-- A uniform normalized original row response at weak coupling.
There is no dependence on H, A or the extensive action budget in
the error constant. The positive denominator is the actual row mass. -/
theorem p4Q2PZ37APC_originalFirstRow_normalizedUniformSlopeError_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hsmall : 16 * beta ≤ 1)
    (A : Cfg H 2) :
    |(∫ B, K H 2 beta A B * Chi (Hol H 2 B) ∂(Mu H 2)) /
        (beta * (∫ B, K H 2 beta A B ∂(Mu H 2))) - (1 / 8 : ℝ)| ≤
      (195 / 2 : ℝ) * beta := by
  let i : ℝ := ∫ B, K H 2 beta A B * Chi (Hol H 2 B) ∂(Mu H 2)
  let z : ℝ := ∫ B, K H 2 beta A B ∂(Mu H 2)
  have hz : 0 < z := p4Q2PZ37APC_rowMass_pos H beta hbeta.le A
  have h := p4Q2PZ37APC_originalFirstRow_linearError_le_rowMass H beta hbeta.le hsmall A
  change |i - beta * z / 8| ≤ (195 / 2 : ℝ) * beta^2 * z at h
  have hEq : i / (beta * z) - (1 / 8 : ℝ) =
      (i - beta * z / 8) / (beta * z) := by
    field_simp [ne_of_gt hbeta, ne_of_gt hz]
  change |i / (beta * z) - (1 / 8 : ℝ)| ≤ (195 / 2 : ℝ) * beta
  rw [hEq, abs_div, abs_of_pos (mul_pos hbeta hz)]
  apply (div_le_iff₀ (mul_pos hbeta hz)).2
  calc
    _ ≤ (195 / 2 : ℝ) * beta^2 * z := h
    _ = _ := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APC_originalFirstRow_mixedRelativeIntegralError_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APC_originalFirstRow_linearError_le_rowMass
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APC_originalFirstRow_normalizedUniformSlopeError_le
