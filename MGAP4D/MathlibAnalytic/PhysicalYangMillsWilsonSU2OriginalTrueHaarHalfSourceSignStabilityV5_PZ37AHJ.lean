import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExplicitRationalRobustSignV5_PZ37AHI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHJ — genuine half-source Haar mass and eventual robust sign

AHI supplied the explicit original fixed-H rational right-boundary mesh
error 13*p_H^2/(32*N), using the older Msrc <= p_H bound.

AGN already proved the SHARPER pointwise bound for the SAME genuine
centered ZW continuous source: |fCont(A)| <= p_H/2.
This leaf transports that estimate through AFZ's exact true spatial Haar
L2 representative, proving Msrc <= p_H/2, without changing the source,
kernel, fixed beta, Haar measure, or any true-Haar cell definition.
The unchanged AEV true right-link Lipschitz estimate and AHG mesh now give

 |T_H(B)-T_H(B_(N,a))| <= 13*p_H^2/(64*N).

The sharpened error is used to preserve strict original AGP positive or
negative rational sign margins q/2 on an AHG right-boundary mesh.

AHI asserted existence of one sign branch at UNBOUNDED mesh orders.
AHJ strengthens the order quantifiers: one strict rational sign margin
persists on SOME right-boundary mesh at EVERY sufficiently large mesh
order, for each H. The original AHH sign-existence argument is used
without adding an independent nonzero-sign or rank assumption.

The chosen rational margin and center labels are existential;
nothing numerically evaluates the true Haar masses or a Boolean checker.
No assertion of both signs, fixed boundary at all mesh orders,
uniform-H coercivity or a continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Once a positive real denominator budget is satisfied, EVERY
larger integer denominator still satisfies it; this is stronger
than picking only an unbounded subsequence. -/
theorem p4Q2PZ37AHJ_eventually_small_denominator
    (C s : ℝ) (hC : 0 ≤ C) (hs : 0 < s) (M : ℕ) :
    ∃ N₀ : ℕ, M < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → C / (N : ℝ) < s := by
  obtain ⟨N₀, hMN₀, hN₀, hs₀⟩ :=
    p4Q2PZ37AHI_exists_largeDenominator C s hC hs M
  refine ⟨N₀, hMN₀, ?_⟩
  intro N hN₀N
  have hN₀real : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast hN₀
  have hLe : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN₀N
  have hNreal : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hN₀real hLe
  have hBound : C < (N₀ : ℝ) * s := (div_lt_iff₀ hN₀real).mp hs₀
  have hBound' : (N₀ : ℝ) * s ≤ (N : ℝ) * s :=
    mul_le_mul_of_nonneg_right hLe hs.le
  exact (div_lt_iff₀ hNreal).mpr (lt_of_lt_of_le hBound hBound')

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ

local instance p4Q2PZ37AHJ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHJ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHJ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHJ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHJ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta0
local notation "t" => decomposableOneSliceTransferIntegral H 2 beta0 f0
local notation "mesh" => p4Q2PZ37AHH_meshBoundary H

local instance p4Q2PZ37AHJ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHJ_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A pointwise statement about fCont is descended only almost everywhere
to the ORIGINAL physical L2 source. No arbitrary L2 pointwise identity. -/
theorem p4Q2PZ37AHJ_originalCenteredSource_halfCount_ae :
    ∀ᵐ A : Cfg ∂muH,
      |(f0 : Lp ℝ 2 muH) A| ≤ pH / 2 := by
  have hRep :
      (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) =ᵐ[muH] fCont := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muH) fCont
  filter_upwards [hRep] with A hA
  rw [hA]
  exact p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A

/-- TRUE original normalized spatial Haar L1 mass is at most p_H/2,
not merely the older p_H. No replacement probability law is used. -/
theorem p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount :
    Msrc ≤ pH / 2 := by
  have hf : Integrable (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) muH :=
    (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hAbs : Integrable (fun A : Cfg => |(f0 : Lp ℝ 2 muH) A|) muH := by
    simpa only [Real.norm_eq_abs] using hf.norm
  unfold p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass
  calc
    (∫ A : Cfg, |(f0 : Lp ℝ 2 muH) A| ∂muH) ≤
        ∫ _ : Cfg, pH / 2 ∂muH :=
      integral_mono_ae hAbs (integrable_const _)
        (p4Q2PZ37AHJ_originalCenteredSource_halfCount_ae H)
    _ = pH / 2 := by simp

/-- Uniform original signed transfer envelope improves as a direct
consequence of its true source mass; neither the kernel nor the transfer
has been replaced by a positive surrogate. -/
theorem p4Q2PZ37AHJ_originalTransfer_abs_le_halfCount (B : Cfg) :
    |t B| ≤ pH / 2 := by
  let f : Cfg → ℝ := fun A => (f0 : Lp ℝ 2 muH) A
  have hf : Integrable f muH :=
    (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hInt : Integrable (fun A : Cfg => f A * K A B) muH :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
      (f0 : Lp ℝ 2 muH) B
  have hK (A : Cfg) : |K A B - 0| ≤ (1 : ℝ) := by
    rw [sub_zero, abs_of_pos
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 beta0 A B)]
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A B
  have h := p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
    muH f (fun A => K A B) (fun _ => 0) 1 hf hInt (by simp) hK
  have hMass : |t B| ≤ Msrc := by
    rw [p4Q2PZ37AEV_originalCenteredTransfer_eq_originalKernelIntegral]
    simpa only [f, p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass,
      mul_zero, integral_zero, sub_zero, one_mul] using h
  exact hMass.trans (p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H)

/-- At the unchanged fixed beta0, the original right-transfer L1
Lipschitz coefficient improves to 13*p_H/256. -/
theorem p4Q2PZ37AHJ_transferSlope_le_halfRational :
    p4Q2PZ37AHH_transferSlope H ≤ (13 / 256 : ℝ) * pH := by
  have hb : 0 ≤ 13 * beta0 :=
    mul_nonneg (by norm_num) p4Q2PZ37ADC_fixedCoupling_pos.le
  have hbUpper : 13 * beta0 ≤ (13 / 128 : ℝ) := by
    have h := p4Q2PZ37AHI_fixedCoupling_le_one128
    linarith only [h]
  have hm : Msrc ≤ pH / 2 :=
    p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H
  have hp : 0 ≤ pH / 2 := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  change (13 * beta0) * Msrc ≤ (13 / 256 : ℝ) * pH
  calc
    (13 * beta0) * Msrc ≤ (13 * beta0) * (pH / 2) :=
      mul_le_mul_of_nonneg_left hm hb
    _ ≤ (13 / 128 : ℝ) * (pH / 2) :=
      mul_le_mul_of_nonneg_right hbUpper hp
    _ = (13 / 256 : ℝ) * pH := by ring

/-- Stronger original RIGHT mesh error: a fully rational coefficient,
true p_H, and the SAME AHG finite rational center presentation. -/
theorem p4Q2PZ37AHJ_halfMeshError
    (B : Cfg) (N : ℕ) (hN : 0 < N) :
    ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      |t B - t (mesh N a)| ≤ (13 / 64 : ℝ) * pH ^ 2 / (N : ℝ) := by
  obtain ⟨a, ha⟩ :=
    p4Q2PZ37AHH_originalTransfer_meshApproximation H B N hN
  have hp : 0 ≤ pH := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  have hNnr : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hProduct : 0 ≤ pH * (4 / (N : ℝ)) :=
    mul_nonneg hp (div_nonneg (by norm_num) hNnr)
  have hSlope :
      p4Q2PZ37AHH_transferSlope H * (pH * (4 / (N : ℝ))) ≤
        ((13 / 256 : ℝ) * pH) * (pH * (4 / (N : ℝ))) :=
    mul_le_mul_of_nonneg_right
      (p4Q2PZ37AHJ_transferSlope_le_halfRational H) hProduct
  refine ⟨a, ?_⟩
  calc
    |t B - t (mesh N a)| ≤
        p4Q2PZ37AHH_transferSlope H *
          ((Fintype.card Link : ℝ) * (4 / (N : ℝ))) := ha
    _ = p4Q2PZ37AHH_transferSlope H * (pH * (4 / (N : ℝ))) := by
      rw [p4Q2PZ37AHI_cardLinks_eq_plaquettes H]
    _ ≤ ((13 / 256 : ℝ) * pH) * (pH * (4 / (N : ℝ))) := hSlope
    _ = (13 / 64 : ℝ) * pH ^ 2 / (N : ℝ) := by ring

/-- Positive original true-Haar AGP table endpoint propagates to a
right-mesh positive margin with the HALVED error coefficient. -/
theorem p4Q2PZ37AHJ_positiveMargin_onMesh
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (q : ℚ)
    (hCert : q ≤ (p4Q2PZ37AGP_originalTable H d B b m n hn).lower)
    (N : ℕ) (hN : 0 < N)
    (hSmall : (13 / 64 : ℝ) * pH ^ 2 / (N : ℝ) < (q : ℝ) / 2) :
    ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      (q : ℝ) / 2 < t (mesh N a) := by
  obtain ⟨a, hErr⟩ := p4Q2PZ37AHJ_halfMeshError H B N hN
  have hqReal : (q : ℝ) ≤
      ((p4Q2PZ37AGP_originalTable H d B b m n hn).lower : ℝ) := by
    exact_mod_cast hCert
  have hPhysical : (q : ℝ) ≤ t B :=
    hqReal.trans (p4Q2PZ37AGP_originalTransfer_bounds H d B b m n hn).1
  have hDelta := (abs_le.mp hErr).2
  refine ⟨a, ?_⟩
  linarith only [hPhysical, hDelta, hSmall]

/-- Negative original signed AGP upper endpoint retains its distinct
orientation; no false positivity assumption on the integrand. -/
theorem p4Q2PZ37AHJ_negativeMargin_onMesh
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (q : ℚ)
    (hCert : (p4Q2PZ37AGP_originalTable H d B b m n hn).upper ≤ -q)
    (N : ℕ) (hN : 0 < N)
    (hSmall : (13 / 64 : ℝ) * pH ^ 2 / (N : ℝ) < (q : ℝ) / 2) :
    ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      t (mesh N a) < -(q : ℝ) / 2 := by
  obtain ⟨a, hErr⟩ := p4Q2PZ37AHJ_halfMeshError H B N hN
  have hqReal : ((p4Q2PZ37AGP_originalTable H d B b m n hn).upper : ℝ) ≤
      -(q : ℝ) := by exact_mod_cast hCert
  have hPhysical : t B ≤ -(q : ℝ) :=
    (p4Q2PZ37AGP_originalTransfer_bounds H d B b m n hn).2.trans hqReal
  have hDelta := (abs_le.mp hErr).1
  refine ⟨a, ?_⟩
  linarith only [hPhysical, hDelta, hSmall]

/-- Strengthens AHI's unbounded-subsequence result: for EVERY finite
H there is one sign and a fixed rational strict margin which can be
realized by an actual rational AHG right boundary at ALL mesh orders
beyond one order N0. The right boundary may vary with N. -/
theorem p4Q2PZ37AHJ_eventualAllOrdersOneSignMargin :
    ∃ q : ℚ, 0 < q ∧
      ((∃ N₀ : ℕ, 96 < N₀ ∧
          ∀ N : ℕ, N₀ ≤ N →
            ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
              (q : ℝ) < t (mesh N a)) ∨
       (∃ N₀ : ℕ, 96 < N₀ ∧
          ∀ N : ℕ, N₀ ≤ N →
            ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
              t (mesh N a) < -(q : ℝ))) := by
  obtain ⟨B, b, d, m, n, hn, hSign⟩ :=
    p4Q2PZ37AHH_exists_strictOriginalHaarTable H
  have hBudget : 0 ≤ (13 / 64 : ℝ) * pH ^ 2 := by positivity
  rcases hSign with hPos | hNeg
  · let Q : ℚ := (p4Q2PZ37AGP_originalTable H d B b m n hn).lower
    have hQ : 0 < Q := hPos
    have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    obtain ⟨N₀, h96, hSmall⟩ :=
      p4Q2PZ37AHJ_eventually_small_denominator
        ((13 / 64 : ℝ) * pH ^ 2) ((Q : ℝ) / 2)
        hBudget (div_pos hQr (by norm_num)) 96
    refine ⟨Q / 2, by positivity, Or.inl ⟨N₀, h96, ?_⟩⟩
    intro N hN₀N
    have hN : 0 < N := by omega
    obtain ⟨a, ha⟩ := p4Q2PZ37AHJ_positiveMargin_onMesh
      H d B b m n hn Q le_rfl N hN (hSmall N hN₀N)
    refine ⟨a, ?_⟩
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ha
  · let Q : ℚ := -(p4Q2PZ37AGP_originalTable H d B b m n hn).upper
    have hQ : 0 < Q := by dsimp [Q]; linarith only [hNeg]
    have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    have hUpper : (p4Q2PZ37AGP_originalTable H d B b m n hn).upper ≤ -Q := by
      dsimp [Q]
      simp
    obtain ⟨N₀, h96, hSmall⟩ :=
      p4Q2PZ37AHJ_eventually_small_denominator
        ((13 / 64 : ℝ) * pH ^ 2) ((Q : ℝ) / 2)
        hBudget (div_pos hQr (by norm_num)) 96
    refine ⟨Q / 2, by positivity, Or.inr ⟨N₀, h96, ?_⟩⟩
    intro N hN₀N
    have hN : 0 < N := by omega
    obtain ⟨a, ha⟩ := p4Q2PZ37AHJ_negativeMargin_onMesh
      H d B b m n hn Q hUpper N hN (hSmall N hN₀N)
    refine ⟨a, ?_⟩
    calc
      t (mesh N a) < -(Q : ℝ) / 2 := ha
      _ = -(((Q / 2 : ℚ) : ℝ)) := by push_cast; ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHJ_eventually_small_denominator
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHJ_originalCenteredSource_halfCount_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHJ_originalTransfer_abs_le_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHJ_transferSlope_le_halfRational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHJ_halfMeshError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHJ_positiveMargin_onMesh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHJ_negativeMargin_onMesh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHJ_eventualAllOrdersOneSignMargin
