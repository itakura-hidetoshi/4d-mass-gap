import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSpatialChordKernelV5_PZ37AEM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEN — genuine continuous Perron vacuum small-distance modulus

AEM gave the UNCONDITIONAL original Wilson-kernel bound
  |K_H(A,B[e↦g]) - K_H(A,B[e↦h])| ≤ 13*beta0*d_J(g,h).

This module uses the EXISTING canonical continuous Perron eigenfunction
Omega_H, the genuine positive physical top transfer norm lambda_H, the
ORIGINAL spatial-slice Haar probability measure, and the original
nonnegative normalized Haar L² Perron vector V_H. The EXACT pointwise
Perron equation is
  lambda_H*Omega_H(B) = ∫ V_H(A)*K_H(A,B) dmu_H(A).

AEK proves the pointwise original global bound Omega_H(A) ≤ k_H⁻¹,
where k_H is the genuine action floor. V_H is almost-everywhere the
same continuous representative, so its true Haar integral is ≤ k_H⁻¹.
AEJ proves lambda_H ≥ k_H > 0.

It follows WITHOUT an added spatial regularity assumption that
  |Omega_H(B[e↦g])-Omega_H(B[e↦h])|
    ≤ 13*beta0*(k_H⁻¹)^2 * d_J(g,h).

The coefficient is explicit and finite for each H, but generally
depends on H. Original rho/q and the full all-link D_H modulus are
separate later constructions. No new probability law or physical
operator is introduced; H-uniform coercivity and continuum mass gap
remain open.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance

local instance p4Q2PZ37AEN_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEN_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEN_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEN_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEN_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

/-- For a genuine integrable nonnegative Haar weight, any
pointwise uniform oscillation estimate on two integrable kernel
sections transfers to their weighted integrals. The integral of
the physical weight is bounded, not postulated to equal one. -/
theorem p4Q2PZ37AEN_real_weightedIntegral_absVariation
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f u v : α → ℝ) (C M : ℝ)
    (hf : Integrable f μ)
    (hu : Integrable (fun x => f x * u x) μ)
    (hv : Integrable (fun x => f x * v x) μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (huv : ∀ x, |u x - v x| ≤ C)
    (hmass : ∫ x, f x ∂μ ≤ M)
    (hC : 0 ≤ C) :
    |(∫ x, f x * u x ∂μ) - (∫ x, f x * v x ∂μ)| ≤ C * M := by
  have hI1 :
      (∫ x, f x * u x ∂μ) ≤
        (∫ x, f x * v x ∂μ) + C * (∫ x, f x ∂μ) := by
    calc
      (∫ x, f x * u x ∂μ) ≤
          ∫ x, (f x * v x + C * f x) ∂μ := by
        apply integral_mono_ae hu (hv.add (hf.const_mul C))
        filter_upwards [hf0] with x hx
        have habs := (abs_le.mp (huv x)).2
        have hmul := mul_le_mul_of_nonneg_left habs hx
        nlinarith only [hmul]
      _ = (∫ x, f x * v x ∂μ) + C * (∫ x, f x ∂μ) := by
        rw [integral_add hv (hf.const_mul C), integral_const_mul]
  have hI2 :
      (∫ x, f x * v x ∂μ) ≤
        (∫ x, f x * u x ∂μ) + C * (∫ x, f x ∂μ) := by
    calc
      (∫ x, f x * v x ∂μ) ≤
          ∫ x, (f x * u x + C * f x) ∂μ := by
        apply integral_mono_ae hv (hu.add (hf.const_mul C))
        filter_upwards [hf0] with x hx
        have habs := (abs_le.mp (huv x)).1
        have hmul := mul_le_mul_of_nonneg_left (by linarith only [habs]) hx
        nlinarith only [hmul]
      _ = (∫ x, f x * u x ∂μ) + C * (∫ x, f x ∂μ) := by
        rw [integral_add hu (hf.const_mul C), integral_const_mul]
  have hscaled : C * (∫ x, f x ∂μ) ≤ C * M :=
    mul_le_mul_of_nonneg_left hmass hC
  apply abs_le.mpr
  constructor <;> linarith only [hI1, hI2, hscaled]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) b0 hb0
local notation "lambda" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0

local instance p4Q2PZ37AEN_links : Fintype Link := Fintype.ofFinite _

/-- The true nonnegative original physical Perron L² vector has a
Haar integral bounded by the explicit AEK pointwise vacuum ceiling.
The a.e. identity is the one proved for the genuine continuous
representative, never an independently assumed posterior weight. -/
theorem p4Q2PZ37AEN_originalNonnegativeVacuum_HaarIntegral_le_explicit
    :
    (∫ A : Cfg,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) b0 hb0).1 A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) ≤ k⁻¹ := by
  let μ : Measure Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) b0 hb0
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hfInt : Integrable (fun A : Cfg => V.1 A) μ :=
    (Lp.memLp (V.1 : Lp ℝ 2 μ)).integrable (by norm_num)
  have hae := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 (by norm_num) b0 hb0
  have hBound : ∀ᵐ A ∂μ, V.1 A ≤ k⁻¹ := by
    filter_upwards [hae] with A hA
    have hx :=
      ((p4Q2PZ37AEK_originalContinuousVacuum_explicitBounds
        H 2 (by norm_num) b0 hb0) A).2
    change Omega A ≤ k⁻¹ at hx
    rw [hA] at hx
    exact hx
  have hMass : (∫ A : Cfg, V.1 A ∂μ) ≤ ∫ _ : Cfg, k⁻¹ ∂μ :=
    integral_mono_ae hfInt (integrable_const _) hBound
  simpa [V, μ] using hMass

/-- Genuine one-link small-distance variation for the EXISTING
continuous Perron vacuum, obtained by integrating the proved AEM
Wilson kernel bound against the genuine nonnegative L² eigenvector.

The finite-H explicit coefficient is 13*beta0/k_H²; it does not
assert a volume-uniform bound as H varies. -/
theorem p4Q2PZ37AEN_originalContinuousVacuum_oneLinkChordLipschitz
    (B : Cfg) (e : Link) (g h : G) :
    |Omega (Replace B e g) - Omega (Replace B e h)| ≤
      (13 * b0 * (k⁻¹)^2) * dJ g h := by
  let μ : Measure Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) b0 hb0
  let Bg := Replace B e g
  let Bh := Replace B e h
  have hk : 0 < k :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H b0
  have hLge : k ≤ lambda :=
    p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
      H 2 (by norm_num) b0 hb0
  have hLpos : 0 < lambda := lt_of_lt_of_le hk hLge
  have hfInt : Integrable (fun A : Cfg => V.1 A) μ :=
    (Lp.memLp (V.1 : Lp ℝ 2 μ)).integrable (by norm_num)
  have hf0 : ∀ᵐ A ∂μ, 0 ≤ V.1 A := by
    simpa only [V, μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H 2 (by norm_num) b0 hb0)
  have hInt (D : Cfg) :
      Integrable (fun A : Cfg => V.1 A * K A D) μ := by
    simpa only [V, μ, K] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
        H 2 (by norm_num) b0 hb0
        ((V : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2 μ) D)
  have hPerron (D : Cfg) :
      lambda * Omega D = ∫ A : Cfg, V.1 A * K A D ∂μ := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
        H 2 (by norm_num) b0 hb0 D
  have hMass :
      (∫ A : Cfg, V.1 A ∂μ) ≤ k⁻¹ := by
    simpa [V, μ] using
      (p4Q2PZ37AEN_originalNonnegativeVacuum_HaarIntegral_le_explicit H)
  have hC : 0 ≤ (13 * b0) * dJ g h := by
    exact mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) hb0)
      (p4Q2PZ37ADK_trueChordalDistance_nonneg g h)
  have hIntegral :
      |(∫ A : Cfg, V.1 A * K A Bg ∂μ) -
        (∫ A : Cfg, V.1 A * K A Bh ∂μ)| ≤
        ((13 * b0) * dJ g h) * k⁻¹ := by
    apply p4Q2PZ37AEN_real_weightedIntegral_absVariation
      μ (fun A : Cfg => V.1 A) (fun A => K A Bg) (fun A => K A Bh)
      ((13 * b0) * dJ g h) k⁻¹
      hfInt (hInt Bg) (hInt Bh) hf0
    · intro A
      exact
        p4Q2PZ37AEM_originalOneSlabKernel_unconditionalChordLipschitz
          H A B e g h
    · exact hMass
    · exact hC
  have hScaled :
      lambda * |Omega Bg - Omega Bh| ≤
        ((13 * b0) * dJ g h) * k⁻¹ := by
    calc
      lambda * |Omega Bg - Omega Bh| =
          |lambda * Omega Bg - lambda * Omega Bh| := by
        rw [← mul_sub, abs_mul, abs_of_pos hLpos]
      _ = |(∫ A : Cfg, V.1 A * K A Bg ∂μ) -
          (∫ A : Cfg, V.1 A * K A Bh ∂μ)| := by
        rw [hPerron Bg, hPerron Bh]
      _ ≤ ((13 * b0) * dJ g h) * k⁻¹ := hIntegral
  have hFloor :
      k * |Omega Bg - Omega Bh| ≤
        ((13 * b0) * dJ g h) * k⁻¹ := by
    calc
      k * |Omega Bg - Omega Bh| ≤
          lambda * |Omega Bg - Omega Bh| :=
        mul_le_mul_of_nonneg_right hLge (abs_nonneg _)
      _ ≤ ((13 * b0) * dJ g h) * k⁻¹ := hScaled
  have hDiv :
      |Omega Bg - Omega Bh| ≤
        (((13 * b0) * dJ g h) * k⁻¹) / k :=
      (le_div_iff₀ hk).2 hFloor
  calc
    |Omega Bg - Omega Bh| ≤
        (((13 * b0) * dJ g h) * k⁻¹) / k := hDiv
    _ = (13 * b0 * (k⁻¹)^2) * dJ g h := by
      rw [div_eq_mul_inv]
      ring

/-- The AEN Perron estimate uses the SAME full two-boundary
physical chordal distance as AEL/ADL when precisely one
second-boundary SU(2) link is replaced. -/
theorem p4Q2PZ37AEN_originalContinuousVacuum_oneLinkFullDistance
    (A B : Cfg) (e : Link) (g h : G) :
    |Omega (Replace B e g) - Omega (Replace B e h)| ≤
      (13 * b0 * (k⁻¹)^2) *
        p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
          (A, Replace B e g) (A, Replace B e h) := by
  rw [p4Q2PZ37AEL_originalFullDistance_secondBoundary_oneLink]
  exact p4Q2PZ37AEN_originalContinuousVacuum_oneLinkChordLipschitz H B e g h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEN_real_weightedIntegral_absVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEN_originalNonnegativeVacuum_HaarIntegral_le_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEN_originalContinuousVacuum_oneLinkChordLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEN_originalContinuousVacuum_oneLinkFullDistance
