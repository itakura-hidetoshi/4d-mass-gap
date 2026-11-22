import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstHaarMomentValueV5_PZ37ANV
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOC — local center-flip cancellation in the original first-mode response

The physical first Gauss-law mode has its genuine pair-Haar representative
-2 times the original primary SU(2) character.  Its sign reverses under an
actual Haar-preserving primary-link center twist.  The complete original
one-slab action changes by at most eight under that twist.

Antisymmetrizing the actual Taylor remainder before taking absolute values
gives |r_H(beta) + beta/4| <= 8 C_H beta^2 for every beta >= 0, where r_H is
the original fixed-Haar physical transfer response.  No smallness premise
C_H beta <= 1 is used.  This improves the global C_H^2 estimate for this
response component.  The changing-vacuum error from ANR is not improved here;
no volume-uniform physical overlap or continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The literal first Taylor remainder of the unchanged full Wilson kernel. -/
noncomputable def p4Q2PZ37AOC_originalKernelTaylorRemainder
    (H : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B - 1 +
    beta * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOC_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOC_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- ANV's genuine center twist is the existing one-link replacement,
with exactly the original link value multiplied by the SU(2) center. -/
private theorem p4Q2PZ37AOC_singleLinkCenterTwist_eq_replaceLink
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2PZ37ANV_singleLinkCenterTwist H target B =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H 2 B target (B target * specialUnitaryTwoNegativeIdentity) := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    rw [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self]
    simp [p4Q2PZ37ANV_singleLinkCenterTwist]
  · rw [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
      H 2 B target e (B target * specialUnitaryTwoNegativeIdentity) he]
    simp [p4Q2PZ37ANV_singleLinkCenterTwist, he]

/-- Replacing a link with its own genuine value leaves the configuration fixed. -/
private theorem p4Q2PZ37AOC_replaceLink_originalValue
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H 2 B target (B target) = B := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self
      H 2 B target (B target)
  · exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
      H 2 B target e (B target) he

/-- The complete original one-slab action changes by at most eight
under the actual right-boundary single-link center flip, for every H. -/
theorem p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A
        (p4Q2PZ37ANV_singleLinkCenterTwist H target B) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B| ≤ 8 := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_continuousVacuumReplaceLink_sub_abs_le_eight
      H 2 (by norm_num) A B target
      (B target * specialUnitaryTwoNegativeIdentity) (B target)
  rw [← p4Q2PZ37AOC_singleLinkCenterTwist_eq_replaceLink H target B,
    p4Q2PZ37AOC_replaceLink_originalValue H target B] at h
  exact h

/-- The same estimate with the original action written first. -/
private theorem p4Q2PZ37AOC_originalSlabAction_sub_rightCenterTwist_abs_le_eight
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A
        (p4Q2PZ37ANV_singleLinkCenterTwist H target B)| ≤ 8 := by
  rw [abs_sub_comm]
  exact p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight H target A B

/-- Continuity is coordinatewise multiplication by a fixed center element. -/
private theorem p4Q2PZ37AOC_singleLinkCenterTwist_continuous
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (p4Q2PZ37ANV_singleLinkCenterTwist H target) := by
  classical
  unfold p4Q2PZ37ANV_singleLinkCenterTwist
  apply continuous_pi
  intro e
  exact (continuous_apply e).mul continuous_const

/-- Use exactly the original primary origin link, so ANV fixes the sign. -/
private theorem p4Q2PZ37AOC_primaryCharacter_centerTwist_odd
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
      (p4Q2PZ37ANV_singleLinkCenterTwist H
        (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)) =
      -Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) := by
  rw [p4Q2PZ37ANV_singleLinkCenterTwist_eq_existingPU]
  exact p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd
    H (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) (Or.inl rfl) B

/-- The genuine normalized primary Wilson character lies in [-1,1]. -/
private theorem p4Q2PZ37AOC_primaryCharacter_abs_le_one
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)| ≤ 1 := by
  rw [p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter]
  unfold GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter
  have hlow := specialUnitaryWilsonPlaquetteEnergy_nonneg
    (by norm_num : 0 < (2 : ℕ))
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
  have hup := specialUnitaryWilsonPlaquetteEnergy_le_two
    (by norm_num : 0 < (2 : ℕ))
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
  rw [abs_le]
  constructor <;> linarith

/-- A reusable continuous representative, prior to any L2 coercion. -/
private theorem p4Q2PZ37AOC_primaryCharacter_continuous (H : ℕ) :
    Continuous
      (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) := by
  have heq :
      (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) =
      (fun B => GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
    funext B
    exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
  rw [heq]
  exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
    H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)

/-- The negative-exponential first remainder has a Lipschitz constant
beta^2*C on [0,C], at every nonnegative beta. -/
theorem p4Q2PZ37AOC_real_expTaylorRemainder_abs_sub_le
    (beta C x y : ℝ) (hbeta : 0 ≤ beta)
    (hx0 : 0 ≤ x) (hxC : x ≤ C) (hy0 : 0 ≤ y) (hyC : y ≤ C) :
    |(Real.exp (-beta * x) - 1 + beta * x) -
      (Real.exp (-beta * y) - 1 + beta * y)| ≤
      (beta^2 * C) * |x - y| := by
  let f : ℝ → ℝ := fun u => Real.exp (-beta * u) - 1 + beta * u
  let f' : ℝ → ℝ := fun u => beta * (1 - Real.exp (-beta * u))
  have hderiv (u : ℝ) : HasDerivAt f (f' u) u := by
    dsimp [f, f']
    convert (((((hasDerivAt_id u).const_mul (-beta)).exp).sub
      (hasDerivAt_const u (1 : ℝ))).add
      ((hasDerivAt_id u).const_mul beta)) using 1
    simp only [id_eq]
    ring
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) C, ‖f' u‖ ≤ beta^2 * C := by
    intro u hu
    have hExp : Real.exp (-beta * u) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta) hu.1
    have hnonneg : 0 ≤ beta * (1 - Real.exp (-beta * u)) :=
      mul_nonneg hbeta (sub_nonneg.mpr hExp)
    have hTaylor := Real.add_one_le_exp (-beta * u)
    have hOne : 1 - Real.exp (-beta * u) ≤ beta * u := by
      linarith only [hTaylor]
    have hScaled := mul_le_mul_of_nonneg_left hOne hbeta
    have hUpper := mul_le_mul_of_nonneg_left hu.2 (sq_nonneg beta)
    dsimp [f']
    rw [abs_of_nonneg hnonneg]
    nlinarith only [hScaled, hUpper]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := Set.Icc (0 : ℝ) C)
    (fun u _hu => (hderiv u).hasDerivWithinAt)
    hbound (convex_Icc (0 : ℝ) C) ⟨hy0, hyC⟩ ⟨hx0, hxC⟩
  simpa only [f, Real.norm_eq_abs] using h

private theorem p4Q2PZ37AOC_originalSlabAction_pair_continuous (H : ℕ) :
    Continuous (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 p.1 p.2) := by
  have hW := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hX := periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous H 2
  dsimp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction]
  exact ((continuous_const.mul (hW.comp continuous_fst)).add hX).add
    (continuous_const.mul (hW.comp continuous_snd))

private theorem p4Q2PZ37AOC_originalKernel_pair_continuous (H : ℕ) (beta : ℝ) :
    Continuous (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta p.1 p.2) := by
  have hExp : Continuous (fun p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      Real.exp (-beta *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 p.1 p.2)) :=
    Real.continuous_exp.comp
      (continuous_const.mul (p4Q2PZ37AOC_originalSlabAction_pair_continuous H))
  simpa only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    using hExp

private theorem p4Q2PZ37AOC_originalKernelTaylorRemainder_pair_continuous
    (H : ℕ) (beta : ℝ) :
    Continuous (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      p4Q2PZ37AOC_originalKernelTaylorRemainder H beta p.1 p.2) := by
  exact ((p4Q2PZ37AOC_originalKernel_pair_continuous H beta).sub continuous_const).add
    (continuous_const.mul (p4Q2PZ37AOC_originalSlabAction_pair_continuous H))

/-- Exact signed pairing under the actual pair-Haar law.  The constant
part of a continuous kernel cancels under the original primary center flip. -/
theorem p4Q2PZ37AOC_originalFirstCharacter_pairHaar_antisymmetrization
    (H : ℕ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ)
    (hF : Continuous F) :
    (-2 : ℝ) *
      (∫ p, F p * Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) =
      -(∫ p, (F p - F (p.1,
          p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) p.2)) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let pairMu := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let sigma : Cfg × Cfg → Cfg × Cfg := fun p => (p.1, tau p.2)
  let chi : Cfg × Cfg → ℝ := fun p =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)
  have hChi : Continuous chi :=
    (p4Q2PZ37AOC_primaryCharacter_continuous H).comp continuous_snd
  have hTau : Continuous tau :=
    p4Q2PZ37AOC_singleLinkCenterTwist_continuous H _
  have hSigma : Continuous sigma :=
    continuous_fst.prodMk (hTau.comp continuous_snd)
  have hMP : MeasurePreserving sigma pairMu pairMu := by
    change MeasurePreserving (Prod.map id tau) (mu.prod mu) (mu.prod mu)
    exact (MeasurePreserving.id mu).prod
      (p4Q2PZ37ANV_singleLinkCenterTwist_haarMeasurePreserving H _)
  have hOdd (p : Cfg × Cfg) : chi (sigma p) = -chi p :=
    p4Q2PZ37AOC_primaryCharacter_centerTwist_odd H p.2
  have hTransport :
      (∫ p, F (sigma p) * chi (sigma p) ∂pairMu) =
        ∫ p, F p * chi p ∂pairMu := by
    have hMap :
        (∫ p, F p * chi p ∂Measure.map sigma pairMu) =
          ∫ p, F (sigma p) * chi (sigma p) ∂pairMu :=
      integral_map hMP.measurable.aemeasurable
        (hF.mul hChi).measurable.aestronglyMeasurable
    rw [hMP.map_eq] at hMap
    exact hMap.symm
  have hTwisted : (∫ p, F (sigma p) * chi p ∂pairMu) =
      -(∫ p, F p * chi p ∂pairMu) := by
    have hNeg :
        (∫ p, F (sigma p) * chi (sigma p) ∂pairMu) =
          -(∫ p, F (sigma p) * chi p ∂pairMu) := by
      simp_rw [hOdd, mul_neg]
      rw [integral_neg]
    rw [hNeg] at hTransport
    linarith only [hTransport]
  have hInt : Integrable (fun p => F p * chi p) pairMu :=
    (hF.mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTwistedInt : Integrable (fun p => F (sigma p) * chi p) pairMu :=
    ((hF.comp hSigma).mul hChi).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDifference :
      (∫ p, (F p - F (sigma p)) * chi p ∂pairMu) =
        (∫ p, F p * chi p ∂pairMu) -
          (∫ p, F (sigma p) * chi p ∂pairMu) := by
    calc
      _ = ∫ p, F p * chi p - F (sigma p) * chi p ∂pairMu := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = _ := integral_sub hInt hTwistedInt
  change (-2 : ℝ) * (∫ p, F p * chi p ∂pairMu) =
    -(∫ p, (F p - F (sigma p)) * chi p ∂pairMu)
  rw [hDifference, hTwisted]
  ring

private theorem p4Q2PZ37AOC_originalFixedHaarResponse_eq_kernelCharacter
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) 0 (by norm_num))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) =
      (-2 : ℝ) * (∫ p,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta p.1 p.2 *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let pairMu := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let E : Lp ℝ 2 pairMu :=
    realL2ExternalTensor (c : Lp ℝ 2 mu) (v1 : Lp ℝ 2 mu)
  let K : Lp ℝ 2 pairMu :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H 2 (by norm_num) beta hbeta
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  have hT : inner ℝ K E = inner ℝ (T c) v1 := by
    change realL2HilbertSchmidtKernelPairing K (c : Lp ℝ 2 mu) (v1 : Lp ℝ 2 mu) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta (c : Lp ℝ 2 mu)) (v1 : Lp ℝ 2 mu)
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
      H 2 (by norm_num) beta hbeta (c : Lp ℝ 2 mu) (v1 : Lp ℝ 2 mu)).symm
  have hU : inner ℝ (U c) v1 = 0 :=
    p4Q2PZ37ANP_originalPhysicalBetaZero_allInput_modeOne_inner_zero H c
  have hResponse : inner ℝ ((T - U) c) v1 = inner ℝ K E := by
    rw [ContinuousLinearMap.sub_apply,
      inner_sub_left (𝕜 := ℝ) (T c) (U c) v1, hU, sub_zero]
    exact hT.symm
  have hK : K =ᵐ[pairMu]
      (fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta p.1 p.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H 2 (by norm_num) beta hbeta
  have hE : E =ᵐ[pairMu]
      (fun p => (-2 : ℝ) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)) :=
    p4Q2PZ37ANV_actualFirstPhysicalTensor_pairHaarRepresentative H
  change inner ℝ ((T - U) c) v1 = _
  rw [hResponse, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ p, (-2 : ℝ) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta p.1 p.2 *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)) ∂pairMu := by
      apply integral_congr_ae
      filter_upwards [hK, hE] with p hk he
      change inner ℝ (K p) (E p) = (-2 : ℝ) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta p.1 p.2 *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2))
      calc
        inner ℝ (K p) (E p) =
            inner ℝ
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H 2 beta p.1 p.2)
              ((-2 : ℝ) *
                Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)) :=
          congrArg₂ (fun a b : ℝ => inner ℝ a b) hk he
        _ = _ := by
          rw [periodicHypercubicEven_real_inner_eq_mul]
          ring
    _ = _ := integral_const_mul (-2 : ℝ) _

/-- Exact local signed remainder for the original physical fixed-Haar
response.  The coefficient 1/4 is ANV's computed original action moment. -/
theorem p4Q2PZ37AOC_originalFixedHaarResponse_eq_localTaylorIntegral
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) 0 (by norm_num))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) + beta * (1 / 4 : ℝ) =
      -(∫ p, (p4Q2PZ37AOC_originalKernelTaylorRemainder H beta p.1 p.2 -
        p4Q2PZ37AOC_originalKernelTaylorRemainder H beta p.1
          (p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) p.2)) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let pairMu := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let chi : Cfg × Cfg → ℝ := fun p =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)
  let S : Cfg × Cfg → ℝ := fun p =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 p.1 p.2
  let K : Cfg × Cfg → ℝ := fun p =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta p.1 p.2
  let R : Cfg × Cfg → ℝ := fun p =>
    p4Q2PZ37AOC_originalKernelTaylorRemainder H beta p.1 p.2
  have hChi : Continuous chi :=
    (p4Q2PZ37AOC_primaryCharacter_continuous H).comp continuous_snd
  have hK : Continuous K := p4Q2PZ37AOC_originalKernel_pair_continuous H beta
  have hS : Continuous S := p4Q2PZ37AOC_originalSlabAction_pair_continuous H
  have hChiInt : Integrable chi pairMu :=
    hChi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKInt : Integrable (fun p => K p * chi p) pairMu :=
    (hK.mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSInt : Integrable (fun p => S p * chi p) pairMu :=
    (hS.mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hChiZero : (∫ p, chi p ∂pairMu) = 0 := by
    have h := p4Q2PZ37AOC_originalFirstCharacter_pairHaar_antisymmetrization H
      (fun _ => (1 : ℝ)) continuous_const
    have hz : (-2 : ℝ) * (∫ p, chi p ∂pairMu) = 0 := by
      simpa only [one_mul, sub_self, zero_mul, integral_zero, neg_zero] using h
    linarith only [hz]
  have hSMoment : (∫ p, S p * chi p ∂pairMu) = -(1 / 8 : ℝ) := by
    calc
      _ = ∫ B : Cfg, (∫ A : Cfg,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B *
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) ∂mu) ∂mu := by
        change (∫ p, S p * chi p ∂(mu.prod mu)) = _
        exact MeasureTheory.integral_prod_symm (fun p => S p * chi p) hSInt
      _ = _ := p4Q2PZ37ANV_originalOneSlab_firstCharacter_iteratedHaar H
  have hRIntegral : (∫ p, R p * chi p ∂pairMu) =
      (∫ p, K p * chi p ∂pairMu) - beta / 8 := by
    calc
      _ = ∫ p, (K p * chi p - chi p) + beta * (S p * chi p) ∂pairMu := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [R, K, S, p4Q2PZ37AOC_originalKernelTaylorRemainder]
        ring
      _ = ((∫ p, K p * chi p ∂pairMu) - (∫ p, chi p ∂pairMu)) +
          beta * (∫ p, S p * chi p ∂pairMu) := by
        have hAdd :
            (∫ p, (K p * chi p - chi p) + beta * (S p * chi p) ∂pairMu) =
              (∫ p, K p * chi p - chi p ∂pairMu) +
                (∫ p, beta * (S p * chi p) ∂pairMu) := by
          simpa only [Pi.sub_apply] using
            (integral_add (hKInt.sub hChiInt) (hSInt.const_mul beta))
        have hSub :
            (∫ p, K p * chi p - chi p ∂pairMu) =
              (∫ p, K p * chi p ∂pairMu) - (∫ p, chi p ∂pairMu) :=
          integral_sub hKInt hChiInt
        rw [hAdd, hSub, integral_const_mul]
      _ = _ := by rw [hChiZero, hSMoment]; ring
  have hResponse :=
    p4Q2PZ37AOC_originalFixedHaarResponse_eq_kernelCharacter H beta hbeta
  calc
    _ = (-2 : ℝ) * (∫ p, R p * chi p ∂pairMu) := by
      rw [hResponse, hRIntegral]
      ring
    _ = _ := p4Q2PZ37AOC_originalFirstCharacter_pairHaar_antisymmetrization H R
      (p4Q2PZ37AOC_originalKernelTaylorRemainder_pair_continuous H beta)

private theorem p4Q2PZ37AOC_originalTaylorRemainder_centerTwist_abs_sub_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2PZ37AOC_originalKernelTaylorRemainder H beta A B -
      p4Q2PZ37AOC_originalKernelTaylorRemainder H beta A
        (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)| ≤
      8 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta^2 := by
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let B' := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B
  let x := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B
  let y := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B'
  have hx0 : 0 ≤ x :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B
  have hy0 : 0 ≤ y :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B'
  have hxC : x ≤ C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by norm_num) A B
  have hyC : y ≤ C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by norm_num) A B'
  have hxy : |x - y| ≤ 8 :=
    p4Q2PZ37AOC_originalSlabAction_sub_rightCenterTwist_abs_le_eight H _ A B
  have hC : 0 ≤ C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  unfold p4Q2PZ37AOC_originalKernelTaylorRemainder
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  change |(Real.exp (-beta * x) - 1 + beta * x) -
    (Real.exp (-beta * y) - 1 + beta * y)| ≤ 8 * C * beta^2
  calc
    _ ≤ (beta^2 * C) * |x - y| :=
      p4Q2PZ37AOC_real_expTaylorRemainder_abs_sub_le beta C x y
        hbeta hx0 hxC hy0 hyC
    _ ≤ (beta^2 * C) * 8 :=
      mul_le_mul_of_nonneg_left hxy (mul_nonneg (sq_nonneg beta) hC)
    _ = 8 * C * beta^2 := by ring

/-- Original fixed-Haar physical response: local center-flip cancellation
reduces the global quadratic-budget coefficient to 8*C_H, for every beta>=0. -/
theorem p4Q2PZ37AOC_originalFixedHaarResponse_localQuadraticError_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    |inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) 0 (by norm_num))
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) + beta * (1 / 4 : ℝ)| ≤
      8 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta^2 := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let f : Cfg × Cfg → ℝ := fun p =>
    (p4Q2PZ37AOC_originalKernelTaylorRemainder H beta p.1 p.2 -
      p4Q2PZ37AOC_originalKernelTaylorRemainder H beta p.1
        (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) p.2)) *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hpoint : ∀ p, ‖f p‖ ≤ 8 * C * beta^2 := by
    intro p
    rw [Real.norm_eq_abs]
    dsimp [f]
    rw [abs_mul]
    calc
      _ ≤ |p4Q2PZ37AOC_originalKernelTaylorRemainder H beta p.1 p.2 -
          p4Q2PZ37AOC_originalKernelTaylorRemainder H beta p.1
            (p4Q2PZ37ANV_singleLinkCenterTwist H
              (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) p.2)| * 1 :=
        mul_le_mul_of_nonneg_left
          (p4Q2PZ37AOC_primaryCharacter_abs_le_one H p.2) (abs_nonneg _)
      _ = _ := mul_one _
      _ ≤ 8 * C * beta^2 :=
        p4Q2PZ37AOC_originalTaylorRemainder_centerTwist_abs_sub_le H beta hbeta p.1 p.2
  rw [p4Q2PZ37AOC_originalFixedHaarResponse_eq_localTaylorIntegral H beta hbeta, abs_neg]
  change |∫ p, f p ∂mu| ≤ 8 * C * beta^2
  have h := norm_integral_le_of_norm_le_const (μ := mu) (f := f)
    (C := 8 * C * beta^2) (Eventually.of_forall hpoint)
  simpa [Real.norm_eq_abs] using h

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOC_originalKernelTaylorRemainder
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOC_real_expTaylorRemainder_abs_sub_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOC_originalFirstCharacter_pairHaar_antisymmetrization
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOC_originalFixedHaarResponse_eq_localTaylorIntegral
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOC_originalFixedHaarResponse_localQuadraticError_le

