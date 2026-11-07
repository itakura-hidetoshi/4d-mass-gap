import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAlignedPositiveSpatialHaarMassV5_PZ37AHL
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHM — Borel true-Haar aligned region and positive-part moment

AHL proves that for every finite original spatial H there is a STRICT
positive rational q and an original spatial all-link chordal ball of
true positive Haar mass on which f_H(B)*T_H(B)>q. The same original
centered ZW spatial Wilson source f_H, FULL fixed-beta Wilson
one-slab signed transfer T_H, and original normalized spatial
product-Haar μ_H are preserved.

This append-only proof makes the Borel/measure-theoretic side explicit.
The original product f_H*T_H has a finite explicit chordal modulus
from AHL. The very same genuine SU(2) product topology therefore
makes every real strict superlevel set OPEN (hence Borel), and the
product itself is a true Haar-measurable function.

The original source and transfer half-plaquette amplitude bounds yield

 |f_H(B)*T_H(B)| <= p_H^2/4.

On the unchanged finite Haar probability law, the positive part
max(f_H*T_H,0) is integrable and nonnegative. AHL's genuine spatial
ball floor and the strict rational q imply a quantitative bound

  0 < q * κ(R/(card(Link_H)+1))^card(Link_H)
       <= ∫_Cfg max(f_H(B)*T_H(B),0) dμ_H(B).

This is a FIRST nonnegative Haar correlation moment: negative
contributions are not discarded from the original SIGNED correlation,
which is a separate AHK object. The mass floor and positive part
are computed from the exact same original action-transfer function
and true original product-Haar.

R, q, the boundary, sign branch and numerical true-Haar mass values
remain existential: the result is not an evaluated numeric sign table.
No individual both-sign shell, H-uniform coercivity, Hamiltonian
spectral gap or 4D continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "J" => specialUnitaryTwoNormalizedTraceFeatureVector

local instance p4Q2PZ37AHM_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHM_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHM_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHM_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHM_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "kappa" => p4Q2PZ37ADQ_sphereRadiusFraction

local instance p4Q2PZ37AHM_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHM_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Original spatial all-link chordal distance to any genuine center
is continuous in the ORIGINAL product topology, via the original
ADK SU(2) real-eight Wilson feature J. -/
theorem p4Q2PZ37AHM_originalSpatialDistance_continuous
    (B : Cfg) :
    Continuous (fun C : Cfg => Dsp B C) := by
  unfold p4Q2PZ37AGG_originalSpatialChordalDistance
  apply continuous_finset_sum
  intro e _he
  change Continuous (fun C : Cfg => ‖J (B e) - J (C e)‖)
  exact (continuous_const.sub
    (p4Q2PZ37ADK_trueFeature_continuous.comp
      (continuous_apply e))).norm

/-- AHL's genuine chordal all-link ball is OPEN; no discrete or
surrogate spatial topology is introduced. -/
theorem p4Q2PZ37AHM_originalSpatialBall_isOpen
    (B : Cfg) (R : ℝ) :
    IsOpen (p4Q2PZ37AHL_originalSpatialBall H B R) :=
  isOpen_lt (p4Q2PZ37AHM_originalSpatialDistance_continuous H B)
    continuous_const

/-- A real threshold keeps the same ORIGINAL physical f_H*T_H
function; this extends AHL's rational superlevel presentation solely
to make Borel measurability transparent. -/
def p4Q2PZ37AHM_originalRealAlignedRegion (q : ℝ) : Set Cfg :=
  {C | q < fCont C * t C}

/-- Every strict real superlevel of the original signed correlation
product is OPEN, using AHL's proved quantitative spatial Lipschitz
bound and actual SU(2) chordal open balls. -/
theorem p4Q2PZ37AHM_originalRealAlignedRegion_isOpen
    (q : ℝ) :
    IsOpen (p4Q2PZ37AHM_originalRealAlignedRegion H q) := by
  rw [isOpen_iff_mem_nhds]
  intro B hB
  change q < fCont B * t B at hB
  let L : ℝ := p4Q2PZ37AHL_productSlope H
  have hL : 0 ≤ L := p4Q2PZ37AHL_productSlope_nonneg H
  let R : ℝ := (fCont B * t B - q) / (L + 1)
  have hDen : 0 < L + 1 := by linarith only [hL]
  have hAmp : 0 < fCont B * t B - q := sub_pos.mpr hB
  have hR : 0 < R := div_pos hAmp hDen
  have hEq : R * (L + 1) = fCont B * t B - q := by
    dsimp [R]
    field_simp
  have hScale : L * R < fCont B * t B - q := by
    nlinarith only [hEq, hR]
  have hCenter : B ∈ p4Q2PZ37AHL_originalSpatialBall H B R := by
    change Dsp B B < R
    have hSelf : Dsp B B = 0 := by
      unfold p4Q2PZ37AGG_originalSpatialChordalDistance
      simp [p4Q2PZ37ADK_trueChordalDistance_self]
    rw [hSelf]
    exact hR
  have hSub :
      p4Q2PZ37AHL_originalSpatialBall H B R ⊆
        p4Q2PZ37AHM_originalRealAlignedRegion H q := by
    intro C hC
    change q < fCont C * t C
    have hLip : |fCont B * t B - fCont C * t C| ≤ L * Dsp B C :=
      p4Q2PZ37AHL_originalProduct_allLinkSlope H B C
    have hSmall : L * Dsp B C < fCont B * t B - q :=
      (mul_le_mul_of_nonneg_left (le_of_lt hC) hL).trans_lt hScale
    have hDelta := (abs_le.mp hLip).2
    linarith only [hSmall, hDelta]
  exact Filter.mem_of_superset
    ((p4Q2PZ37AHM_originalSpatialBall_isOpen H B R).mem_nhds hCenter)
    hSub

/-- AHL's true rational-margin region is Borel under the ORIGINAL
spatial product-Haar measurable-space structure. -/
theorem p4Q2PZ37AHM_originalAlignedRegion_isOpen (q : ℚ) :
    IsOpen (p4Q2PZ37AHL_originalAlignedRegion H q) :=
  p4Q2PZ37AHM_originalRealAlignedRegion_isOpen H (q : ℝ)

theorem p4Q2PZ37AHM_originalAlignedRegion_measurableSet (q : ℚ) :
    MeasurableSet (p4Q2PZ37AHL_originalAlignedRegion H q) :=
  (p4Q2PZ37AHM_originalAlignedRegion_isOpen H q).measurableSet

/-- True Borel measurability follows from the proved openness of ALL
real superlevel sets, not from an assumed integral kernel regularity. -/
theorem p4Q2PZ37AHM_originalSignedProduct_measurable :
    Measurable (fun C : Cfg => fCont C * t C) := by
  apply measurable_of_Ioi
  intro q
  change MeasurableSet (p4Q2PZ37AHM_originalRealAlignedRegion H q)
  exact (p4Q2PZ37AHM_originalRealAlignedRegion_isOpen H q).measurableSet

/-- Global pointwise envelope of the same original signed product,
using genuine AGN source and AHJ transfer half-plaquette bounds. -/
theorem p4Q2PZ37AHM_originalSignedProduct_abs_le_quarterCount
    (B : Cfg) :
    |fCont B * t B| ≤ pH ^ 2 / 4 := by
  have hf : |fCont B| ≤ pH / 2 :=
    p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H B
  have ht : |t B| ≤ pH / 2 :=
    p4Q2PZ37AHJ_originalTransfer_abs_le_halfCount H B
  have hpHalf : 0 ≤ pH / 2 := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  calc
    |fCont B * t B| = |fCont B| * |t B| := abs_mul _ _
    _ ≤ (pH / 2) * (pH / 2) :=
      mul_le_mul hf ht (abs_nonneg _) hpHalf
    _ = pH ^ 2 / 4 := by ring

/-- The genuine signed action-transfer product is integrable under
the SAME original finite Haar probability; it is not replaced by
its unsigned or positive-part values. -/
theorem p4Q2PZ37AHM_originalSignedProduct_integrable :
    Integrable (fun B : Cfg => fCont B * t B) muH := by
  apply Integrable.of_bound
    (p4Q2PZ37AHM_originalSignedProduct_measurable H).aestronglyMeasurable
    (pH ^ 2 / 4)
  filter_upwards with B
  simpa only [Real.norm_eq_abs] using
    p4Q2PZ37AHM_originalSignedProduct_abs_le_quarterCount H B

/-- A nonnegative, original-Haar-integrable positive part of the
TRUE signed correlation product; no sign of T_H alone is assumed. -/
theorem p4Q2PZ37AHM_originalPositivePart_integrable :
    Integrable (fun B : Cfg => max (fCont B * t B) 0) muH := by
  have hMeas : Measurable (fun B : Cfg => max (fCont B * t B) 0) :=
    (p4Q2PZ37AHM_originalSignedProduct_measurable H).max measurable_const
  apply Integrable.of_bound hMeas.aestronglyMeasurable (pH ^ 2 / 4)
  filter_upwards with B
  have hPos : 0 ≤ max (fCont B * t B) 0 := le_max_right _ _
  have hHi : max (fCont B * t B) 0 ≤ pH ^ 2 / 4 :=
    max_le_iff.mpr ⟨
      (le_abs_self _).trans
        (p4Q2PZ37AHM_originalSignedProduct_abs_le_quarterCount H B),
      by positivity⟩
  rw [Real.norm_eq_abs, abs_of_nonneg hPos]
  exact hHi

/-- The original positive-part Haar moment is an actual first
nonnegative scalar moment of f_H*T_H, distinct from AHK's signed
Haar quadratic pairing and not a substituted transfer. -/
def p4Q2PZ37AHM_originalPositivePartHaarMoment : ℝ :=
  ∫ B : Cfg, max (fCont B * t B) 0 ∂muH

theorem p4Q2PZ37AHM_originalPositivePartHaarMoment_nonneg :
    0 ≤ p4Q2PZ37AHM_originalPositivePartHaarMoment H := by
  unfold p4Q2PZ37AHM_originalPositivePartHaarMoment
  exact integral_nonneg (fun _ => le_max_right _ _)

/-- AHL's positive-mass strict rational superlevel quantitatively
forces a nonzero FIRST positive-part Haar moment. No cancellation
is silently applied to the original signed integral. -/
theorem p4Q2PZ37AHM_exists_explicitPositivePartMomentFloor :
    ∃ q : ℚ, 0 < q ∧
      ∃ B : Cfg, ∃ R : ℝ, 0 < R ∧
        (∀ C ∈ p4Q2PZ37AHL_originalSpatialBall H B R,
          (q : ℝ) < fCont C * t C) ∧
        (q : ℝ) *
            p4Q2PZ37ADQ_sphereRadiusFraction
              (R / ((Fintype.card Link : ℝ) + 1)) ^ Fintype.card Link ≤
          p4Q2PZ37AHM_originalPositivePartHaarMoment H ∧
        0 < p4Q2PZ37AHM_originalPositivePartHaarMoment H := by
  obtain ⟨q, hq, B, R, hR, hStable, hMass, _hPos⟩ :=
    p4Q2PZ37AHL_exists_rationalAlignedRegion_positiveHaarMass H
  let A : Set Cfg := p4Q2PZ37AHL_originalAlignedRegion H q
  have hMeas : MeasurableSet A :=
    p4Q2PZ37AHM_originalAlignedRegion_measurableSet H q
  have hPosInt := p4Q2PZ37AHM_originalPositivePart_integrable H
  have hQreal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hMonotone :
      (∫ C in A, (q : ℝ) ∂muH) ≤
        ∫ C in A, max (fCont C * t C) 0 ∂muH := by
    apply setIntegral_mono_on integrableOn_const hPosInt.integrableOn hMeas
    intro C hC
    change (q : ℝ) < fCont C * t C at hC
    exact (le_of_lt hC).trans (le_max_left _ _)
  have hMonotone' :
      (q : ℝ) * Measure.real muH A ≤
        ∫ C in A, max (fCont C * t C) 0 ∂muH := by
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hMonotone
  have hWhole :
      (∫ C in A, max (fCont C * t C) 0 ∂muH) ≤
        p4Q2PZ37AHM_originalPositivePartHaarMoment H := by
    unfold p4Q2PZ37AHM_originalPositivePartHaarMoment
    exact setIntegral_le_integral hPosInt
      (ae_of_all _ (fun C => le_max_right (fCont C * t C) 0))
  have hFloor :
      (q : ℝ) * kappa
          (R / ((Fintype.card Link : ℝ) + 1)) ^ Fintype.card Link ≤
        p4Q2PZ37AHM_originalPositivePartHaarMoment H := by
    calc
      (q : ℝ) * kappa
          (R / ((Fintype.card Link : ℝ) + 1)) ^ Fintype.card Link ≤
        (q : ℝ) * Measure.real muH A :=
          mul_le_mul_of_nonneg_left hMass hQreal.le
      _ ≤ ∫ C in A, max (fCont C * t C) 0 ∂muH := hMonotone'
      _ ≤ p4Q2PZ37AHM_originalPositivePartHaarMoment H := hWhole
  have hStrict :
      0 < p4Q2PZ37AHM_originalPositivePartHaarMoment H := by
    have hPosRadius :
        0 < kappa (R / ((Fintype.card Link : ℝ) + 1)) := by
      exact p4Q2PZ37ADQ_sphereRadiusFraction_pos _
    exact lt_of_lt_of_le (mul_pos hQreal (pow_pos hPosRadius _)) hFloor
  exact ⟨q, hq, B, R, hR, hStable, hFloor, hStrict⟩

/-- UNCONDITIONAL strictly positive true original spatial-Haar
first moment of the positive part of f_H*T_H for every finite H. -/
theorem p4Q2PZ37AHM_originalPositivePartHaarMoment_pos :
    0 < p4Q2PZ37AHM_originalPositivePartHaarMoment H := by
  obtain ⟨_q, _hq, _B, _R, _hR, _hStable, _hFloor, hPos⟩ :=
    p4Q2PZ37AHM_exists_explicitPositivePartMomentFloor H
  exact hPos

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalSpatialDistance_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalSpatialBall_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalRealAlignedRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalAlignedRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalAlignedRegion_measurableSet
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalSignedProduct_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalSignedProduct_abs_le_quarterCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalSignedProduct_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalPositivePart_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalPositivePartHaarMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_exists_explicitPositivePartMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHM_originalPositivePartHaarMoment_pos
