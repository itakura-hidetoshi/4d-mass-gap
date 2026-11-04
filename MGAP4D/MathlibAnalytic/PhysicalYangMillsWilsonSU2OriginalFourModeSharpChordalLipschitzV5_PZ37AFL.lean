import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalChordalCellRadiusCertificatesV5_PZ37AFK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFL — unconditional sharp chordal control of original SU(2) Haar modes

AFK requires envelope and chordal Lipschitz bounds for the four genuine
Wilson fundamental Haar-character modes, in addition to independently
certified bounds for the full Wilson/Perron physical receiver.

The four original quaternion translates phi_j(g) are bounded by one
from the exact genuine four-mode identity sum_j phi_j(g)^2 = 1.
The original real-eight normalized SU(2) feature J gives
  chi(g) = <J(1), J(g)>,   ||J(1)|| = 1,
so original normalized Wilson character satisfies
  |chi(g)-chi(h)| <= d_J(g,h).
The exact ADK calibration d_J^2=2 E(g^-1 h) shows genuine LEFT
translation is an isometry; hence ALL four original quaternion modes
satisfy the SHARP unconditional bound
  |phi_j(g)-phi_j(h)| <= d_J(g,h).

AFL discharges AFK's character envelope and slope proof obligations
without assuming external arbitrary character constants. It defines
a reduced data structure for genuinely certified ORIGINAL receiver
bounds/slopes, actual SU(2) cell radii/masses, and finite rational
sample errors, and constructs the full AFK => AFJ => AFI => AFH typed
certificate and original AEA/AFD Haar shell-packing consequences.

The original receiver slope, Haar cell masses, radii, and actual
numerical samples remain independent physical certification problems.
No numeric physical threshold crossing, H-uniform coercivity, Hamiltonian
spectral gap, or continuum 4D Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "J" => specialUnitaryTwoNormalizedTraceFeatureVector
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter
local notation "mu" => normalizedCompactHaar G

local instance p4Q2PZ37AFL_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFL_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFL_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFL_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFL_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFL_probabilityG : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The original normalized Wilson fundamental character equals
the inner product with the REAL eight-coordinate identity feature. -/
theorem p4Q2PZ37AFL_originalCharacter_eq_identityFeature (g : G) :
    chi g = inner ℝ (J (1 : G)) (J g) := by
  calc
    chi g = normalizedSpecialUnitaryRealTrace 2 g := by
      unfold p4Q2PZ35C_originalOneLinkCharacter
      rw [specialUnitaryWilsonPlaquetteEnergy_eq]
      ring
    _ = specialUnitaryNormalizedTraceRelativeKernel 2 (1 : G) g := by
      simp [specialUnitaryNormalizedTraceRelativeKernel]
    _ = inner ℝ (J (1 : G)) (J g) :=
      specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector (1 : G) g

/-- The SAME genuine normalized original feature has unit norm at
the SU(2) group identity, with no external norm constant. -/
theorem p4Q2PZ37AFL_originalIdentityFeature_norm_one :
    ‖J (1 : G)‖ = 1 := by
  have hsq := p4Q2PZ37ADK_trueFeature_norm_sq_one (1 : G)
  nlinarith [norm_nonneg (J (1 : G))]

/-- Original normalized Wilson character is 1-Lipschitz for the
genuine calibrated ADK full matrix-feature chordal metric. -/
theorem p4Q2PZ37AFL_originalCharacter_chordal_oneLipschitz (g h : G) :
    |chi g - chi h| ≤ dJ g h := by
  have hIdentity :
      chi g - chi h = inner ℝ (J (1 : G)) (J g - J h) := by
    rw [p4Q2PZ37AFL_originalCharacter_eq_identityFeature g,
      p4Q2PZ37AFL_originalCharacter_eq_identityFeature h,
      inner_sub_right]
  calc
    |chi g - chi h| =
        |inner ℝ (J (1 : G)) (J g - J h)| :=
      congrArg abs hIdentity
    _ ≤ ‖J (1 : G)‖ * ‖J g - J h‖ :=
      abs_real_inner_le_norm _ _
    _ = dJ g h := by
      rw [p4Q2PZ37AFL_originalIdentityFeature_norm_one]
      simp [p4Q2PZ37ADK_trueChordalDistance]

/-- Left multiplication by any ACTUAL SU(2) group element is
an isometry of the ADK original calibrated chordal metric. -/
theorem p4Q2PZ37AFL_originalChordal_left_isometry
    (a g h : G) : dJ (a * g) (a * h) = dJ g h := by
  have hgroup : (a * g)⁻¹ * (a * h) = g⁻¹ * h := by group
  have hsq : (dJ (a * g) (a * h)) ^ 2 = (dJ g h) ^ 2 := by
    rw [p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy,
      p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy, hgroup]
  nlinarith [p4Q2PZ37ADK_trueChordalDistance_nonneg (a * g) (a * h),
    p4Q2PZ37ADK_trueChordalDistance_nonneg g h]

/-- Exact quaternion translations therefore have canonical chordal
Lipschitz coefficient ONE: no physical assumption or proxy mode. -/
theorem p4Q2PZ37AFL_originalFourMode_chordal_oneLipschitz
    (j : Fin 4) (g h : G) :
    |phi j g - phi j h| ≤ dJ g h := by
  change |chi (q j * g) - chi (q j * h)| ≤ dJ g h
  calc
    |chi (q j * g) - chi (q j * h)| ≤
        dJ (q j * g) (q j * h) :=
      p4Q2PZ37AFL_originalCharacter_chordal_oneLipschitz
        (q j * g) (q j * h)
    _ = dJ g h :=
      p4Q2PZ37AFL_originalChordal_left_isometry (q j) g h

/-- Each of the four actual Wilson/Haar modes has ABSOLUTE
envelope ONE, by the exact original sum-of-four-squares identity. -/
theorem p4Q2PZ37AFL_originalFourMode_abs_le_one
    (j : Fin 4) (g : G) : |phi j g| ≤ 1 := by
  have hTerm : (phi j g) ^ 2 ≤ ∑ k : Fin 4, (phi k g) ^ 2 := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun k : Fin 4 => (phi k g) ^ 2)
      (fun k _ => sq_nonneg (phi k g)) (Finset.mem_univ j)
  rw [p4Q2PZ37ACK_fourModeCharacter_sum_sq] at hTerm
  have hAbsSq : (|phi j g|) ^ 2 ≤ (1 : ℝ) := by
    simpa only [sq_abs] using hTerm
  nlinarith [abs_nonneg (phi j g)]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Shell" => p4Q2PZ37AFF_originalExceptionalShell H
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H

local instance p4Q2PZ37AFL_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFL_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- AFK witness reduced to genuinely unverified PHYSICAL receiver
bounds, real SU(2) cells/masses and rational numerical point errors.
The character constants are proved above and are NOT user inputs. -/
structure p4Q2PZ37AFL_originalReceiverOnlyCellSamples
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  partition : p4Q2PZ37AFJ_originalHaarCells
  center : Fin partition.n → G
  radius : ℝ
  hRadius : 0 ≤ radius
  hCellRadius : ∀ i (g : G), g ∈ partition.cell i →
    p4Q2PZ37ADK_trueChordalDistance g (center i) ≤ radius
  hThetaLo : 0 ≤ lo
  receiverEnvelope : Pair → ℝ
  hReceiverEnvelope_nonneg : ∀ a ∈ c.s, 0 ≤ receiverEnvelope a
  hReceiverBound : ∀ a ∈ c.s, ∀ g : G,
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a g| ≤ receiverEnvelope a
  receiverSlope : Pair → ℝ
  hReceiverSlope_nonneg : ∀ a ∈ c.s, 0 ≤ receiverSlope a
  hReceiverSlope : ∀ a ∈ c.s, ∀ g h : G,
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a g -
     p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a h| ≤
      receiverSlope a * p4Q2PZ37ADK_trueChordalDistance g h
  meanSample : Pair → Fin partition.n → ℚ
  meanSampleError : Pair → ℝ
  hMeanSampleError_nonneg : ∀ a ∈ c.s, 0 ≤ meanSampleError a
  hMeanSample : ∀ a ∈ c.s, ∀ i,
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a (center i) -
        (meanSample a i : ℝ)| ≤ meanSampleError a
  secondSample : Pair → Fin partition.n → ℚ
  secondSampleError : Pair → ℝ
  hSecondSampleError_nonneg : ∀ a ∈ c.s, 0 ≤ secondSampleError a
  hSecondSample : ∀ a ∈ c.s, ∀ i,
    |(p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a (center i))^2 -
       (secondSample a i : ℝ)| ≤ secondSampleError a
  coefficientSample : Pair → Fin 4 → Fin partition.n → ℚ
  coefficientSampleError : Pair → Fin 4 → ℝ
  hCoefficientSampleError_nonneg : ∀ a ∈ c.s, ∀ j,
    0 ≤ coefficientSampleError a j
  hCoefficientSample : ∀ a ∈ c.s, ∀ j i,
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a (center i) *
       p4Q2PZ37ACK_fourModeCharacter j (center i) -
       (coefficientSample a j i : ℝ)| ≤ coefficientSampleError a j

/-- Actual type-preserving AFK certificate, with proof-derived SHARP
character envelope and chordal slope equal to one, for all four modes. -/
def p4Q2PZ37AFL_toOriginalChordalCellSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c) :
    p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c where
  partition := d.partition
  center := d.center
  radius := d.radius
  hRadius := d.hRadius
  hCellRadius := d.hCellRadius
  hThetaLo := d.hThetaLo
  receiverEnvelope := d.receiverEnvelope
  hReceiverEnvelope_nonneg := d.hReceiverEnvelope_nonneg
  hReceiverBound := d.hReceiverBound
  receiverSlope := d.receiverSlope
  hReceiverSlope_nonneg := d.hReceiverSlope_nonneg
  hReceiverSlope := d.hReceiverSlope
  characterEnvelope := fun _ => 1
  characterSlope := fun _ => 1
  hCharacterEnvelope_nonneg := by intro j; norm_num
  hCharacterSlope_nonneg := by intro j; norm_num
  hCharacterBound := by
    intro j g
    exact p4Q2PZ37AFL_originalFourMode_abs_le_one j g
  hCharacterSlope := by
    intro j g h
    simpa only [one_mul] using
      p4Q2PZ37AFL_originalFourMode_chordal_oneLipschitz j g h
  meanSample := d.meanSample
  meanSampleError := d.meanSampleError
  hMeanSampleError_nonneg := d.hMeanSampleError_nonneg
  hMeanSample := d.hMeanSample
  secondSample := d.secondSample
  secondSampleError := d.secondSampleError
  hSecondSampleError_nonneg := d.hSecondSampleError_nonneg
  hSecondSample := d.hSecondSample
  coefficientSample := d.coefficientSample
  coefficientSampleError := d.coefficientSampleError
  hCoefficientSampleError_nonneg := d.hCoefficientSampleError_nonneg
  hCoefficientSample := d.hCoefficientSample

/-- The four actual AFK coefficient error radii now require only
the SAME physical receiver's slope L_F and envelope M_F:
  deltaCoeff_j = (L_F+M_F)*r + epsilon_j.
This is an equality of the *actual certificate formulae*. -/
theorem p4Q2PZ37AFL_canonicalCoefficientOscillation_eq
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c)
    (a : Pair) (j : Fin 4) :
    p4Q2PZ37AFK_coefficientOscillation H e c
      (p4Q2PZ37AFL_toOriginalChordalCellSamples H e c d) a j =
    (d.receiverSlope a + d.receiverEnvelope a) * d.radius +
      d.coefficientSampleError a j := by
  simp [p4Q2PZ37AFK_coefficientOscillation,
    p4Q2PZ37AFL_toOriginalChordalCellSamples]

/-- Build the same genuine AFJ normalized Haar integral witness from
the reduced ORIGINAL receiver-only physical certification workload. -/
def p4Q2PZ37AFL_toOriginalReceiverQuadrature
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c) :
    p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c :=
  p4Q2PZ37AFK_toOriginalReceiverQuadrature H e c
    (p4Q2PZ37AFL_toOriginalChordalCellSamples H e c d)

/-- The AFJ quadrature gives the same verified ORIGINAL AFI coefficient
and variance certificate for the unchanged SU(2) Wilson/Perron source. -/
def p4Q2PZ37AFL_toOriginalCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFK_toOriginalCoefficientVarianceCertificate H e c
    (p4Q2PZ37AFL_toOriginalChordalCellSamples H e c d)

/-- The strict original shell center filter, with no guessed
character slope or independent proxy SU(2) Haar measure. -/
def p4Q2PZ37AFL_originalReceiverOnlyShellCenters
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c) :
    Finset Pair :=
  p4Q2PZ37AFK_originalChordalShellCenters H e c
    (p4Q2PZ37AFL_toOriginalChordalCellSamples H e c d)

/-- Every certified reduced input with a passing center forces BOTH
authentic original Wilson/Perron residual gap signs, not a proxy crossing. -/
theorem p4Q2PZ37AFL_originalReceiverOnlyCenter_trueSigns
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFL_originalReceiverOnlyShellCenters H e c d) :
    c.etaLo < Gap e lo a ∧ Gap e hi a < -c.etaHi :=
  p4Q2PZ37AFK_originalChordalCenter_trueSigns H e c
    (p4Q2PZ37AFL_toOriginalChordalCellSamples H e c d) a ha

/-- A passing reduced certificate gives TRUE original boundary pair-Haar
shell mass, using the unchanged AEA floor. -/
theorem p4Q2PZ37AFL_originalReceiverOnlyCenter_positiveHaarShell
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFL_originalReceiverOnlyShellCenters H e c d) :
    0 < Measure.real outer (Shell e lo hi) :=
  p4Q2PZ37AFK_originalChordalCenter_positiveHaarShell H e c
    (p4Q2PZ37AFL_toOriginalChordalCellSamples H e c d) a ha

/-- The same genuine AFD finite greedy separated packing and its
explicit H-dependent Haar floor remain valid from reduced input. -/
theorem p4Q2PZ37AFL_originalReceiverOnlyPacking_exists
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c) :
    ∃ t : Finset Pair,
      t ⊆ p4Q2PZ37AFL_originalReceiverOnlyShellCenters H e c d ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b) ∧
      (∀ a ∈ p4Q2PZ37AFL_originalReceiverOnlyShellCenters H e c d,
        ∃ b ∈ t, D a b < 2 * c.r) ∧
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) :=
  p4Q2PZ37AFK_originalChordalPacking_exists H e c
    (p4Q2PZ37AFL_toOriginalChordalCellSamples H e c d)

/-- Strict crossing is impossible at zero true physical four-mode
amplitude or coincident original residual-ratio thresholds. -/
theorem p4Q2PZ37AFL_originalReceiverOnlyCenter_thresholdObstruction
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFL_originalReceiverOnlyShellCenters H e c d) :
    0 < (p4Q2PZ37ACM_originalCovarianceAmplitude H b0 hb0 e a)^2 ∧
      lo < hi :=
  p4Q2PZ37AFK_originalChordalCenter_thresholdObstruction H e c
    (p4Q2PZ37AFL_toOriginalChordalCellSamples H e c d) a ha

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFL_originalCharacter_eq_identityFeature
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFL_originalIdentityFeature_norm_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFL_originalCharacter_chordal_oneLipschitz
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFL_originalChordal_left_isometry
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFL_originalFourMode_chordal_oneLipschitz
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFL_originalFourMode_abs_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFL_canonicalCoefficientOscillation_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFL_originalReceiverOnlyCenter_trueSigns
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFL_originalReceiverOnlyCenter_positiveHaarShell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFL_originalReceiverOnlyPacking_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFL_originalReceiverOnlyCenter_thresholdObstruction
