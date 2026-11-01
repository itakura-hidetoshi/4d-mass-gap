import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalBoundaryHaarCylindersV5_PZ37ADJ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeNormalizedTraceHilbertPowerPullback
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullbackL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADK — calibrated original SU(2) feature-chordal Haar balls

The original genuine normalized SU(2) matrix-realification Hilbert feature
J(g) of the normalized relative trace is retained from the existing
Wilson cyclic-four-edge construction. Its chordal distance is
d_J(g,h)=||J(g)-J(h)||, and we prove the EXACT physical calibration

    d_J(g,h)^2 = 2*E_SU2(g^-1*h).

It is nonnegative, symmetric, satisfies the triangle inequality and
generates OPEN subsets in the ORIGINAL SU(2) topology. This is a
quantitatively calibrated feature pseudometric; no arbitrary
ADH pseudoMetrizableSpacePseudoMetric and no replacement probability
law are used. Separation by J can be certified independently.

The genuine ABV quaternion eight-translate theorem gives
μ{E(g)<=1/2} >= 1/8. For EVERY genuine SU(2) center a and EVERY
real radius r>1, the translated closed Wilson cap is INSIDE the
explicit feature-chordal open ball B_J(a,r). Exact normalized compact
Haar invariance proves μ(B_J(a,r)) >= 1/8 > 1/17.

Map this SAME calibrated one-link feature ball to the unchanged
finite-H original boundary pair-Haar ν_H by the genuine
measure-preserving coordinate projections. All links, centers and
H share the exact numeric one-coordinate ball floor, and ACI's
original nonzero covariance witness is itself the ball center.
For TWO genuine boundary coordinates, the pair product-Haar ball
rectangle has an explicit ≥1/64 lower mass.

These are true physical coordinate-cylinder evaluations. The full
all-link metric ball and a pointwise covariance lower bound throughout
the large cylinder are NOT inferred. A genuine receiver Lipschitz
bound and actual amplitude estimate, ADH numeric 68 inequality,
H-uniform coercivity and continuum 4D mass gap remain OPEN.
Append-only, same original source, Perron/transfer, receiver,
two interacting posteriors and boundary pair-Haar.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "haar" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "J" => specialUnitaryTwoNormalizedTraceFeatureVector

local instance p4Q2PZ37ADK_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADK_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADK_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADK_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADK_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADK_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The REAL eight-coordinate normalized SU(2) matrix feature has
unit squared Hilbert norm, by the SAME normalized trace kernel. -/
theorem p4Q2PZ37ADK_trueFeature_norm_sq_one (g : G) :
    ‖J g‖ ^ 2 = 1 := by
  calc
    ‖J g‖ ^ 2 = inner ℝ (J g) (J g) :=
      (real_inner_self_eq_norm_sq (J g)).symm
    _ = specialUnitaryNormalizedTraceRelativeKernel 2 g g :=
      (specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector g g).symm
    _ = 1 := specialUnitaryNormalizedTraceRelativeKernel_self 2 (by norm_num) g

/-- EXACT calibrated squared Euclidean chord on the genuine original
matrix feature, in terms of the original SU(2) Wilson energy. -/
theorem p4Q2PZ37ADK_trueFeature_chord_sq_eq_twiceWilsonEnergy
    (g h : G) :
    ‖J g - J h‖ ^ 2 = 2 * E (g⁻¹ * h) := by
  calc
    ‖J g - J h‖ ^ 2 =
        ‖J g‖ ^ 2 - 2 * inner ℝ (J g) (J h) + ‖J h‖ ^ 2 := by
      rw [norm_sub_sq_real]
    _ = 1 - 2 * specialUnitaryNormalizedTraceRelativeKernel 2 g h + 1 := by
      rw [p4Q2PZ37ADK_trueFeature_norm_sq_one,
        p4Q2PZ37ADK_trueFeature_norm_sq_one,
        ← specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector]
    _ = 2 * E (g⁻¹ * h) := by
      unfold specialUnitaryNormalizedTraceRelativeKernel
      rw [specialUnitaryWilsonPlaquetteEnergy_eq]
      ring

/-- Calibrated chordal distance in the original normalized real-eight
matrix feature. It is a concrete formula, not the uncalibrated ADH
existence-only pseudometric. -/
def p4Q2PZ37ADK_trueChordalDistance (g h : G) : ℝ :=
  ‖J g - J h‖

theorem p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy (g h : G) :
    (p4Q2PZ37ADK_trueChordalDistance g h) ^ 2 =
      2 * E (g⁻¹ * h) :=
  p4Q2PZ37ADK_trueFeature_chord_sq_eq_twiceWilsonEnergy g h

theorem p4Q2PZ37ADK_trueChordalDistance_nonneg (g h : G) :
    0 ≤ p4Q2PZ37ADK_trueChordalDistance g h :=
  norm_nonneg _

theorem p4Q2PZ37ADK_trueChordalDistance_self (g : G) :
    p4Q2PZ37ADK_trueChordalDistance g g = 0 := by
  simp [p4Q2PZ37ADK_trueChordalDistance]

theorem p4Q2PZ37ADK_trueChordalDistance_symm (g h : G) :
    p4Q2PZ37ADK_trueChordalDistance g h =
      p4Q2PZ37ADK_trueChordalDistance h g := by
  simpa [p4Q2PZ37ADK_trueChordalDistance] using
    (norm_sub_rev (J g) (J h))

theorem p4Q2PZ37ADK_trueChordalDistance_triangle (g h k : G) :
    p4Q2PZ37ADK_trueChordalDistance g k ≤
      p4Q2PZ37ADK_trueChordalDistance g h +
        p4Q2PZ37ADK_trueChordalDistance h k := by
  change ‖J g - J k‖ ≤ ‖J g - J h‖ + ‖J h - J k‖
  calc
    ‖J g - J k‖ = ‖(J g - J h) + (J h - J k)‖ := by
      congr 1
      abel
    _ ≤ ‖J g - J h‖ + ‖J h - J k‖ := norm_add_le _ _

/-- Continuity of the exact explicit normalized real-eight matrix
feature in the unchanged SU(2) topology. -/
theorem p4Q2PZ37ADK_trueFeature_continuous :
    Continuous (fun g : G => J g) := by
  have hEq :
      (fun g : G => J g) =
        specialUnitaryTwoNormalizedTraceHilbertKernelFeature.feature := by
    funext g
    exact specialUnitaryTwoNormalizedTraceFeatureVector_eq_kernelFeature g
  rw [hEq]
  exact RealHilbertKernelFeature.continuous_feature_of_continuous_kernel
    specialUnitaryTwoNormalizedTraceHilbertKernelFeature
    (continuous_specialUnitaryNormalizedTraceRelativeKernel 2)

/-- A genuine open SU(2) chordal feature-ball at a variable physical
center and a NUMERIC radius in the normalized Hilbert metric. -/
def p4Q2PZ37ADK_trueChordalBall (a : G) (r : ℝ) : Set G :=
  {g | p4Q2PZ37ADK_trueChordalDistance a g < r}

theorem p4Q2PZ37ADK_trueChordalBall_isOpen (a : G) (r : ℝ) :
    IsOpen (p4Q2PZ37ADK_trueChordalBall a r) := by
  have hCont :
      Continuous (fun g : G => ‖J a - J g‖) :=
    (continuous_const.sub p4Q2PZ37ADK_trueFeature_continuous).norm
  exact isOpen_lt hCont continuous_const

theorem p4Q2PZ37ADK_trueChordalBall_mem_center (a : G) (r : ℝ)
    (hr : 0 < r) :
    a ∈ p4Q2PZ37ADK_trueChordalBall a r := by
  simpa [p4Q2PZ37ADK_trueChordalBall,
    p4Q2PZ37ADK_trueChordalDistance] using hr

/-- Original SU(2) Haar low-energy cap left translated to a
SPECIFIC physical SU(2) center, without changing the measure. -/
def p4Q2PZ37ADK_translatedOriginalLowCap (a : G) : Set G :=
  (fun g : G => a⁻¹ * g) ⁻¹' p4Q2PZ37ABV_lowEnergyCap

/-- ORIGINAL Wilson low-energy cap lies in a genuine calibrated
chordal ball of ANY explicit radius r>1; this follows from
d_J²=2E and E<=1/2, not from qualitative continuity. -/
theorem p4Q2PZ37ADK_translatedLowCap_subset_chordalBall
    (a : G) (r : ℝ) (hr : 1 < r) :
    p4Q2PZ37ADK_translatedOriginalLowCap a ⊆
      p4Q2PZ37ADK_trueChordalBall a r := by
  intro g hg
  have hEnergy : E (a⁻¹ * g) ≤ (1 / 2 : ℝ) := hg
  have hSq :=
    p4Q2PZ37ADK_trueFeature_chord_sq_eq_twiceWilsonEnergy a g
  have hNonneg : 0 ≤ ‖J a - J g‖ := norm_nonneg _
  have hNorm : ‖J a - J g‖ ≤ 1 := by
    nlinarith
  exact lt_of_le_of_lt hNorm hr

theorem p4Q2PZ37ADK_translatedOriginalLowCap_mass_eq (a : G) :
    Measure.real haar (p4Q2PZ37ADK_translatedOriginalLowCap a) =
      Measure.real haar p4Q2PZ37ABV_lowEnergyCap := by
  have hp : MeasurePreserving
      (fun g : G => a⁻¹ * g) (normalizedCompactHaar G) (normalizedCompactHaar G) := by
    simpa only [mul_one] using
      (normalizedCompactHaar_measurePreserving_mul_left_right G a⁻¹ (1 : G))
  change Measure.real haar
    ((fun g : G => a⁻¹ * g) ⁻¹' p4Q2PZ37ABV_lowEnergyCap) =
      Measure.real haar p4Q2PZ37ABV_lowEnergyCap
  simp only [measureReal_def]
  rw [hp.measure_preimage p4Q2PZ37ABV_lowEnergyCap_measurable.nullMeasurableSet]

/-- This is an EXPLICIT SU(2) NUMERICAL BALL MASS LOWER BOUND:
all centers a, and all radii r>1, have genuine normalized Haar
mass at least 1/8. The bound holds for the same actual continuous
SU(2) Haar probability, never a discrete approximation. -/
theorem p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth
    (a : G) (r : ℝ) (hr : 1 < r) :
    (1 / 8 : ℝ) ≤
      Measure.real haar (p4Q2PZ37ADK_trueChordalBall a r) := by
  calc
    (1 / 8 : ℝ) ≤ Measure.real haar p4Q2PZ37ABV_lowEnergyCap :=
      p4Q2PZ37ABV_lowEnergyCap_real_mass_lower
    _ = Measure.real haar (p4Q2PZ37ADK_translatedOriginalLowCap a) :=
      (p4Q2PZ37ADK_translatedOriginalLowCap_mass_eq a).symm
    _ ≤ Measure.real haar (p4Q2PZ37ADK_trueChordalBall a r) :=
      measureReal_mono (p4Q2PZ37ADK_translatedLowCap_subset_chordalBall a r hr)

/-- A NUMERIC 5/4-radius genuine chordal ball at every group center
crosses ADI's Haar-mass >1/17 NECESSARY geometric filter. -/
theorem p4Q2PZ37ADK_trueChordalBall_radiusFiveFour_mass_gt_seventeenth
    (a : G) :
    (1 / 17 : ℝ) <
      Measure.real haar (p4Q2PZ37ADK_trueChordalBall a (5 / 4)) := by
  have h :=
    p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth a (5 / 4) (by norm_num)
  linarith

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "slice" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local instance p4Q2PZ37ADK_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADK_sliceProbability : IsProbabilityMeasure slice := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ADK_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

private theorem p4Q2PZ37ADK_leftCoordinateMP
    (e : Link) :
    MeasurePreserving (fun z : Pair => z.1 e) outer (normalizedCompactHaar G) := by
  have hLeft : MeasurePreserving (fun z : Pair => z.1) outer slice := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    exact MeasureTheory.measurePreserving_fst
  have hEval : MeasurePreserving (fun x : Cfg => x e) slice (normalizedCompactHaar G) := by
    simpa only [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (fun _ : Link => normalizedCompactHaar G) e)
  simpa only [Function.comp_def] using hEval.comp hLeft

/-- Genuine ORIGINAL finite-H pair-Haar cylinder in a numerical
normalized-matrix-Hilbert chordal ball around a specified SU(2) center. -/
def p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder
    (e : Link) (a : G) (r : ℝ) : Set Pair :=
  {z | z.1 e ∈ p4Q2PZ37ADK_trueChordalBall a r}

theorem p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_isOpen
    (e : Link) (a : G) (r : ℝ) :
    IsOpen (p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder H e a r) := by
  have hEval : Continuous (fun z : Pair => z.1 e) :=
    (continuous_apply e).comp continuous_fst
  exact (p4Q2PZ37ADK_trueChordalBall_isOpen a r).preimage hEval

theorem p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_mass_eq
    (e : Link) (a : G) (r : ℝ) :
    Measure.real outer (p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder H e a r) =
      Measure.real haar (p4Q2PZ37ADK_trueChordalBall a r) := by
  have hp := p4Q2PZ37ADK_leftCoordinateMP H e
  change Measure.real outer
      ((fun z : Pair => z.1 e) ⁻¹' p4Q2PZ37ADK_trueChordalBall a r) =
    Measure.real haar (p4Q2PZ37ADK_trueChordalBall a r)
  simp only [measureReal_def]
  rw [hp.measure_preimage
    (p4Q2PZ37ADK_trueChordalBall_isOpen a r).measurableSet.nullMeasurableSet]

theorem p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_mass_ge_eighth
    (e : Link) (a : G) (r : ℝ) (hr : 1 < r) :
    (1 / 8 : ℝ) ≤
      Measure.real outer (p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder H e a r) := by
  rw [p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_mass_eq]
  exact p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth a r hr

/-- This TRUE finite-volume first-link chordal cylinder is explicitly
>1/17 in the original boundary pair-Haar, at every SU(2) center.
Nothing is inferred about the unconstrained other link variables. -/
theorem p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_fiveFour_mass_gt_seventeenth
    (e : Link) (a : G) :
    (1 / 17 : ℝ) <
      Measure.real outer
        (p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder H e a (5 / 4)) := by
  have h :=
    p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_mass_ge_eighth
      H e a (5 / 4) (by norm_num)
  linarith

/-- The original physical ACI genuine nonzero covariance point
can be chosen AS the center of an ACTUAL five-four calibrated
link-coordinate open Haar ball cylinder of mass >1/17. -/
theorem p4Q2PZ37ADK_everyOriginalLink_nonzeroCov_centeredChordalCylinder
    (e : Link) :
    ∃ z₀ : Pair,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0 ∧
      z₀ ∈ p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder
        H e (z₀.1 e) (5 / 4) ∧
      IsOpen (p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder
        H e (z₀.1 e) (5 / 4)) ∧
      (1 / 17 : ℝ) <
        Measure.real outer (p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder
          H e (z₀.1 e) (5 / 4)) := by
  obtain ⟨z₀, hz₀⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
        (originalWilsonExplicitIdentityBoundary H)
  refine ⟨z₀, hz₀, ?_,
    p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_isOpen
      H e (z₀.1 e) (5 / 4),
    p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_fiveFour_mass_gt_seventeenth
      H e (z₀.1 e)⟩
  exact p4Q2PZ37ADK_trueChordalBall_mem_center (z₀.1 e) (5 / 4) (by norm_num)

private theorem p4Q2PZ37ADK_rightCoordinateMP
    (e : Link) :
    MeasurePreserving (fun z : Pair => z.2 e) outer (normalizedCompactHaar G) := by
  have hRight : MeasurePreserving (fun z : Pair => z.2) outer slice := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    exact MeasureTheory.measurePreserving_snd
  have hEval : MeasurePreserving (fun x : Cfg => x e) slice (normalizedCompactHaar G) := by
    simpa only [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (fun _ : Link => normalizedCompactHaar G) e)
  simpa only [Function.comp_def] using hEval.comp hRight

/-- Two ORIGINAL physical-boundary link coordinates, both inside
numeric 5/4 calibrated chordal balls. The event is NOT an all-link
metric ball and imposes no covariance regularity premise. -/
def p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder
    (e : Link) (a b : G) : Set Pair :=
  {z | z.1 e ∈ p4Q2PZ37ADK_trueChordalBall a (5 / 4) ∧
    z.2 e ∈ p4Q2PZ37ADK_trueChordalBall b (5 / 4)}

/-- Exact original Haar pair-coordinate law, with
one actual SU(2) Haar factor for EACH original boundary. -/
theorem p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder_mass_eq
    (e : Link) (a b : G) :
    Measure.real outer (p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder H e a b) =
      Measure.real haar (p4Q2PZ37ADK_trueChordalBall a (5 / 4)) *
        Measure.real haar (p4Q2PZ37ADK_trueChordalBall b (5 / 4)) := by
  have hEval : MeasurePreserving (fun x : Cfg => x e)
      slice (normalizedCompactHaar G) := by
    simpa only [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (fun _ : Link => normalizedCompactHaar G) e)
  have hPair : MeasurePreserving
      (fun z : Pair => (z.1 e, z.2 e)) outer
      ((normalizedCompactHaar G).prod (normalizedCompactHaar G)) := by
    have hProd := hEval.prod hEval
    simpa [periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      Function.comp_def] using hProd
  have hMass :
      Measure.real outer (p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder H e a b) =
        Measure.real ((normalizedCompactHaar G).prod (normalizedCompactHaar G))
          (p4Q2PZ37ADK_trueChordalBall a (5 / 4) ×ˢ
            p4Q2PZ37ADK_trueChordalBall b (5 / 4)) := by
    change Measure.real outer
        ((fun z : Pair => (z.1 e, z.2 e)) ⁻¹'
          (p4Q2PZ37ADK_trueChordalBall a (5 / 4) ×ˢ
            p4Q2PZ37ADK_trueChordalBall b (5 / 4))) =
      Measure.real ((normalizedCompactHaar G).prod (normalizedCompactHaar G))
          (p4Q2PZ37ADK_trueChordalBall a (5 / 4) ×ˢ
            p4Q2PZ37ADK_trueChordalBall b (5 / 4))
    simp only [measureReal_def]
    rw [hPair.measure_preimage
      ((p4Q2PZ37ADK_trueChordalBall_isOpen a (5 / 4)).measurableSet.prod
        (p4Q2PZ37ADK_trueChordalBall_isOpen b (5 / 4)).measurableSet).nullMeasurableSet]
  rw [hMass, measureReal_prod_prod]

/-- Two genuine boundary-coordinate calibrated chordal balls have
explicit true pair-Haar mass ≥1/64 for EVERY finite H/link/centers. -/
theorem p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder_mass_ge_sixtyFour
    (e : Link) (a b : G) :
    (1 / 64 : ℝ) ≤
      Measure.real outer (p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder H e a b) := by
  rw [p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder_mass_eq]
  calc
    (1 / 64 : ℝ) = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
    _ ≤ Measure.real haar (p4Q2PZ37ADK_trueChordalBall a (5 / 4)) *
        Measure.real haar (p4Q2PZ37ADK_trueChordalBall b (5 / 4)) :=
      mul_le_mul
        (p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth a (5 / 4) (by norm_num))
        (p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth b (5 / 4) (by norm_num))
        (by norm_num)
        (le_trans (by norm_num)
          (p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth a (5 / 4) (by norm_num)))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueFeature_norm_sq_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueFeature_chord_sq_eq_twiceWilsonEnergy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalDistance_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalDistance_self
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalDistance_symm
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalDistance_triangle
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueFeature_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalBall_isOpen
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalBall_mem_center
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_translatedLowCap_subset_chordalBall
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_translatedOriginalLowCap_mass_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADK_trueChordalBall_radiusFiveFour_mass_gt_seventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_mass_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_mass_ge_eighth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADK_originalFirstBoundaryChordalCylinder_fiveFour_mass_gt_seventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADK_everyOriginalLink_nonzeroCov_centeredChordalCylinder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder_mass_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADK_originalTwoBoundaryChordalCylinder_mass_ge_sixtyFour
