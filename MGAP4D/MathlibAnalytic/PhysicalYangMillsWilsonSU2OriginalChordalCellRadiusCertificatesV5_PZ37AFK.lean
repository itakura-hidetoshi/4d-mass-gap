import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHaarQuadratureCertificatesV5_PZ37AFJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFK — genuine SU(2) chordal cell-radius error certificates

AFJ requires an independent actual-cell inequality for every original
Wilson/Perron receiver, squared receiver, and four Haar integrands.
AFK weakens this *verification workload*, never the mathematical
conclusion or the original model: it suffices to certify at finitely many
real SU(2) cell centers, with explicit rational rounding errors and
uniform genuine chordal oscillation constants.

The chordal distance is the ADK original real-eight matrix-feature
distance d_J(g,h); no arbitrary pseudometric is substituted.
Each AFJ measurable Haar cell has a genuinely verified center g_i and
a common radius r >= 0: g in C_i implies d_J(g,g_i) <= r.

Assume an actual original receiver uniform envelope M_F(z), a genuine
receiver chordal Lipschitz slope L_F(z), and a genuine four-mode
character envelope M_phi(j) and slope L_phi(j). These assumptions are
proof obligations about the ACTUAL original functions, not about a
numerical surrogate receiver. From one rational sample of F, F^2
and F phi_j at each true SU(2) center, with certified errors
epsMean(z), epsSecond(z), epsCoeff(z,j), deduce

  deltaMean = L_F*r + epsMean
  deltaSecond = 2*M_F*L_F*r + epsSecond
  deltaCoeff_j = (L_F*M_phi_j + M_F*L_phi_j)*r + epsCoeff_j.

These explicit inequalities build AFJ's original Haar quadrature
structure, then AFI's original coefficient/variance certificate,
the AFH genuine exceptional shell, and an original disjoint packing.

AFK does NOT establish concrete bounds on the true physical receiver,
the actual cell radii, normalized SU(2) Haar cell masses, numerical
quadrature values, strict shell crossings, volume-uniform coercivity,
or a 4D Yang--Mills continuum mass gap. Its purpose is to expose the
finite exact obligations needed for a subsequent numeric certification.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local instance p4Q2PZ37AFK_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFK_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFK_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFK_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFK_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFK_probabilityG : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

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
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H

local instance p4Q2PZ37AFK_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFK_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Actual chordal slope and certified center error produce a
whole-cell enclosure, using only the triangle inequality in ℝ. -/
private theorem p4Q2PZ37AFK_centerError_to_cell
    (x y q L d r eps : ℝ)
    (hSlope : |x - y| ≤ L * d)
    (hRadius : d ≤ r)
    (hL : 0 ≤ L)
    (hSample : |y - q| ≤ eps) :
    |x - q| ≤ L * r + eps := by
  calc
    |x - q| ≤ |x - y| + |y - q| := abs_sub_le x y q
    _ ≤ L * d + eps := add_le_add hSlope hSample
    _ ≤ L * r + eps :=
      add_le_add (mul_le_mul_of_nonneg_left hRadius hL) (le_refl eps)

/-- The squared genuine receiver oscillates at most twice the
receiver envelope times the original receiver Lipschitz slope. -/
private theorem p4Q2PZ37AFK_square_chordal_modulus
    (x y L M d : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hx : |x| ≤ M) (hy : |y| ≤ M)
    (hSlope : |x-y| ≤ L*d) :
    |x^2-y^2| ≤ (2*M*L)*d := by
  have hSum : |x+y| ≤ 2*M := by
    calc
      |x+y| ≤ |x|+|y| := abs_add_le _ _
      _ ≤ M+M := add_le_add hx hy
      _ = 2*M := by ring
  calc
    |x^2-y^2| = |x-y| * |x+y| := by
      rw [show x^2-y^2=(x-y)*(x+y) by ring, abs_mul]
    _ ≤ (L*d)* |x+y| :=
      mul_le_mul_of_nonneg_right hSlope (abs_nonneg _)
    _ ≤ (L*d)*(2*M) :=
      mul_le_mul_of_nonneg_left hSum (mul_nonneg hL hd)
    _ = (2*M*L)*d := by ring

/-- Product of the genuine receiver and the true Haar character:
the mixed oscillation needs both envelopes and both slopes. -/
private theorem p4Q2PZ37AFK_product_chordal_modulus
    (x y u v Lx Lu Mx Mu d : ℝ)
    (hLx : 0 ≤ Lx) (hLu : 0 ≤ Lu)
    (hMx : 0 ≤ Mx) (hMu : 0 ≤ Mu) (hd : 0 ≤ d)
    (hX : |x-y| ≤ Lx*d) (hU : |u-v| ≤ Lu*d)
    (hYBound : |y| ≤ Mx) (hUBound : |u| ≤ Mu) :
    |x*u-y*v| ≤ (Lx*Mu+Mx*Lu)*d := by
  have hTermX :
      |x-y| * |u| ≤ (Lx*d)*Mu := by
    calc
      |x-y| * |u| ≤ (Lx*d)* |u| :=
        mul_le_mul_of_nonneg_right hX (abs_nonneg _)
      _ ≤ (Lx*d)*Mu :=
        mul_le_mul_of_nonneg_left hUBound (mul_nonneg hLx hd)
  have hTermU :
      |y| * |u-v| ≤ Mx*(Lu*d) := by
    calc
      |y| * |u-v| ≤ |y| * (Lu*d) :=
        mul_le_mul_of_nonneg_left hU (abs_nonneg _)
      _ ≤ Mx*(Lu*d) :=
        mul_le_mul_of_nonneg_right hYBound (mul_nonneg hLu hd)
  calc
    |x*u-y*v| = |(x-y)*u+y*(u-v)| := by congr 1; ring
    _ ≤ |(x-y)*u| + |y*(u-v)| := abs_add_le _ _
    _ = |x-y| * |u|+|y| * |u-v| := by rw [abs_mul, abs_mul]
    _ ≤ (Lx*d)*Mu + Mx*(Lu*d) := add_le_add hTermX hTermU
    _ = (Lx*Mu+Mx*Lu)*d := by ring

/-- Radius-controlled AFJ cells and certified ORIGINAL receiver
point samples. No future existence or numerical values are hidden.
The chordal bounds are on actual SU(2) elements, not a substitute law. -/
structure p4Q2PZ37AFK_originalChordalCellSamples
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  partition : p4Q2PZ37AFJ_originalHaarCells
  center : Fin partition.n → G
  radius : ℝ
  hRadius : 0 ≤ radius
  hCellRadius : ∀ i (g : G), g ∈ partition.cell i →
    p4Q2PZ37ADK_trueChordalDistance g (center i) ≤ radius
  hThetaLo : 0 ≤ lo
  receiverEnvelope :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  hReceiverEnvelope_nonneg : ∀ a ∈ c.s, 0 ≤ receiverEnvelope a
  hReceiverBound : ∀ a ∈ c.s, ∀ g : G,
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a g| ≤ receiverEnvelope a
  receiverSlope :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  hReceiverSlope_nonneg : ∀ a ∈ c.s, 0 ≤ receiverSlope a
  hReceiverSlope : ∀ a ∈ c.s, ∀ g h : G,
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a g -
     p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a h| ≤
      receiverSlope a * p4Q2PZ37ADK_trueChordalDistance g h
  characterEnvelope : Fin 4 → ℝ
  characterSlope : Fin 4 → ℝ
  hCharacterEnvelope_nonneg : ∀ j, 0 ≤ characterEnvelope j
  hCharacterSlope_nonneg : ∀ j, 0 ≤ characterSlope j
  hCharacterBound : ∀ j (g : G),
    |p4Q2PZ37ACK_fourModeCharacter j g| ≤ characterEnvelope j
  hCharacterSlope : ∀ j (g h : G),
    |p4Q2PZ37ACK_fourModeCharacter j g -
      p4Q2PZ37ACK_fourModeCharacter j h| ≤
       characterSlope j * p4Q2PZ37ADK_trueChordalDistance g h
  meanSample :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
       Fin partition.n → ℚ
  meanSampleError :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  hMeanSampleError_nonneg : ∀ a ∈ c.s, 0 ≤ meanSampleError a
  hMeanSample : ∀ a ∈ c.s, ∀ i,
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a (center i) -
        (meanSample a i : ℝ)| ≤ meanSampleError a
  secondSample :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
       Fin partition.n → ℚ
  secondSampleError :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  hSecondSampleError_nonneg : ∀ a ∈ c.s, 0 ≤ secondSampleError a
  hSecondSample : ∀ a ∈ c.s, ∀ i,
    |(p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a (center i))^2 -
       (secondSample a i : ℝ)| ≤ secondSampleError a
  coefficientSample :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
       Fin 4 → Fin partition.n → ℚ
  coefficientSampleError :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
       Fin 4 → ℝ
  hCoefficientSampleError_nonneg : ∀ a ∈ c.s, ∀ j,
    0 ≤ coefficientSampleError a j
  hCoefficientSample : ∀ a ∈ c.s, ∀ j i,
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a (center i) *
       p4Q2PZ37ACK_fourModeCharacter j (center i) -
       (coefficientSample a j i : ℝ)| ≤ coefficientSampleError a j

/-- A radius+chordal-slope formula, with original sample rounding. -/
def p4Q2PZ37AFK_meanOscillation
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) : ℝ :=
  d.receiverSlope a * d.radius + d.meanSampleError a

/-- Exact square residual's Lipschitz inflation: 2 M_F L_F r. -/
def p4Q2PZ37AFK_secondOscillation
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) : ℝ :=
  (2*d.receiverEnvelope a*d.receiverSlope a)*d.radius +
    d.secondSampleError a

/-- Genuine F phi_j coefficient product's mixed chordal error. -/
def p4Q2PZ37AFK_coefficientOscillation
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (j : Fin 4) : ℝ :=
  (d.receiverSlope a*d.characterEnvelope j +
    d.receiverEnvelope a*d.characterSlope j)*d.radius +
    d.coefficientSampleError a j

/-- The slope and radius requirements alone guarantee nonnegative
mean oscillation budgets, without assuming the AFJ local checks. -/
theorem p4Q2PZ37AFK_meanOscillation_nonneg
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    0 ≤ p4Q2PZ37AFK_meanOscillation H e c d a := by
  unfold p4Q2PZ37AFK_meanOscillation
  exact add_nonneg
    (mul_nonneg (d.hReceiverSlope_nonneg a ha) d.hRadius)
    (d.hMeanSampleError_nonneg a ha)

/-- Squared physical receiver's error radius is nonnegative. -/
theorem p4Q2PZ37AFK_secondOscillation_nonneg
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    0 ≤ p4Q2PZ37AFK_secondOscillation H e c d a := by
  unfold p4Q2PZ37AFK_secondOscillation
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (d.hReceiverEnvelope_nonneg a ha))
        (d.hReceiverSlope_nonneg a ha)) d.hRadius
  · exact d.hSecondSampleError_nonneg a ha

/-- Product coefficient error is nonnegative on the actual finite net. -/
theorem p4Q2PZ37AFK_coefficientOscillation_nonneg
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4) :
    0 ≤ p4Q2PZ37AFK_coefficientOscillation H e c d a j := by
  unfold p4Q2PZ37AFK_coefficientOscillation
  exact add_nonneg
    (mul_nonneg
      (add_nonneg
        (mul_nonneg (d.hReceiverSlope_nonneg a ha)
          (d.hCharacterEnvelope_nonneg j))
        (mul_nonneg (d.hReceiverEnvelope_nonneg a ha)
          (d.hCharacterSlope_nonneg j))) d.hRadius)
    (d.hCoefficientSampleError_nonneg a ha j)

/-- One center evaluation per original SU(2) cell, not an
uncountable family of independent AFJ pointwise inequalities. -/
theorem p4Q2PZ37AFK_meanLocal_from_chordal
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (i : Fin d.partition.n)
    (g : G) (hg : g ∈ d.partition.cell i) :
    |F b0 hb0 f0 e a g - (d.meanSample a i : ℝ)| ≤
      p4Q2PZ37AFK_meanOscillation H e c d a := by
  exact p4Q2PZ37AFK_centerError_to_cell
    (F b0 hb0 f0 e a g) (F b0 hb0 f0 e a (d.center i))
    (d.meanSample a i : ℝ) (d.receiverSlope a)
    (dJ g (d.center i)) d.radius (d.meanSampleError a)
    (d.hReceiverSlope a ha g (d.center i))
    (d.hCellRadius i g hg) (d.hReceiverSlope_nonneg a ha)
    (d.hMeanSample a ha i)

/-- Squared physical receiver admits a cellwise error from the
same certified chordal radius and the actual receiver envelope. -/
theorem p4Q2PZ37AFK_secondLocal_from_chordal
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (i : Fin d.partition.n)
    (g : G) (hg : g ∈ d.partition.cell i) :
    |(F b0 hb0 f0 e a g)^2 - (d.secondSample a i : ℝ)| ≤
      p4Q2PZ37AFK_secondOscillation H e c d a := by
  apply p4Q2PZ37AFK_centerError_to_cell
    ((F b0 hb0 f0 e a g)^2) ((F b0 hb0 f0 e a (d.center i))^2)
    (d.secondSample a i : ℝ)
    (2*d.receiverEnvelope a*d.receiverSlope a)
    (dJ g (d.center i)) d.radius (d.secondSampleError a)
  · exact p4Q2PZ37AFK_square_chordal_modulus
      (F b0 hb0 f0 e a g) (F b0 hb0 f0 e a (d.center i))
      (d.receiverSlope a) (d.receiverEnvelope a) (dJ g (d.center i))
      (d.hReceiverEnvelope_nonneg a ha) (d.hReceiverSlope_nonneg a ha)
      (p4Q2PZ37ADK_trueChordalDistance_nonneg g (d.center i))
      (d.hReceiverBound a ha g) (d.hReceiverBound a ha (d.center i))
      (d.hReceiverSlope a ha g (d.center i))
  · exact d.hCellRadius i g hg
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (d.hReceiverEnvelope_nonneg a ha))
      (d.hReceiverSlope_nonneg a ha)
  · exact d.hSecondSample a ha i

/-- Genuine four-mode F*phi_j needs both receiver and character
slope terms; its numerical center is checked only once per cell. -/
theorem p4Q2PZ37AFK_coefficientLocal_from_chordal
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4)
    (i : Fin d.partition.n) (g : G) (hg : g ∈ d.partition.cell i) :
    |F b0 hb0 f0 e a g * phi j g -
      (d.coefficientSample a j i : ℝ)| ≤
        p4Q2PZ37AFK_coefficientOscillation H e c d a j := by
  apply p4Q2PZ37AFK_centerError_to_cell
    (F b0 hb0 f0 e a g * phi j g)
    (F b0 hb0 f0 e a (d.center i) * phi j (d.center i))
    (d.coefficientSample a j i : ℝ)
    (d.receiverSlope a*d.characterEnvelope j +
      d.receiverEnvelope a*d.characterSlope j)
    (dJ g (d.center i)) d.radius (d.coefficientSampleError a j)
  · exact p4Q2PZ37AFK_product_chordal_modulus
      (F b0 hb0 f0 e a g) (F b0 hb0 f0 e a (d.center i))
      (phi j g) (phi j (d.center i))
      (d.receiverSlope a) (d.characterSlope j)
      (d.receiverEnvelope a) (d.characterEnvelope j)
      (dJ g (d.center i))
      (d.hReceiverSlope_nonneg a ha) (d.hCharacterSlope_nonneg j)
      (d.hReceiverEnvelope_nonneg a ha) (d.hCharacterEnvelope_nonneg j)
      (p4Q2PZ37ADK_trueChordalDistance_nonneg g (d.center i))
      (d.hReceiverSlope a ha g (d.center i))
      (d.hCharacterSlope j g (d.center i))
      (d.hReceiverBound a ha (d.center i)) (d.hCharacterBound j g)
  · exact d.hCellRadius i g hg
  · exact add_nonneg
      (mul_nonneg (d.hReceiverSlope_nonneg a ha) (d.hCharacterEnvelope_nonneg j))
      (mul_nonneg (d.hReceiverEnvelope_nonneg a ha) (d.hCharacterSlope_nonneg j))
  · exact d.hCoefficientSample a ha j i

/-- Construct the EXACT AFJ genuine Haar finite-cell witness from
certified metric radii, chordal slopes and rational center samples. -/
def p4Q2PZ37AFK_toOriginalReceiverQuadrature
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c) :
    p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c where
  partition := d.partition
  hThetaLo := d.hThetaLo
  coefficientSample := d.coefficientSample
  coefficientOsc := fun a j => p4Q2PZ37AFK_coefficientOscillation H e c d a j
  hCoefficientOsc_nonneg := by
    intro a ha j
    exact p4Q2PZ37AFK_coefficientOscillation_nonneg H e c d a ha j
  hCoefficientLocal := by
    intro a ha j i g hg
    exact p4Q2PZ37AFK_coefficientLocal_from_chordal H e c d a ha j i g hg
  meanSample := d.meanSample
  meanOsc := fun a => p4Q2PZ37AFK_meanOscillation H e c d a
  hMeanOsc_nonneg := by
    intro a ha
    exact p4Q2PZ37AFK_meanOscillation_nonneg H e c d a ha
  hMeanLocal := by
    intro a ha i g hg
    exact p4Q2PZ37AFK_meanLocal_from_chordal H e c d a ha i g hg
  secondSample := d.secondSample
  secondOsc := fun a => p4Q2PZ37AFK_secondOscillation H e c d a
  hSecondOsc_nonneg := by
    intro a ha
    exact p4Q2PZ37AFK_secondOscillation_nonneg H e c d a ha
  hSecondLocal := by
    intro a ha i g hg
    exact p4Q2PZ37AFK_secondLocal_from_chordal H e c d a ha i g hg

/-- Build the same AFI genuine Wilson/Perron coefficient-and-variance
certificate; no independently fitted residual model is introduced. -/
def p4Q2PZ37AFK_toOriginalCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFJ_toOriginalCoefficientVarianceCertificate H e c
    (p4Q2PZ37AFK_toOriginalReceiverQuadrature H e c d)

/-- Original strict-shell centers selected from certified radius
tables and actual SU(2) Haar-cell rational weights. -/
def p4Q2PZ37AFK_originalChordalShellCenters
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c) :
    Finset Pair :=
  p4Q2PZ37AFI_derivedOriginalShellCenters H e c
    (p4Q2PZ37AFK_toOriginalCoefficientVarianceCertificate H e c d)

/-- A chosen AFK cell certificate can never create a false original
physical residual-gap crossing. -/
theorem p4Q2PZ37AFK_originalChordalCenter_trueSigns
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFK_originalChordalShellCenters H e c d) :
    c.etaLo < Gap e lo a ∧ Gap e hi a < -c.etaHi :=
  p4Q2PZ37AFI_derivedCenter_trueOriginalSigns H e c
    (p4Q2PZ37AFK_toOriginalCoefficientVarianceCertificate H e c d) a ha

/-- Positivity is for the ORIGINAL pair-Haar measure and actual
Wilson/Perron exceptional shell, conditional on a certified center. -/
theorem p4Q2PZ37AFK_originalChordalCenter_positiveHaarShell
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFK_originalChordalShellCenters H e c d) :
    0 < Measure.real outer (Shell e lo hi) := by
  have hFloor := p4Q2PZ37AFH_intervalCenter_floor_le_shellMass H e c
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c
      (p4Q2PZ37AFK_toOriginalCoefficientVarianceCertificate H e c d)) a ha
  exact (p4Q2PZ37AEA_explicitFloor_pos H c.r c.hR).trans_le hFloor

/-- The genuinely separated AFD packing and its H-dependent
Haar-mass floor survive the reduction to finitely many cell centers. -/
theorem p4Q2PZ37AFK_originalChordalPacking_exists
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c) :
    ∃ t : Finset Pair,
      t ⊆ p4Q2PZ37AFK_originalChordalShellCenters H e c d ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2*c.r ≤ D a b) ∧
      (∀ a ∈ p4Q2PZ37AFK_originalChordalShellCenters H e c d,
        ∃ b ∈ t, D a b < 2*c.r) ∧
      (t.card : ℝ)*p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) :=
  p4Q2PZ37AFI_derivedOriginalPacking_exists H e c
    (p4Q2PZ37AFK_toOriginalCoefficientVarianceCertificate H e c d)

/-- Every actual finite AFK candidate has positive genuine four-mode
amplitude and two strictly distinct thresholds, never zero-amplitude
pseudo-shell crossing. -/
theorem p4Q2PZ37AFK_originalChordalCenter_thresholdObstruction
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFK_originalChordalShellCenters H e c d) :
    0 < (p4Q2PZ37ACM_originalCovarianceAmplitude H b0 hb0 e a)^2 ∧
      lo < hi :=
  p4Q2PZ37AFH_intervalCenter_amplitude_pos_and_threshold_strict H e c
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c
      (p4Q2PZ37AFK_toOriginalCoefficientVarianceCertificate H e c d)) a ha

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_meanOscillation_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_secondOscillation_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_coefficientOscillation_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_meanLocal_from_chordal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_secondLocal_from_chordal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_coefficientLocal_from_chordal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_originalChordalCenter_trueSigns
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_originalChordalCenter_positiveHaarShell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_originalChordalPacking_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFK_originalChordalCenter_thresholdObstruction
