import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPerronThresholdProfileV5_PZ37ACX
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAmplitudeMomentRegionsV5_PZ37ACN

/-!
# P4-Q2-PZ37ACY — original four-mode / higher-residual intersection

Append-only genuine finite-volume interacting Wilson SU(2) theorem leaf.
Preserve the original Gauss-law centered physical source, original FF receiver,
ground-state Perron representative, updated transfer section U_z, both actual
interacting posteriors, true boundary-pair Haar ν_H, and same spatial link e.

Let A(z)^2 be the original receiver's genuine first-four Haar coefficient
energy, W(z) its genuine higher-character Haar residual, S its proved
positive four-coefficient covariance second moment, B its actual original
FC receiver envelope, and tau(b) its original posterior squared exponent
gap. The precise ACT/ACU Perron-weighted local discriminator satisfies
  w(z) = 16 A(z)^2 - tau(b) W(z)
because both original energies retain the SAME P_z^2 factor.

For arbitrary residual threshold r>0, define two OPEN original boundary
regions
  H = {z | 2*S < A(z)^2},
  L_r = {z | W(z) < r},
  J_r = H intersect L_r.
On J_r, w(z)>32*S-tau(b)*r. An unconditional, quantitatively
nontrivial *overlap* inequality follows from the original high-four-mode
Haar mass floor and the true higher-character residual moment Wbar:
  r*nu_H(J_r) >=
    r*(4*S)/(B^2/2-4*S) - Wbar.
Thus the original physical data, without an assumed independent Haar
receiver, control the intersection and its inclusion in the ACT/ACW
Perron-threshold favorable region.

A stronger unconditional result uses the ORIGINAL local FC allocation
4*A(z)^2 + W(z) <= B^2. Every z in H actually satisfies
W(z) < B^2-8*S, so for this proved, strictly positive residual cap the
intersection J_{B^2-8*S} equals H, and retains ACN's explicit strictly
positive Haar-mass lower floor. On the SAME region
  w(z) > 32*S - tau(b)*(B^2-8*S).
Its positive-Haar-mass existence is unconditional, while the strict
POSITIVITY of this signed threshold remains OPEN for actual Wilson data.

A conditional moment criterion combining Wbar, S, B and the ACT/ACW
Haar-mass ratio C/(C+delta) yields positive original GI *SQUARED
CERTIFICATE*, with an open nonzero actual signed GI-response region via
previous ACO. We do not assert this sufficient condition for the actual
Wilson model, nor any volume-uniform coercivity or continuum 4D mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local instance p4Q2PZ37ACY_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACY_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACY_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACY_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACY_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACY_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "d" => p4Q2PZ37ACT_originalTransferLocalDiscriminant H
local notation "w" => p4Q2PZ37ACU_weightedLocalDiscriminant H
local notation "C" => p4Q2PZ37ACW_originalNegativeFCBudget H
local notation "T" => p4Q2PZ37ACW_originalPositiveWeightThresholdRegion H
local instance p4Q2PZ37ACY_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACY_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The SAME original four-mode positive-signal boundary region whose
strict Haar-mass floor was established in ACN; no new amplitude model. -/
def p4Q2PZ37ACY_originalHighFourModeRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Set Pair :=
  {z | 2 * S b hb e < (A b hb e z) ^ 2}
local notation "High" => p4Q2PZ37ACY_originalHighFourModeRegion H

/-- Original TRUE higher-character Haar remainder low-energy region. -/
def p4Q2PZ37ACY_originalLowResidualRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (r : ℝ) : Set Pair :=
  {z | W b hb e z < r}
local notation "Low" => p4Q2PZ37ACY_originalLowResidualRegion H

/-- Simultaneous high genuine first-four signal and low genuine higher
SU(2) Haar remainder on EXACTLY the same original boundary pair. -/
def p4Q2PZ37ACY_originalModeIntersectionRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (r : ℝ) : Set Pair :=
  High b hb e ∩ Low b hb e r
local notation "Good" => p4Q2PZ37ACY_originalModeIntersectionRegion H

/-- Existing ACN positive signal floor exactly in this module's
original physical boundary data, not a substitute distribution. -/
def p4Q2PZ37ACY_originalFourModeMassFloor
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  (4 * S b hb e) / ((B b hb) ^ 2 / 2 - 4 * S b hb e)
local notation "F" => p4Q2PZ37ACY_originalFourModeMassFloor H

/-- A physically selected residual threshold that is proved strictly
positive at b>0 by the actual ACN high-four-mode receiver moment. -/
def p4Q2PZ37ACY_originalSelectedResidualCeiling
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  (B b hb) ^ 2 - 8 * S b hb e
local notation "Rcap" => p4Q2PZ37ACY_originalSelectedResidualCeiling H

/-- Original updated-Perron-transfer discriminant as the ORIGINAL FF
receiver's first-four and higher-mode energies, with the identical P_z²
factor in BOTH components; no loss of the boundary-dependent weight. -/
theorem p4Q2PZ37ACY_originalWeightedLocal_eq_fourMode_sub_residual
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    w b hb e z = 16 * (A b hb e z) ^ 2 - tau b * W b hb e z := by
  have hA := p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b hb e z
  have hW := p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b hb e z
  calc
    w b hb e z =
        16 * ((P b hb z) ^ 2 * tA2 b hb e z) -
          tau b * ((P b hb z) ^ 2 * tW b hb e z) := by
      unfold p4Q2PZ37ACU_weightedLocalDiscriminant
        p4Q2PZ37ACT_originalTransferLocalDiscriminant
      ring
    _ = 16 * (A b hb e z) ^ 2 - tau b * W b hb e z := by
      rw [← hA, ← hW]

/-- Both original high-four-mode and low-higher-mode regions are OPEN,
with no positive lower bound on the varying Perron representative. -/
theorem p4Q2PZ37ACY_originalHighFourModeRegion_isOpen
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    IsOpen (High b hb e) := by
  unfold p4Q2PZ37ACY_originalHighFourModeRegion
  exact isOpen_lt continuous_const
    (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb e)

/-- Original higher-mode residual is continuous, so low-energy regions
are OPEN in the true, both-configuration boundary pair topology. -/
theorem p4Q2PZ37ACY_originalLowResidualRegion_isOpen
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (r : ℝ) :
    IsOpen (Low b hb e r) := by
  unfold p4Q2PZ37ACY_originalLowResidualRegion
  exact isOpen_lt
    (p4Q2PZ37ACR_originalResidual_continuous H b hb e)
    continuous_const

/-- Simultaneous signal/residual test is also OPEN on the actual pair. -/
theorem p4Q2PZ37ACY_originalModeIntersectionRegion_isOpen
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (r : ℝ) :
    IsOpen (Good b hb e r) := by
  unfold p4Q2PZ37ACY_originalModeIntersectionRegion
  exact (p4Q2PZ37ACY_originalHighFourModeRegion_isOpen H b hb e).inter
    (p4Q2PZ37ACY_originalLowResidualRegion_isOpen H b hb e r)

/-- On every true original high-four-mode boundary pair, the ORIGINAL
FF receiver FC allocation forces the higher-Haar remainder strictly
below B²−8S, without a high-mode smallness hypothesis. -/
theorem p4Q2PZ37ACY_highFourMode_forces_residual_below_selectedCeiling
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair)
    (hz : z ∈ High b hb e) :
    W b hb e z < Rcap b hb e := by
  have hHigh : 2 * S b hb e < (A b hb e z) ^ 2 := hz
  have hVar := p4Q2PZ37ACA_originalReceiver_variance_le_FC
    H b hb f₀ e z
  change V b hb e z ≤ (B b hb) ^ 2 at hVar
  have hDec := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual
    H b hb e z
  unfold p4Q2PZ37ACY_originalSelectedResidualCeiling
  nlinarith only [hHigh, hVar, hDec]

/-- At the ACTUAL physical selected residual ceiling, the intersection
is IDENTICAL to the original high-signal region, not merely a.e. -/
theorem p4Q2PZ37ACY_selectedIntersection_eq_highFourMode
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Good b hb e (Rcap b hb e) = High b hb e := by
  ext z
  constructor
  · intro hz
    exact hz.1
  · intro hz
    exact ⟨hz,
      p4Q2PZ37ACY_highFourMode_forces_residual_below_selectedCeiling
        H b hb e z hz⟩

/-- From the unchanged ACN high-signal proof: its Haar-mass floor is
strictly positive, and the physical selected residual cap is positive. -/
theorem p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Rcap b hb.le e ∧
      0 < F b hb.le e ∧
      F b hb.le e ≤ Measure.real outer (High b hb.le e) := by
  obtain ⟨hDen, hMass⟩ :=
    p4Q2PZ37ACN_highAmplitudeRegion_mass_lower H b hb e
  have hS := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    H b hb e
  have hF : 0 < F b hb.le e :=
    div_pos (mul_pos (by norm_num) hS) hDen
  have hR : 0 < Rcap b hb.le e := by
    unfold p4Q2PZ37ACY_originalSelectedResidualCeiling
    linarith only [hDen]
  change F b hb.le e ≤ Measure.real outer (High b hb.le e) at hMass
  exact ⟨hR, hF, hMass⟩

/-- Genuine high-four-mode / low-higher-mode simultaneous region has
an unconditional explicit POSITIVE Haar mass floor, at the physical
selected residual ceiling. Neither GI sign nor H-uniformity is claimed. -/
theorem p4Q2PZ37ACY_selectedIntersection_open_positiveMass_lower
    (b : ℝ) (hb : 0 < b) (e : Link) :
    IsOpen (Good b hb.le e (Rcap b hb.le e)) ∧
      0 < F b hb.le e ∧
      F b hb.le e ≤
        Measure.real outer (Good b hb.le e (Rcap b hb.le e)) := by
  obtain ⟨_, hfPos, hFloor⟩ :=
    p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass H b hb e
  rw [p4Q2PZ37ACY_selectedIntersection_eq_highFourMode H b hb.le e]
  exact ⟨p4Q2PZ37ACY_originalHighFourModeRegion_isOpen H b hb.le e,
    hfPos, hFloor⟩

/-- Simultaneous high four-mode energy and low residual r imply a
strict, ORIGINAL Perron-weighted ACT local discriminator floor.
In particular the same local test uses the very same boundary pair. -/
theorem p4Q2PZ37ACY_intersection_forces_weightedDiscriminant_floor
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (r : ℝ) (z : Pair)
    (hz : z ∈ Good b hb e r) :
    32 * S b hb e - tau b * r < w b hb e z := by
  have hSignal : 2 * S b hb e < (A b hb e z) ^ 2 := hz.1
  have hResidual : W b hb e z < r := hz.2
  have hTau : 0 ≤ tau b := sq_nonneg _
  have hAmp : 32 * S b hb e < 16 * (A b hb e z) ^ 2 := by
    linarith only [hSignal]
  have hProd : tau b * W b hb e z ≤ tau b * r :=
    mul_le_mul_of_nonneg_left (le_of_lt hResidual) hTau
  rw [p4Q2PZ37ACY_originalWeightedLocal_eq_fourMode_sub_residual]
  linarith only [hAmp, hProd]

/-- A selected original high-signal region ALWAYS has w(z) above this
explicit local physical threshold, which can be negative. -/
theorem p4Q2PZ37ACY_selectedHighRegion_weightedDiscriminant_floor
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair)
    (hz : z ∈ High b hb e) :
    32 * S b hb e - tau b * Rcap b hb e < w b hb e z := by
  apply p4Q2PZ37ACY_intersection_forces_weightedDiscriminant_floor
    H b hb e (Rcap b hb e) z
  exact ⟨hz,
    p4Q2PZ37ACY_highFourMode_forces_residual_below_selectedCeiling
      H b hb e z hz⟩

/-- The SAME original pair-Haar measure of simultaneous four-mode
and low-residual boundaries is bounded by the ACT/ACW favorable threshold
region whenever delta<=32S−tau*r. -/
theorem p4Q2PZ37ACY_intersection_subset_originalThresholdRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (r delta : ℝ)
    (hDelta : delta ≤ 32 * S b hb e - tau b * r) :
    Good b hb e r ⊆ T b hb e delta := by
  intro z hz
  exact lt_of_le_of_lt hDelta
    (p4Q2PZ37ACY_intersection_forces_weightedDiscriminant_floor
      H b hb e r z hz)

/-- Integral of the indicator-envelope on the ORIGINAL pair-Haar law.
This is a sharp overlap-minus-residual estimate for ANY real r>0:
  r*nu_H(high) <= r*nu_H(high ∩ {W<r}) + true Wbar.
No independence or concentration assumption occurs. -/
theorem p4Q2PZ37ACY_originalIntersection_residualMoment_overlap
    (b : ℝ) (hb : 0 < b) (e : Link)
    (r : ℝ) (hr : 0 < r) :
    r * Measure.real outer (High b hb.le e) ≤
      r * Measure.real outer (Good b hb.le e r) + Wbar b hb.le e := by
  have hHighMeas : MeasurableSet (High b hb.le e) :=
    (p4Q2PZ37ACY_originalHighFourModeRegion_isOpen H b hb.le e).measurableSet
  have hGoodMeas : MeasurableSet (Good b hb.le e r) :=
    (p4Q2PZ37ACY_originalModeIntersectionRegion_isOpen
      H b hb.le e r).measurableSet
  have hHI : Integrable
      ((High b hb.le e).indicator (fun _ : Pair => (1 : ℝ))) outer :=
    (integrable_const _).indicator hHighMeas
  have hGI : Integrable
      ((Good b hb.le e r).indicator (fun _ : Pair => (1 : ℝ))) outer :=
    (integrable_const _).indicator hGoodMeas
  have hWI : Integrable (W b hb.le e) outer :=
    (p4Q2PZ37ACR_originalResidual_continuous H b hb.le e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Pair) :
      r * (High b hb.le e).indicator (fun _ : Pair => (1 : ℝ)) z ≤
        r * (Good b hb.le e r).indicator (fun _ : Pair => (1 : ℝ)) z +
          W b hb.le e z := by
    by_cases ha : z ∈ High b hb.le e
    · by_cases hw : z ∈ Low b hb.le e r
      · have hBoth : z ∈ Good b hb.le e r := ⟨ha, hw⟩
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem hBoth]
        have hW0 := p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg
          H b hb.le e z
        simp only [mul_one]
        linarith only [hW0]
      · have hNot : z ∉ Good b hb.le e r := fun h => hw h.2
        rw [Set.indicator_of_mem ha, Set.indicator_of_notMem hNot]
        have hLarge : r ≤ W b hb.le e z := le_of_not_gt hw
        simpa only [mul_one, mul_zero, zero_add] using hLarge
    · have hNot : z ∉ Good b hb.le e r := fun h => ha h.1
      rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem hNot]
      have hW0 := p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg
        H b hb.le e z
      simpa only [mul_zero, zero_add] using hW0
  have hBound :=
    integral_mono (hHI.const_mul r) ((hGI.const_mul r).add hWI) hPoint
  have hHighIntegral :
      (∫ z : Pair,
          r * (High b hb.le e).indicator (fun _ : Pair => (1 : ℝ)) z ∂outer) =
        r * Measure.real outer (High b hb.le e) := by
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hHighMeas]
    simp
  have hGoodIntegral :
      (∫ z : Pair,
          r * (Good b hb.le e r).indicator (fun _ : Pair => (1 : ℝ)) z ∂outer) =
        r * Measure.real outer (Good b hb.le e r) := by
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hGoodMeas]
    simp
  change (∫ z : Pair,
      r * (High b hb.le e).indicator (fun _ : Pair => (1 : ℝ)) z ∂outer) ≤
    (∫ z : Pair,
      r * (Good b hb.le e r).indicator (fun _ : Pair => (1 : ℝ)) z +
        W b hb.le e z ∂outer) at hBound
  rw [hHighIntegral, integral_add (hGI.const_mul r) hWI,
    hGoodIntegral] at hBound
  change r * Measure.real outer (High b hb.le e) ≤
    r * Measure.real outer (Good b hb.le e r) + Wbar b hb.le e at hBound
  exact hBound

/-- Quantitative true SU(2) four-mode/Haar-residual region overlap:
  r*ACN_mass_floor - Wbar <= r*nu_H(intersection).
It is unconditional for each r>0, but its RHS lower bound need not
be positive without a further verified physical relation. -/
theorem p4Q2PZ37ACY_originalIntersection_mass_lower_from_moments
    (b : ℝ) (hb : 0 < b) (e : Link)
    (r : ℝ) (hr : 0 < r) :
    r * F b hb.le e - Wbar b hb.le e ≤
      r * Measure.real outer (Good b hb.le e r) := by
  have hHigh := (p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass
    H b hb e).2.2
  have hMul := mul_le_mul_of_nonneg_left hHigh hr.le
  have hOverlap :=
    p4Q2PZ37ACY_originalIntersection_residualMoment_overlap H b hb e r hr
  linarith only [hMul, hOverlap]

/-- A positive numerical surplus of original moments gives a genuine
OPEN, positive-pair-Haar-mass simultaneous four-mode/residual region. -/
theorem p4Q2PZ37ACY_originalIntersection_positiveMass_of_momentSurplus
    (b : ℝ) (hb : 0 < b) (e : Link)
    (r : ℝ) (hr : 0 < r)
    (hSurplus : Wbar b hb.le e < r * F b hb.le e) :
    IsOpen (Good b hb.le e r) ∧
      0 < Measure.real outer (Good b hb.le e r) := by
  have hBound :=
    p4Q2PZ37ACY_originalIntersection_mass_lower_from_moments
      H b hb e r hr
  have hProd : 0 < r * Measure.real outer (Good b hb.le e r) := by
    linarith only [hBound, hSurplus]
  exact ⟨p4Q2PZ37ACY_originalModeIntersectionRegion_isOpen H b hb.le e r,
    (mul_pos_iff_of_pos_left hr).mp hProd⟩

/-- Preserving the SAME original boundary pairs, the moment overlap
bound transfers to the actual Perron-weighted ACT/ACW threshold region. -/
theorem p4Q2PZ37ACY_originalThresholdMass_lower_from_modeIntersection
    (b : ℝ) (hb : 0 < b) (e : Link)
    (r delta : ℝ) (hr : 0 < r)
    (hDelta : delta ≤ 32 * S b hb.le e - tau b * r) :
    r * F b hb.le e - Wbar b hb.le e ≤
      r * Measure.real outer (T b hb.le e delta) := by
  have hSub :=
    p4Q2PZ37ACY_intersection_subset_originalThresholdRegion
      H b hb.le e r delta hDelta
  have hMass : Measure.real outer (Good b hb.le e r) ≤
      Measure.real outer (T b hb.le e delta) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hSub)
  have hBound :=
    p4Q2PZ37ACY_originalIntersection_mass_lower_from_moments
      H b hb e r hr
  have hMul := mul_le_mul_of_nonneg_left hMass hr.le
  linarith only [hBound, hMul]

/-- Genuine high signal + physically proved low residual give an
UNCONDITIONAL explicit STRICTLY POSITIVE original pair-Haar threshold
mass at the true selected threshold (which itself may be negative). -/
theorem p4Q2PZ37ACY_selectedThreshold_open_positiveHaarMass
    (b : ℝ) (hb : 0 < b) (e : Link) :
    IsOpen (T b hb.le e
      (32 * S b hb.le e - tau b * Rcap b hb.le e)) ∧
    0 < F b hb.le e ∧
    F b hb.le e ≤
      Measure.real outer (T b hb.le e
        (32 * S b hb.le e - tau b * Rcap b hb.le e)) := by
  obtain ⟨_, hfPos, hHighFloor⟩ :=
    p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass H b hb e
  have hSub : High b hb.le e ⊆
      T b hb.le e
        (32 * S b hb.le e - tau b * Rcap b hb.le e) := by
    intro z hz
    exact p4Q2PZ37ACY_selectedHighRegion_weightedDiscriminant_floor
      H b hb.le e z hz
  have hMass : Measure.real outer (High b hb.le e) ≤
      Measure.real outer (T b hb.le e
        (32 * S b hb.le e - tau b * Rcap b hb.le e)) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hSub)
  exact ⟨p4Q2PZ37ACW_originalThresholdRegion_isOpen H b hb e _,
    hfPos, hHighFloor.trans hMass⟩

/-- A checkable S,Wbar,B,tau intersection surplus criterion for the
actual positive GI SQUARED mean certificate. It is strictly conditional:
the unmodified Wilson data are not asserted to satisfy this threshold. -/
theorem p4Q2PZ37ACY_originalMomentIntersection_surplus_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (r delta : ℝ) (hr : 0 < r) (hDelta : 0 < delta)
    (hLocal : delta ≤ 32 * S b hb.le e - tau b * r)
    (hSurplus :
      r * (C b hb.le / (C b hb.le + delta)) <
        r * F b hb.le e - Wbar b hb.le e) :
    0 < Budget b hb.le e := by
  have hBound :=
    p4Q2PZ37ACY_originalThresholdMass_lower_from_modeIntersection
      H b hb e r delta hr hLocal
  have hMass :
      C b hb.le / (C b hb.le + delta) <
        Measure.real outer (T b hb.le e delta) := by
    by_contra hn
    have hLe : Measure.real outer (T b hb.le e delta) ≤
        C b hb.le / (C b hb.le + delta) := le_of_not_gt hn
    have hProd := mul_le_mul_of_nonneg_left hLe hr.le
    linarith only [hBound, hProd, hSurplus]
  exact p4Q2PZ37ACW_originalRegionMass_ratio_gives_positiveBudget
    H b hb e delta hDelta hMass

/-- Same exact original moment intersection criterion yields an open
nonzero TRUE SIGNED two-interacting-posterior GI response region through
ACO. This is a conditional implication, not the certificate/response
identification, and not a continuum Yang–Mills mass-gap theorem. -/
theorem p4Q2PZ37ACY_originalMomentIntersection_surplus_gives_openGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (r delta : ℝ) (hr : 0 < r) (hDelta : 0 < delta)
    (hLocal : delta ≤ 32 * S b hb.le e - tau b * r)
    (hSurplus :
      r * (C b hb.le / (C b hb.le + delta)) <
        r * F b hb.le e - Wbar b hb.le e) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e
    (p4Q2PZ37ACY_originalMomentIntersection_surplus_gives_positiveBudget
      H b hb e r delta hr hDelta hLocal hSurplus)

/-- If the genuine mean GI squared certificate is NOT positive, the
physical S,Wbar,FC quantities face a necessary compatibility obstruction
for every r>0, delta>0 with delta<=32S−tau*r. -/
theorem p4Q2PZ37ACY_nonpositiveBudget_forces_intersectionMomentObstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0)
    (r delta : ℝ) (hr : 0 < r) (hDelta : 0 < delta)
    (hLocal : delta ≤ 32 * S b hb.le e - tau b * r) :
    r * F b hb.le e - Wbar b hb.le e ≤
      r * (C b hb.le / (C b hb.le + delta)) := by
  have hBound :=
    p4Q2PZ37ACY_originalThresholdMass_lower_from_modeIntersection
      H b hb e r delta hr hLocal
  have hObstruct :=
    p4Q2PZ37ACX_nonpositiveBudget_thresholdMass_upper
      H b hb e delta hDelta hNonpos
  have hScaled := mul_le_mul_of_nonneg_left hObstruct hr.le
  simpa only [add_comm] using (le_trans hBound hScaled)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalWeightedLocal_eq_fourMode_sub_residual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalHighFourModeRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalLowResidualRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalModeIntersectionRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_highFourMode_forces_residual_below_selectedCeiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_selectedIntersection_eq_highFourMode
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_selectedIntersection_open_positiveMass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_intersection_forces_weightedDiscriminant_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_selectedHighRegion_weightedDiscriminant_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_intersection_subset_originalThresholdRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalIntersection_residualMoment_overlap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalIntersection_mass_lower_from_moments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalIntersection_positiveMass_of_momentSurplus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalThresholdMass_lower_from_modeIntersection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_selectedThreshold_open_positiveHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalMomentIntersection_surplus_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_originalMomentIntersection_surplus_gives_openGIRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACY_nonpositiveBudget_forces_intersectionMomentObstruction
