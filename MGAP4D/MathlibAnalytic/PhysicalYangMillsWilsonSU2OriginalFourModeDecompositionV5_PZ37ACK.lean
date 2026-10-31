import MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoFourModeHaarV5_PZ37ACK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaugeOrbitV5_PZ37ACK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCovarianceMomentRegionsV5_PZ37ACJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRegressionErrorBudgetV5_PZ37ACJ

/-!
# P4-Q2-PZ37ACK — the original physical receiver's four Haar modes

Project the SAME original centered-source receiver onto the four genuine
quaternion translates of the fundamental real SU(2) character. Their exact
Haar Gram matrix is one quarter of the identity. The remainder subtracts
the actual link-section mean, not the unrelated spatial source mean.

The original simultaneous gauge action identifies each coefficient with
minus the original energy covariance in a genuinely transformed context.
It preserves the original outer pair-Haar measure. Consequently every
coefficient has the SAME outer squared moment S from ACJ, and exactly
  integral_outer Var(F) = 16*S + W,
  integral_outer (Var(F)-4*C^2) = 12*S + W,
where W is the actual nonnegative integral of the four-mode remainder square.

This strengthens the original envelope to S <= B^2/16 and gives genuine
averaged residual obstructions at each finite H,b>0,e. No claim of a
numerical or H-uniform positive floor for S, a favorable-region GI margin,
or continuum coercivity is made. All original physical data are retained.
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
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local notation "φ" => p4Q2PZ37ACK_fourModeCharacter
local notation "q" => p4Q2PZ35B_quaternionFamily
local instance p4Q2PZ37ACK_decompositionGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACK_decompositionCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACK_decompositionCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACK_decompositionMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACK_decompositionBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACK_decompositionProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "Γ" => p4Q2PZ37ACK_originalGaugePair H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local instance p4Q2PZ37ACK_decompositionLinks : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACK_decompositionOuterProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Actual four coefficients of the unchanged centered physical receiver. -/
def p4Q2PZ37ACK_originalFourModeCoefficient
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (j : Fin 4) : ℝ :=
  CompactFiniteHaarProjection.coefficient μ (F b hb f₀ e z) φ j
local notation "m" => p4Q2PZ37ACK_originalFourModeCoefficient H

/-- The genuine four-mode orthogonal projection with Gram normalization 1/4. -/
def p4Q2PZ37ACK_originalFourModeProjection
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : G → ℝ :=
  CompactFiniteHaarProjection.projection μ (F b hb f₀ e z) φ

/-- Actual link-centered remainder after removing all four fundamental modes. -/
def p4Q2PZ37ACK_originalFourModeRemainder
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : G → ℝ :=
  CompactFiniteHaarProjection.remainder μ (F b hb f₀ e z) φ
local notation "R" => p4Q2PZ37ACK_originalFourModeRemainder H

/-- Actual residual square integral in the original single-link Haar law. -/
def p4Q2PZ37ACK_originalFourModeResidualEnergy
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  ∫ g : G, (R b hb e z g) ^ 2 ∂μ
local notation "Wz" => p4Q2PZ37ACK_originalFourModeResidualEnergy H

/-- The true outer mean of the nonnegative four-mode remainder energy. -/
def p4Q2PZ37ACK_originalFourModeResidualMoment
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ := ∫ z : Pair, Wz b hb e z ∂outer
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualMoment H

/-- Mean variance of the actual physical receiver under the original outer law. -/
def p4Q2PZ37ACK_originalReceiverVarianceMoment
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, Var (F b hb f₀ e z) ∂outer
local notation "Vbar" => p4Q2PZ37ACK_originalReceiverVarianceMoment H

/-- Mean of the original scalar energy-regression defect, with no recentering. -/
def p4Q2PZ37ACK_originalReceiverDefectMoment
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ∂outer
local notation "Dbar" => p4Q2PZ37ACK_originalReceiverDefectMoment H

private theorem p4Q2PZ37ACK_decomposition_receiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : Continuous (F b hb f₀ e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) b hb f₀ e).continuous.comp
      (continuous_const.prodMk continuous_id)

private theorem p4Q2PZ37ACK_decomposition_covariance_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Continuous (C b hb e) :=
  p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f₀ e

private theorem p4Q2PZ37ACK_decomposition_variance_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Continuous (fun z : Pair => Var (F b hb f₀ e z)) :=
  p4Q2PZ37ACD_originalReceiver_variance_continuous H b hb f₀ e

/-- Each coefficient is exactly minus the original covariance at a genuine
gauge-transformed context, with both original boundaries transformed together. -/
theorem p4Q2PZ37ACK_originalFourModeCoefficient_eq_gaugeCovariance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (j : Fin 4) :
    m b hb e z j = -C b hb e (Γ e (q j) z) := by
  have h := p4Q2PZ37ACK_centeredReceiver_covariance_gauge H b hb e (q j) z
  change C b hb e (Γ e (q j) z) = -m b hb e z j at h
  linarith

/-- The remainder is centered under the SAME link Haar measure. -/
theorem p4Q2PZ37ACK_originalFourModeRemainder_mean_zero
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    (∫ g : G, R b hb e z g ∂μ) = 0 := by
  exact CompactFiniteHaarProjection.remainder_mean_zero μ (F b hb f₀ e z) φ
    (p4Q2PZ37ACK_decomposition_receiver_continuous H b hb e z)
    p4Q2PZ37ACK_fourModeCharacter_continuous p4Q2PZ37ACK_fourModeCharacter_mean_zero

/-- Every one of the four actual fundamental Haar modes is orthogonal
to the same unchanged receiver's remainder. -/
theorem p4Q2PZ37ACK_originalFourModeRemainder_orthogonal
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (j : Fin 4) :
    (∫ g : G, R b hb e z g * φ j g ∂μ) = 0 := by
  exact CompactFiniteHaarProjection.remainder_orthogonal μ (F b hb f₀ e z) φ
    (p4Q2PZ37ACK_decomposition_receiver_continuous H b hb e z)
    p4Q2PZ37ACK_fourModeCharacter_continuous p4Q2PZ37ACK_fourModeCharacter_mean_zero
    p4Q2PZ37ACK_fourModeCharacter_gram j

/-- Exact four-mode square completion of the original physical receiver. -/
theorem p4Q2PZ37ACK_originalFourModeResidualEnergy_eq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    Wz b hb e z = Var (F b hb f₀ e z) - 4 * ∑ j : Fin 4, (m b hb e z j) ^ 2 := by
  exact CompactFiniteHaarProjection.pythagoras μ (F b hb f₀ e z) φ
    (p4Q2PZ37ACK_decomposition_receiver_continuous H b hb e z)
    p4Q2PZ37ACK_fourModeCharacter_continuous p4Q2PZ37ACK_fourModeCharacter_mean_zero
    p4Q2PZ37ACK_fourModeCharacter_gram

/-- Nonnegativity is proved from the actual residual square, not assumed. -/
theorem p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : 0 ≤ Wz b hb e z :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- The same nonnegativity holds after taking the original outer Haar mean. -/
theorem p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : 0 ≤ W b hb e :=
  integral_nonneg (p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg H b hb e)

private theorem p4Q2PZ37ACK_decomposition_coefficient_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (j : Fin 4) :
    Continuous (fun z : Pair => m b hb e z j) := by
  have hc := p4Q2PZ37ACK_decomposition_covariance_continuous H b hb e
  have hg : Continuous (Γ e (q j)) :=
    (p4Q2PZ37ACK_originalGaugePair_continuous H e).comp
      (continuous_const.prodMk continuous_id)
  have heq : (fun z : Pair => m b hb e z j) =
      (fun z : Pair => -C b hb e (Γ e (q j) z)) := by
    funext z
    exact p4Q2PZ37ACK_originalFourModeCoefficient_eq_gaugeCovariance H b hb e z j
  rw [heq]
  exact (hc.comp hg).neg

private theorem p4Q2PZ37ACK_decomposition_squareSum_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Continuous (fun z : Pair => ∑ j : Fin 4, (m b hb e z j) ^ 2) := by
  exact continuous_finset_sum _ fun j _ =>
    (p4Q2PZ37ACK_decomposition_coefficient_continuous H b hb e j).pow 2

private theorem p4Q2PZ37ACK_decomposition_residual_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Continuous (Wz b hb e) := by
  have heq : Wz b hb e = fun z : Pair =>
      Var (F b hb f₀ e z) - 4 * ∑ j : Fin 4, (m b hb e z j) ^ 2 := by
    funext z
    exact p4Q2PZ37ACK_originalFourModeResidualEnergy_eq H b hb e z
  rw [heq]
  exact (p4Q2PZ37ACK_decomposition_variance_continuous H b hb e).sub
    (continuous_const.mul (p4Q2PZ37ACK_decomposition_squareSum_continuous H b hb e))

/-- Genuine outer gauge invariance makes ALL FOUR coefficient-square
moments equal to ACJ's actual S, without an isotropy hypothesis. -/
theorem p4Q2PZ37ACK_originalFourModeCoefficient_outerSquare
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (j : Fin 4) :
    (∫ z : Pair, (m b hb e z j) ^ 2 ∂outer) = S b hb e := by
  have hm := p4Q2PZ37ACK_originalGaugePair_measurePreserving H e (q j)
  have hc := (p4Q2PZ37ACK_decomposition_covariance_continuous H b hb e).pow 2
  have hi : (∫ z : Pair, (C b hb e z) ^ 2 ∂Measure.map (Γ e (q j)) outer) =
      ∫ z : Pair, (C b hb e (Γ e (q j) z)) ^ 2 ∂outer :=
    integral_map_of_stronglyMeasurable hm.measurable hc.stronglyMeasurable
  rw [hm.map_eq] at hi
  calc
    _ = ∫ z : Pair, (C b hb e (Γ e (q j) z)) ^ 2 ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      rw [p4Q2PZ37ACK_originalFourModeCoefficient_eq_gaugeCovariance, neg_sq]
    _ = ∫ z : Pair, (C b hb e z) ^ 2 ∂outer := hi.symm
    _ = S b hb e := rfl

private theorem p4Q2PZ37ACK_decomposition_squareSum_integral
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, (∑ j : Fin 4, (m b hb e z j) ^ 2) ∂outer) = 4 * S b hb e := by
  have hi (j : Fin 4) : Integrable (fun z : Pair => (m b hb e z j) ^ 2) outer :=
    ((p4Q2PZ37ACK_decomposition_coefficient_continuous H b hb e j).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum _ (fun j _ => hi j)]
  simp_rw [p4Q2PZ37ACK_originalFourModeCoefficient_outerSquare H b hb e]
  simp

/-- Exact variance allocation: four equal outer mode moments and the
actual nonnegative higher-mode remainder. -/
theorem p4Q2PZ37ACK_originalVarianceMoment_eq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Vbar b hb e = 16 * S b hb e + W b hb e := by
  have hV : Integrable (fun z : Pair => Var (F b hb f₀ e z)) outer :=
    (p4Q2PZ37ACK_decomposition_variance_continuous H b hb e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hM : Integrable (fun z : Pair => 4 * ∑ j : Fin 4, (m b hb e z j) ^ 2) outer :=
    (continuous_const.mul (p4Q2PZ37ACK_decomposition_squareSum_continuous H b hb e)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hW : W b hb e = Vbar b hb e - 16 * S b hb e := by
    unfold p4Q2PZ37ACK_originalFourModeResidualMoment
    simp_rw [p4Q2PZ37ACK_originalFourModeResidualEnergy_eq]
    rw [integral_sub hV hM, integral_const_mul,
      p4Q2PZ37ACK_decomposition_squareSum_integral]
    change Vbar b hb e - 4 * (4 * S b hb e) = Vbar b hb e - 16 * S b hb e
    ring
  linarith

/-- The original scalar energy defect retains the OTHER three fundamental
modes, plus the actual higher-mode remainder, after genuine outer averaging. -/
theorem p4Q2PZ37ACK_originalDefectMoment_eq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Dbar b hb e = 12 * S b hb e + W b hb e := by
  have hV : Integrable (fun z : Pair => Var (F b hb f₀ e z)) outer :=
    (p4Q2PZ37ACK_decomposition_variance_continuous H b hb e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hC : Integrable (fun z : Pair => 4 * (C b hb e z) ^ 2) outer :=
    (continuous_const.mul ((p4Q2PZ37ACK_decomposition_covariance_continuous H b hb e).pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold p4Q2PZ37ACK_originalReceiverDefectMoment
  rw [integral_sub hV hC, integral_const_mul]
  change Vbar b hb e - 4 * S b hb e = 12 * S b hb e + W b hb e
  rw [p4Q2PZ37ACK_originalVarianceMoment_eq]
  ring

/-- Genuine four-mode isotropy improves the SAME FC envelope by a factor
of four. The true transfer norm and physical source norm remain in B. -/
theorem p4Q2PZ37ACK_originalCovarianceSecondMoment_le_FC_sixteenth
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : S b hb e ≤ (B b hb) ^ 2 / 16 := by
  have hV : Vbar b hb e ≤ (B b hb) ^ 2 := by
    have hi : Integrable (fun z : Pair => Var (F b hb f₀ e z)) outer :=
      (p4Q2PZ37ACK_decomposition_variance_continuous H b hb e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      Vbar b hb e ≤ ∫ _z : Pair, (B b hb) ^ 2 ∂outer := by
        apply integral_mono hi (integrable_const _)
        intro z
        exact p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb f₀ e z
      _ = (B b hb) ^ 2 := by simp
  have hw := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb e
  rw [p4Q2PZ37ACK_originalVarianceMoment_eq] at hV
  linarith

/-- At every finite volume, positive coupling and actual link, the actual
average scalar regression defect is strictly positive and at least 12*S. -/
theorem p4Q2PZ37ACK_originalDefectMoment_positive_floor
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < 12 * S b hb.le e ∧ 12 * S b hb.le e ≤ Dbar b hb.le e := by
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hw := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e
  rw [p4Q2PZ37ACK_originalDefectMoment_eq]
  constructor <;> linarith

/-- At least three quarters of the actual mean variance remain after
regression onto the SINGLE scalar Wilson energy. -/
theorem p4Q2PZ37ACK_originalDefectMoment_threeQuarters
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : (3 / 4 : ℝ) * Vbar b hb e ≤ Dbar b hb e := by
  have hw := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb e
  rw [p4Q2PZ37ACK_originalVarianceMoment_eq, p4Q2PZ37ACK_originalDefectMoment_eq]
  linarith

private theorem p4Q2PZ37ACK_decomposition_defect_integrable
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Integrable (fun z : Pair => Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2) outer :=
  ((p4Q2PZ37ACK_decomposition_variance_continuous H b hb e).sub
    (continuous_const.mul ((p4Q2PZ37ACK_decomposition_covariance_continuous H b hb e).pow 2))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- No almost-everywhere original scalar defect/covariance-square ratio
below 12 can hold at any finite H,b>0,e. Selected regions remain possible. -/
theorem p4Q2PZ37ACK_no_ae_defect_covariance_ratio
    (b : ℝ) (hb : 0 < b) (e : Link) (theta : ℝ) (htheta : theta < 12) :
    ¬ (∀ᵐ z : Pair ∂outer,
      Var (F b hb.le f₀ e z) - 4 * (C b hb.le e z) ^ 2 ≤
        theta * (C b hb.le e z) ^ 2) := by
  intro hCap
  have hC : Integrable (fun z : Pair => theta * (C b hb.le e z) ^ 2) outer :=
    (continuous_const.mul ((p4Q2PZ37ACK_decomposition_covariance_continuous H b hb.le e).pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := integral_mono_ae
    (p4Q2PZ37ACK_decomposition_defect_integrable H b hb.le e) hC hCap
  rw [integral_const_mul] at hi
  change Dbar b hb.le e ≤ theta * S b hb.le e at hi
  have hLower := (p4Q2PZ37ACK_originalDefectMoment_positive_floor H b hb e).2
  have hStrict := mul_lt_mul_of_pos_right htheta
    (p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e)
  linarith

/-- In particular no all-context defect/covariance-square cap below 12
can be assigned to this same original physical receiver. -/
theorem p4Q2PZ37ACK_no_allContext_defect_covariance_ratio
    (b : ℝ) (hb : 0 < b) (e : Link) (theta : ℝ) (htheta : theta < 12) :
    ¬ (∀ z : Pair,
      Var (F b hb.le f₀ e z) - 4 * (C b hb.le e z) ^ 2 ≤
        theta * (C b hb.le e z) ^ 2) := by
  intro hCap
  exact p4Q2PZ37ACK_no_ae_defect_covariance_ratio H b hb e theta htheta
    (Filter.Eventually.of_forall hCap)

/-- No almost-everywhere original scalar defect/variance ratio below
three quarters is compatible with the genuine four-mode Haar allocation. -/
theorem p4Q2PZ37ACK_no_ae_defect_variance_ratio
    (b : ℝ) (hb : 0 < b) (e : Link) (theta : ℝ) (htheta : theta < (3 / 4 : ℝ)) :
    ¬ (∀ᵐ z : Pair ∂outer,
      Var (F b hb.le f₀ e z) - 4 * (C b hb.le e z) ^ 2 ≤
        theta * Var (F b hb.le f₀ e z)) := by
  intro hCap
  have hV : Integrable (fun z : Pair => theta * Var (F b hb.le f₀ e z)) outer :=
    (continuous_const.mul (p4Q2PZ37ACK_decomposition_variance_continuous H b hb.le e)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := integral_mono_ae
    (p4Q2PZ37ACK_decomposition_defect_integrable H b hb.le e) hV hCap
  rw [integral_const_mul] at hi
  change Dbar b hb.le e ≤ theta * Vbar b hb.le e at hi
  have hLower := p4Q2PZ37ACK_originalDefectMoment_threeQuarters H b hb.le e
  have hS := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hW := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e
  have hVpos : 0 < Vbar b hb.le e := by
    rw [p4Q2PZ37ACK_originalVarianceMoment_eq]
    linarith
  have hStrict := mul_lt_mul_of_pos_right htheta hVpos
  linarith

/-- The same obstruction excludes an all-context ratio below three quarters. -/
theorem p4Q2PZ37ACK_no_allContext_defect_variance_ratio
    (b : ℝ) (hb : 0 < b) (e : Link) (theta : ℝ) (htheta : theta < (3 / 4 : ℝ)) :
    ¬ (∀ z : Pair,
      Var (F b hb.le f₀ e z) - 4 * (C b hb.le e z) ^ 2 ≤
        theta * Var (F b hb.le f₀ e z)) := by
  intro hCap
  exact p4Q2PZ37ACK_no_ae_defect_variance_ratio H b hb e theta htheta
    (Filter.Eventually.of_forall hCap)

/-- Fully numerical upper bound for the SAME covariance moment, retaining
the genuine finite slab action budget and physical source norm. -/
theorem p4Q2PZ37ACK_originalCovarianceSecondMoment_le_numeric
    (b : ℝ) (hb : 0 < b) (e : Link) :
    S b hb.le e ≤ 36 * b ^ 2 *
      Real.exp ((2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H + 48) * b) *
        ‖f₀‖ ^ 2 := by
  let A := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let U : ℝ := 576 * b ^ 2 * Real.exp ((2 * A + 48) * b) * ‖f₀‖ ^ 2
  have hV : Vbar b hb.le e ≤ U := by
    have hi : Integrable (fun z : Pair => Var (F b hb.le f₀ e z)) outer :=
      (p4Q2PZ37ACK_decomposition_variance_continuous H b hb.le e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      Vbar b hb.le e ≤ ∫ _z : Pair, U ∂outer := by
        apply integral_mono hi (integrable_const _)
        intro z
        exact p4Q2PZ37ACJ_originalReceiver_variance_le_numericBudget H b hb f₀ e z
      _ = U := by simp
  have hw := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e
  rw [p4Q2PZ37ACK_originalVarianceMoment_eq] at hV
  change S b hb.le e ≤ 36 * b ^ 2 * Real.exp ((2 * A + 48) * b) * ‖f₀‖ ^ 2
  dsimp [U] at hV
  linarith

/-- The original plaquette count makes the H dependence explicit. This is
an upper estimate and supplies no new numerical or uniform positive floor. -/
theorem p4Q2PZ37ACK_originalCovarianceSecondMoment_le_plaquetteBudget
    (b : ℝ) (hb : 0 < b) (e : Link) :
    S b hb.le e ≤
      216 * (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) * b ^ 2 *
        Real.exp ((2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H + 48) * b) := by
  let A := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let P : ℝ := Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H)
  have hNorm : ‖f₀‖ ^ 2 ≤ 6 * P := by
    simpa only [Fintype.card_eq_nat_card] using
      (p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount H)
  have hScale : 0 ≤ 36 * b ^ 2 * Real.exp ((2 * A + 48) * b) := by positivity
  calc
    S b hb.le e ≤ 36 * b ^ 2 * Real.exp ((2 * A + 48) * b) * ‖f₀‖ ^ 2 :=
      p4Q2PZ37ACK_originalCovarianceSecondMoment_le_numeric H b hb e
    _ ≤ (36 * b ^ 2 * Real.exp ((2 * A + 48) * b)) * (6 * P) :=
      mul_le_mul_of_nonneg_left hNorm hScale
    _ = _ := by dsimp [A, P]; ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalFourModeCoefficient_eq_gaugeCovariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalFourModeRemainder_mean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalFourModeRemainder_orthogonal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalFourModeResidualEnergy_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalFourModeCoefficient_outerSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalVarianceMoment_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalDefectMoment_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalCovarianceSecondMoment_le_FC_sixteenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalDefectMoment_positive_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalDefectMoment_threeQuarters
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_no_ae_defect_covariance_ratio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_no_allContext_defect_covariance_ratio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_no_ae_defect_variance_ratio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_no_allContext_defect_variance_ratio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalCovarianceSecondMoment_le_numeric
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalCovarianceSecondMoment_le_plaquetteBudget
