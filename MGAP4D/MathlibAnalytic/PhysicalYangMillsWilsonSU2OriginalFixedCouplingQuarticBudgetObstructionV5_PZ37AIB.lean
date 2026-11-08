import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalThirdOrderTaylorQuarticRemainderV5_PZ37AIA
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIB — original fixed-coupling quartic budget obstruction

Keep the same original even periodic lattice, full Wilson action, both
spatial halfweights, signed ZW source, product Haar, physical transfer,
typed history, canonical root and fixed Lean/mathlib/workflows.

An explicit restriction/zero-extension equivalence counts the ACTUAL
primary spatial slice. The SAME plaquette list used by AFZ satisfies
p_H = 24*(H+1)^3, including p_0=24 and p_H>=192 for H>=1.

The original source bound gives V_H <= (p_H/2)*M_H. The unchanged coupling
beta0=log(3/2)/64 lies in [1/192,1/128]. The unchanged right-boundary cap
C_B is at least 3*p_H. These imply, for every real beta, the BUDGET floor
  E4_B >= (27/8)*(beta*p_H)^3*(beta*V_H).
This is not a lower bound on the actual fourth-order remainder.

For beta>0, AIA's coarse half-variance and scaled quartic margins are
equivalent, and either requires 81*(beta*p_H)^3<12. At the ORIGINAL fixed
coupling this necessary count-only condition holds exactly when H=0.
For every H>=1 and every original right boundary, E4_B is at least
(27/8)*beta0*V_H, strictly greater than beta0*V_H/2. Both coarse margins
are therefore impossible. H=0 merely passes the necessary count-only
condition; a sufficient-margin witness there remains unproved.

No failure of a correlation-retaining weighted certificate is inferred.
No actual fixed-coupling transfer sign, positive/negative shells,
volume-uniform coercivity, Hamiltonian gap or continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Clearing the common positive factor beta/48 gives exactly the scaled
quartic margin. No sign assumption on C, M or V is needed for this identity. -/
theorem p4Q2PZ37AIB_real_quarticMargin_iff_scaled
    (beta C M V : ℝ) (hbeta : 0 < beta) :
    ((beta * C) ^ 4 / 48) * M < beta * V / 2 ↔
      beta ^ 3 * C ^ 4 * M < 24 * V := by
  have hBudget :
      ((beta * C) ^ 4 / 48) * M =
        (beta / 48) * (beta ^ 3 * C ^ 4 * M) := by ring
  have hSignal : beta * V / 2 = (beta / 48) * (24 * V) := by ring
  rw [hBudget, hSignal]
  exact mul_lt_mul_iff_right₀ (div_pos hbeta (by norm_num))

/-- The cap C >= 3p and moment inequality 2V <= pM force a quantitative
lower bound on the coarse quartic budget. Only even powers of beta enter,
so beta need not be positive. V itself need not be nonnegative here. -/
theorem p4Q2PZ37AIB_real_quarticBudget_lowerBound
    (p M V C beta : ℝ)
    (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hVariance : V ≤ p * M / 2) (hCap : 3 * p ≤ C) :
    (27 / 8 : ℝ) * (beta * p) ^ 3 * (beta * V) ≤
      ((beta * C) ^ 4 / 48) * M := by
  have hMass : 2 * V ≤ p * M := by
    linarith only [hVariance]
  have hBetaFourth : 0 ≤ beta ^ 4 := by positivity
  have hCapFourth : (3 * p) ^ 4 ≤ C ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hp) hCap 4
  have hCapCoefficient : 0 ≤ beta ^ 4 / 48 :=
    div_nonneg hBetaFourth (by norm_num)
  have hMassCoefficient : 0 ≤ (27 / 16 : ℝ) * beta ^ 4 * p ^ 3 :=
    mul_nonneg
      (mul_nonneg (by norm_num) hBetaFourth)
      (pow_nonneg hp 3)
  calc
    (27 / 8 : ℝ) * (beta * p) ^ 3 * (beta * V) =
        ((27 / 16 : ℝ) * beta ^ 4 * p ^ 3) * (2 * V) := by ring
    _ ≤ ((27 / 16 : ℝ) * beta ^ 4 * p ^ 3) * (p * M) :=
      mul_le_mul_of_nonneg_left hMass hMassCoefficient
    _ = (beta ^ 4 / 48) * (3 * p) ^ 4 * M := by ring
    _ ≤ (beta ^ 4 / 48) * C ^ 4 * M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCapFourth hCapCoefficient) hM
    _ = ((beta * C) ^ 4 / 48) * M := by ring

/-- A successful coarse scaled margin necessarily has small beta*p.
Strict positivity of beta and V justifies cancellation of beta*V. -/
theorem p4Q2PZ37AIB_real_scaledQuarticMargin_necessary
    (p M V C beta : ℝ)
    (hp : 0 ≤ p) (hM : 0 ≤ M) (hV : 0 < V)
    (hVariance : V ≤ p * M / 2) (hCap : 3 * p ≤ C)
    (hbeta : 0 < beta)
    (hMargin : beta ^ 3 * C ^ 4 * M < 24 * V) :
    81 * (beta * p) ^ 3 < 12 := by
  have hBudget : ((beta * C) ^ 4 / 48) * M < beta * V / 2 :=
    (p4Q2PZ37AIB_real_quarticMargin_iff_scaled beta C M V hbeta).mpr hMargin
  have hLower := p4Q2PZ37AIB_real_quarticBudget_lowerBound
    p M V C beta hp hM hVariance hCap
  have hSignal : 0 < beta * V := mul_pos hbeta hV
  have hProduct :
      ((27 / 8 : ℝ) * (beta * p) ^ 3) * (beta * V) <
        (1 / 2 : ℝ) * (beta * V) := by
    calc
      ((27 / 8 : ℝ) * (beta * p) ^ 3) * (beta * V) ≤
          ((beta * C) ^ 4 / 48) * M := hLower
      _ < beta * V / 2 := hBudget
      _ = (1 / 2 : ℝ) * (beta * V) := by ring
  have hSmall : (27 / 8 : ℝ) * (beta * p) ^ 3 < (1 / 2 : ℝ) :=
    (mul_lt_mul_iff_left₀ hSignal).mp hProduct
  linarith only [hSmall]

/-- If beta*p >= 1, both equivalent coarse quartic margins fail.
This is an obstruction to those sufficient conditions only. -/
theorem p4Q2PZ37AIB_real_coarseQuarticMargins_impossible
    (p M V C beta : ℝ)
    (hp : 0 ≤ p) (hM : 0 ≤ M) (hV : 0 < V)
    (hVariance : V ≤ p * M / 2) (hCap : 3 * p ≤ C)
    (hbeta : 0 < beta) (hLarge : 1 ≤ beta * p) :
    ¬ (beta ^ 3 * C ^ 4 * M < 24 * V) ∧
      ¬ (((beta * C) ^ 4 / 48) * M < beta * V / 2) := by
  have hCube : (1 : ℝ) ≤ (beta * p) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hLarge 3
    simpa only [one_pow] using h
  have hNoScaled : ¬ (beta ^ 3 * C ^ 4 * M < 24 * V) := by
    intro hMargin
    have hNecessary := p4Q2PZ37AIB_real_scaledQuarticMargin_necessary
      p M V C beta hp hM hV hVariance hCap hbeta hMargin
    linarith only [hCube, hNecessary]
  refine ⟨hNoScaled, ?_⟩
  intro hBudget
  exact hNoScaled
    ((p4Q2PZ37AIB_real_quarticMargin_iff_scaled beta C M V hbeta).mp hBudget)

namespace GroundStatePosteriorJoint

/-- The three actual spatial axes of the original four-dimensional lattice. -/
theorem p4Q2PZ37AIB_spatialDirection_card :
    Nat.card PeriodicHypercubicEvenSpatialDirection = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The actual increasing spatial direction pairs have three elements. -/
theorem p4Q2PZ37AIB_spatialDirectionPair_card :
    Nat.card PeriodicHypercubicEvenSpatialDirectionPair = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Restrict an original primary-plane vertex to its spatial coordinates;
the inverse inserts the prescribed zero time coordinate. -/
def p4Q2PZ37AIB_originalSliceVertexEquiv (H : ℕ) :
    PeriodicHypercubicEvenSpatialSliceVertex H ≃
      (PeriodicHypercubicEvenSpatialDirection →
        ZMod (PeriodicHypercubicEvenSideLength H)) where
  toFun v mu := v.1 mu.1
  invFun x :=
    ⟨fun mu => if hmu : mu = 0 then 0 else x ⟨mu, hmu⟩, by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩
  left_inv v := by
    apply Subtype.ext
    funext mu
    change (if hmu : mu = 0 then 0 else
      v.1 (⟨mu, hmu⟩ : PeriodicHypercubicEvenSpatialDirection).1) = v.1 mu
    by_cases hmu : mu = 0
    · subst mu
      simpa only [dif_pos rfl] using
        (show v.1 0 = 0 from v.2).symm
    · simp only [dif_neg hmu]
  right_inv x := by
    funext mu
    change (if hmu : mu.1 = 0 then 0 else x ⟨mu.1, hmu⟩) = x mu
    simp only [dif_neg mu.2]

/-- There are exactly L^3 vertices on the original primary spatial slice. -/
theorem p4Q2PZ37AIB_originalSliceVertex_card (H : ℕ) :
    Nat.card (PeriodicHypercubicEvenSpatialSliceVertex H) =
      (PeriodicHypercubicEvenSideLength H) ^ 3 := by
  calc
    Nat.card (PeriodicHypercubicEvenSpatialSliceVertex H) =
        Nat.card (PeriodicHypercubicEvenSpatialDirection →
          ZMod (PeriodicHypercubicEvenSideLength H)) :=
      Nat.card_congr (p4Q2PZ37AIB_originalSliceVertexEquiv H)
    _ = (PeriodicHypercubicEvenSideLength H) ^ 3 := by
      rw [Nat.card_fun, Nat.card_zmod, p4Q2PZ37AIB_spatialDirection_card]

/-- The actual positive spatial links number 3*L^3. -/
theorem p4Q2PZ37AIB_originalSliceLink_card (H : ℕ) :
    Nat.card (PeriodicHypercubicEvenSpatialSliceLink H) =
      3 * (PeriodicHypercubicEvenSideLength H) ^ 3 := by
  change Nat.card (PeriodicHypercubicEvenSpatialSliceVertex H ×
    PeriodicHypercubicEvenSpatialDirection) =
      3 * (PeriodicHypercubicEvenSideLength H) ^ 3
  rw [Nat.card_prod, p4Q2PZ37AIB_originalSliceVertex_card,
    p4Q2PZ37AIB_spatialDirection_card]
  exact Nat.mul_comm _ _

/-- The actual spatial plaquettes number 3*L^3. -/
theorem p4Q2PZ37AIB_originalSlicePlaquette_card (H : ℕ) :
    Nat.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) =
      3 * (PeriodicHypercubicEvenSideLength H) ^ 3 := by
  change Nat.card (PeriodicHypercubicEvenSpatialSliceVertex H ×
    PeriodicHypercubicEvenSpatialDirectionPair) =
      3 * (PeriodicHypercubicEvenSideLength H) ^ 3
  rw [Nat.card_prod, p4Q2PZ37AIB_originalSliceVertex_card,
    p4Q2PZ37AIB_spatialDirectionPair_card]
  exact Nat.mul_comm _ _

/-- The canonical original list enumerates precisely that carrier. -/
theorem p4Q2PZ37AIB_originalPlaquetteList_length (H : ℕ) :
    (periodicHypercubicEvenSpatialSlicePlaquetteList H).length =
      3 * (PeriodicHypercubicEvenSideLength H) ^ 3 := by
  simpa only [periodicHypercubicEvenSpatialSlicePlaquetteList,
    Finset.length_toList, Finset.card_univ, Fintype.card_eq_nat_card] using
      p4Q2PZ37AIB_originalSlicePlaquette_card H

/-- Exact AFZ count at every original finite volume, including H=0. -/
theorem p4Q2PZ37AIB_plaquetteCount_exact (H : ℕ) :
    p4Q2PZ37AFZ_plaquetteCount H = 24 * ((H : ℝ) + 1) ^ 3 := by
  unfold p4Q2PZ37AFZ_plaquetteCount
  rw [p4Q2PZ37AIB_originalPlaquetteList_length H]
  simp only [PeriodicHypercubicEvenSideLength, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The smallest original periodic lattice has exactly 24 spatial plaquettes. -/
theorem p4Q2PZ37AIB_plaquetteCount_zero :
    p4Q2PZ37AFZ_plaquetteCount 0 = 24 := by
  norm_num [p4Q2PZ37AIB_plaquetteCount_exact]

/-- The next original periodic lattice has exactly 192 spatial plaquettes. -/
theorem p4Q2PZ37AIB_plaquetteCount_one :
    p4Q2PZ37AFZ_plaquetteCount 1 = 192 := by
  norm_num [p4Q2PZ37AIB_plaquetteCount_exact]

/-- Every original H>=1 volume has at least 192 spatial plaquettes. -/
theorem p4Q2PZ37AIB_plaquetteCount_ge_192 (H : ℕ) (hH : 1 ≤ H) :
    (192 : ℝ) ≤ p4Q2PZ37AFZ_plaquetteCount H := by
  have hHreal : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hCube : (2 : ℝ) ^ 3 ≤ ((H : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith only [hHreal]) 3
  rw [p4Q2PZ37AIB_plaquetteCount_exact H]
  nlinarith only [hCube]

end GroundStatePosteriorJoint

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIB_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIB_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIB_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIB_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIB_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "CB" => p4Q2PZ37AHY_originalBoundaryActionBudget H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AIB_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The true signed continuous source square is dominated by its original
absolute value times the exact AGN half-count envelope. -/
theorem p4Q2PZ37AIB_originalSourceSquare_le_halfCount_abs
    (A : Cfg) : (fCont A) ^ 2 ≤ (pH / 2) * |fCont A| := by
  calc
    (fCont A) ^ 2 = |fCont A| ^ 2 := (sq_abs _).symm
    _ = |fCont A| * |fCont A| := pow_two _
    _ ≤ (pH / 2) * |fCont A| :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A)
        (abs_nonneg _)

/-- Actual Haar source variance versus actual Haar L1 mass, with the
AHN continuous-representative bridge and no source positivity assumption. -/
theorem p4Q2PZ37AIB_originalSourceSecondMoment_le_halfCount_L1Mass :
    Vsrc ≤ (pH / 2) * Msrc := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hSquare : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbs : Integrable (fun A : Cfg => |fCont A|) muH :=
    hf.abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    Vsrc = (∫ A : Cfg, (fCont A) ^ 2 ∂muH) := rfl
    _ ≤ (∫ A : Cfg, (pH / 2) * |fCont A| ∂muH) :=
      integral_mono hSquare (hAbs.const_mul (pH / 2))
        (fun A => p4Q2PZ37AIB_originalSourceSquare_le_halfCount_abs H A)
    _ = (pH / 2) * Msrc := by
      rw [integral_const_mul,
        ← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H]

/-- An exact rational lower bound for the unchanged original fixed
coupling log(3/2)/64, using mathlib's logarithm inequality at 3/2. -/
theorem p4Q2PZ37AIB_fixedCoupling_ge_oneDiv192 :
    (1 / 192 : ℝ) ≤ beta0 := by
  have hlog := Real.one_sub_inv_le_log_of_pos
    (x := (3 / 2 : ℝ)) (by norm_num)
  norm_num at hlog
  unfold p4Q2PZ37ADC_fixedCoupling
  linarith only [hlog]

/-- The existing boundary action budget is at least three times the
original plaquette count, since the retained right Wilson halfweight is nonnegative. -/
theorem p4Q2PZ37AIB_originalBoundaryActionBudget_ge_threeCount
    (B : Cfg) : 3 * pH ≤ CB B := by
  have hW : 0 ≤ W B :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) B
  unfold p4Q2PZ37AHY_originalBoundaryActionBudget
  linarith only [hW]

local notation "E4B" => p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget H

/-- At positive coupling, AIA's two coarse sufficient margins are exactly
equivalent for the same original source, variance and boundary budget. -/
theorem p4Q2PZ37AIB_originalQuarticMargin_iff_scaled
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) :
    E4B beta B < beta * Vsrc / 2 ↔
      beta ^ 3 * (CB B) ^ 4 * Msrc < 24 * Vsrc := by
  unfold p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget
  exact p4Q2PZ37AIB_real_quarticMargin_iff_scaled
    beta (CB B) Msrc Vsrc hbeta

/-- This is a lower bound on the COARSE BUDGET, not on the actual remainder.
It holds for every real beta and uses the genuine source moments. -/
theorem p4Q2PZ37AIB_originalQuarticBudget_varianceLowerBound
    (beta : ℝ) (B : Cfg) :
    (27 / 8 : ℝ) * (beta * pH) ^ 3 * (beta * Vsrc) ≤ E4B beta B := by
  have hVariance : Vsrc ≤ pH * Msrc / 2 := by
    calc
      Vsrc ≤ (pH / 2) * Msrc :=
        p4Q2PZ37AIB_originalSourceSecondMoment_le_halfCount_L1Mass H
      _ = pH * Msrc / 2 := by ring
  unfold p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget
  exact p4Q2PZ37AIB_real_quarticBudget_lowerBound
    pH Msrc Vsrc (CB B) beta
    (p4Q2PZ37AHN_count_pos H).le
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).1.le
    hVariance (p4Q2PZ37AIB_originalBoundaryActionBudget_ge_threeCount H B)

/-- A successful coarse scaled margin must lie in this count-dependent
coupling range. No actual-transfer sign is asserted by the converse. -/
theorem p4Q2PZ37AIB_originalScaledQuarticMargin_necessary
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg)
    (hMargin : beta ^ 3 * (CB B) ^ 4 * Msrc < 24 * Vsrc) :
    81 * (beta * pH) ^ 3 < 12 := by
  have hVariance : Vsrc ≤ pH * Msrc / 2 := by
    calc
      Vsrc ≤ (pH / 2) * Msrc :=
        p4Q2PZ37AIB_originalSourceSecondMoment_le_halfCount_L1Mass H
      _ = pH * Msrc / 2 := by ring
  exact p4Q2PZ37AIB_real_scaledQuarticMargin_necessary
    pH Msrc Vsrc (CB B) beta
    (p4Q2PZ37AHN_count_pos H).le
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).1.le
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
    hVariance (p4Q2PZ37AIB_originalBoundaryActionBudget_ge_threeCount H B)
    hbeta hMargin

theorem p4Q2PZ37AIB_originalHalfVarianceQuarticMargin_necessary
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg)
    (hMargin : E4B beta B < beta * Vsrc / 2) :
    81 * (beta * pH) ^ 3 < 12 :=
  p4Q2PZ37AIB_originalScaledQuarticMargin_necessary H beta hbeta B
    ((p4Q2PZ37AIB_originalQuarticMargin_iff_scaled H beta hbeta B).mp hMargin)

/-- Once beta*p_H reaches one, neither of the two coarse sufficient
margins can hold. This does not decide the original transfer sign. -/
theorem p4Q2PZ37AIB_originalCoarseQuarticMargins_impossible_of_largeCount
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) (hLarge : 1 ≤ beta * pH) :
    ¬ (beta ^ 3 * (CB B) ^ 4 * Msrc < 24 * Vsrc) ∧
      ¬ (E4B beta B < beta * Vsrc / 2) := by
  have hVariance : Vsrc ≤ pH * Msrc / 2 := by
    calc
      Vsrc ≤ (pH / 2) * Msrc :=
        p4Q2PZ37AIB_originalSourceSecondMoment_le_halfCount_L1Mass H
      _ = pH * Msrc / 2 := by ring
  unfold p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget
  exact p4Q2PZ37AIB_real_coarseQuarticMargins_impossible
    pH Msrc Vsrc (CB B) beta
    (p4Q2PZ37AHN_count_pos H).le
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).1.le
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
    hVariance (p4Q2PZ37AIB_originalBoundaryActionBudget_ge_threeCount H B)
    hbeta hLarge

/-- Quantitative separation of the coarse budget from the half-variance
target, still with the original full-action boundary cap. -/
theorem p4Q2PZ37AIB_originalQuarticBudget_signalFloor_of_largeCount
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) (hLarge : 1 ≤ beta * pH) :
    (27 / 8 : ℝ) * (beta * Vsrc) ≤ E4B beta B := by
  have hCube : (1 : ℝ) ≤ (beta * pH) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hLarge 3
    simpa only [one_pow] using h
  have hCoef : 0 ≤ (27 / 8 : ℝ) * (beta * Vsrc) :=
    mul_nonneg (by norm_num)
      (mul_nonneg hbeta (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le)
  calc
    (27 / 8 : ℝ) * (beta * Vsrc) =
        ((27 / 8 : ℝ) * (beta * Vsrc)) * 1 := by ring
    _ ≤ ((27 / 8 : ℝ) * (beta * Vsrc)) * (beta * pH) ^ 3 :=
      mul_le_mul_of_nonneg_left hCube hCoef
    _ = (27 / 8 : ℝ) * (beta * pH) ^ 3 * (beta * Vsrc) := by ring
    _ ≤ E4B beta B :=
      p4Q2PZ37AIB_originalQuarticBudget_varianceLowerBound H beta B

/-- Exact rational enclosure of the unchanged original fixed coupling. -/
theorem p4Q2PZ37AIB_fixedCoupling_rationalInterval :
    (1 / 192 : ℝ) ≤ beta0 ∧ beta0 ≤ (1 / 128 : ℝ) :=
  ⟨p4Q2PZ37AIB_fixedCoupling_ge_oneDiv192,
    p4Q2PZ37AHI_fixedCoupling_le_one128⟩

/-- Original finite-volume growth of beta0*p_H, obtained without
floating-point approximations or a rescaled coupling. -/
theorem p4Q2PZ37AIB_originalFixedCoupling_count_cubicFloor :
    ((H : ℝ) + 1) ^ 3 / 8 ≤ beta0 * pH := by
  calc
    ((H : ℝ) + 1) ^ 3 / 8 = (1 / 192 : ℝ) * pH := by
      rw [p4Q2PZ37AIB_plaquetteCount_exact H]
      ring
    _ ≤ beta0 * pH :=
      mul_le_mul_of_nonneg_right p4Q2PZ37AIB_fixedCoupling_ge_oneDiv192
        (p4Q2PZ37AHN_count_pos H).le

/-- At every original volume H>=1, the unchanged fixed coupling times
the actual plaquette count is already at least one. -/
theorem p4Q2PZ37AIB_originalFixedCoupling_count_ge_one (hH : 1 ≤ H) :
    (1 : ℝ) ≤ beta0 * pH := by
  calc
    (1 : ℝ) = (1 / 192 : ℝ) * 192 := by norm_num
    _ ≤ beta0 * pH :=
      mul_le_mul p4Q2PZ37AIB_fixedCoupling_ge_oneDiv192
        (p4Q2PZ37AIB_plaquetteCount_ge_192 H hH)
        (by norm_num) p4Q2PZ37ADC_fixedCoupling_pos.le

/-- Quantitative failure of the coarse half-variance target at the
ORIGINAL fixed coupling and every right boundary when H>=1. -/
theorem p4Q2PZ37AIB_originalFixedQuarticBudget_signalFloor
    (hH : 1 ≤ H) (B : Cfg) :
    (27 / 8 : ℝ) * (beta0 * Vsrc) ≤ E4B beta0 B :=
  p4Q2PZ37AIB_originalQuarticBudget_signalFloor_of_largeCount
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B
    (p4Q2PZ37AIB_originalFixedCoupling_count_ge_one H hH)

/-- The coarse budget is strictly greater than the requested
half-variance margin; this is not a lower bound on the true error. -/
theorem p4Q2PZ37AIB_originalFixedQuarticBudget_gt_halfVariance
    (hH : 1 ≤ H) (B : Cfg) :
    beta0 * Vsrc / 2 < E4B beta0 B := by
  have hFloor := p4Q2PZ37AIB_originalFixedQuarticBudget_signalFloor H hH B
  have hSignal : 0 < beta0 * Vsrc :=
    mul_pos p4Q2PZ37ADC_fixedCoupling_pos
      (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  linarith only [hFloor, hSignal]

/-- Neither AIA coarse sufficient margin can hold at fixed beta0 for
H>=1. Weighted quartic certificates and true transfer signs are untouched. -/
theorem p4Q2PZ37AIB_originalFixedCoarseQuarticMargins_impossible
    (hH : 1 ≤ H) (B : Cfg) :
    ¬ (beta0 ^ 3 * (CB B) ^ 4 * Msrc < 24 * Vsrc) ∧
      ¬ (E4B beta0 B < beta0 * Vsrc / 2) :=
  p4Q2PZ37AIB_originalCoarseQuarticMargins_impossible_of_largeCount
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos B
    (p4Q2PZ37AIB_originalFixedCoupling_count_ge_one H hH)

/-- The necessary count-only condition already fails at every H>=1. -/
theorem p4Q2PZ37AIB_originalFixedNecessaryCriterion_impossible
    (hH : 1 ≤ H) : ¬ (81 * (beta0 * pH) ^ 3 < 12) := by
  have hCube : (1 : ℝ) ≤ (beta0 * pH) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (p4Q2PZ37AIB_originalFixedCoupling_count_ge_one H hH) 3
    simpa only [one_pow] using h
  intro hNecessary
  linarith only [hCube, hNecessary]

/-- The smallest original lattice passes this NECESSARY count-only
test. It does not supply a witness for either original sufficient margin. -/
theorem p4Q2PZ37AIB_originalFixedNecessaryCriterion_zero :
    81 * (beta0 * p4Q2PZ37AFZ_plaquetteCount 0) ^ 3 < 12 := by
  have hUpper : beta0 * p4Q2PZ37AFZ_plaquetteCount 0 ≤ (3 / 16 : ℝ) := by
    rw [p4Q2PZ37AIB_plaquetteCount_zero]
    have hBeta := p4Q2PZ37AHI_fixedCoupling_le_one128
    linarith only [hBeta]
  have hProduct : 0 ≤ beta0 * p4Q2PZ37AFZ_plaquetteCount 0 :=
    mul_nonneg p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37AHN_count_pos 0).le
  have hCube := pow_le_pow_left₀ hProduct hUpper 3
  calc
    81 * (beta0 * p4Q2PZ37AFZ_plaquetteCount 0) ^ 3 ≤
        81 * (3 / 16 : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hCube (by norm_num)
    _ < 12 := by norm_num

/-- Exact volume classification of the necessary count-only test,
not an equivalence with actual transfer negativity or a sufficient margin. -/
theorem p4Q2PZ37AIB_originalFixedNecessaryCriterion_iff_zero :
    81 * (beta0 * pH) ^ 3 < 12 ↔ H = 0 := by
  constructor
  · intro hNecessary
    by_contra hH
    have hLarge : 1 ≤ H := by omega
    exact (p4Q2PZ37AIB_originalFixedNecessaryCriterion_impossible H hLarge) hNecessary
  · intro hH
    subst H
    exact p4Q2PZ37AIB_originalFixedNecessaryCriterion_zero

/-- Any successful original fixed-coupling coarse scaled margin would
have to occur on the smallest lattice. Existence there remains open. -/
theorem p4Q2PZ37AIB_originalFixedScaledQuarticMargin_only_zero
    (B : Cfg)
    (hMargin : beta0 ^ 3 * (CB B) ^ 4 * Msrc < 24 * Vsrc) :
    H = 0 :=
  (p4Q2PZ37AIB_originalFixedNecessaryCriterion_iff_zero H).mp
    (p4Q2PZ37AIB_originalScaledQuarticMargin_necessary
      H beta0 p4Q2PZ37ADC_fixedCoupling_pos B hMargin)

theorem p4Q2PZ37AIB_originalFixedHalfVarianceQuarticMargin_only_zero
    (B : Cfg) (hMargin : E4B beta0 B < beta0 * Vsrc / 2) :
    H = 0 :=
  p4Q2PZ37AIB_originalFixedScaledQuarticMargin_only_zero H B
    ((p4Q2PZ37AIB_originalQuarticMargin_iff_scaled
      H beta0 p4Q2PZ37ADC_fixedCoupling_pos B).mp hMargin)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIB_real_quarticMargin_iff_scaled
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIB_real_quarticBudget_lowerBound
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIB_real_scaledQuarticMargin_necessary
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIB_real_coarseQuarticMargins_impossible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_spatialDirection_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_spatialDirectionPair_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalSliceVertexEquiv
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalSliceVertex_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalSliceLink_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalSlicePlaquette_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalPlaquetteList_length
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_plaquetteCount_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_plaquetteCount_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_plaquetteCount_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_plaquetteCount_ge_192
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalSourceSquare_le_halfCount_abs
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalSourceSecondMoment_le_halfCount_L1Mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_fixedCoupling_ge_oneDiv192
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalBoundaryActionBudget_ge_threeCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalQuarticMargin_iff_scaled
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalQuarticBudget_varianceLowerBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalScaledQuarticMargin_necessary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalHalfVarianceQuarticMargin_necessary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalCoarseQuarticMargins_impossible_of_largeCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalQuarticBudget_signalFloor_of_largeCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_fixedCoupling_rationalInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedCoupling_count_cubicFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedCoupling_count_ge_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedQuarticBudget_signalFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedQuarticBudget_gt_halfVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedCoarseQuarticMargins_impossible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedNecessaryCriterion_impossible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedNecessaryCriterion_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedNecessaryCriterion_iff_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedScaledQuarticMargin_only_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIB_originalFixedHalfVarianceQuarticMargin_only_zero
