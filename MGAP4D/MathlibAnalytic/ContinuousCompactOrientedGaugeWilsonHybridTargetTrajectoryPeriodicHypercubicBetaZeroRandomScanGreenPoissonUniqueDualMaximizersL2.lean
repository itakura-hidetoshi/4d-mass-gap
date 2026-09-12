import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanGreenPoissonFenchelDualityL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local notation "Ω₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
local notation "H₀" =>
  Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
local notation "A₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
local notation "G₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
local notation "GE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
local notation "PE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
local notation "Φ₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
local notation "Ψ₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2

/-- A scalar in the closed unit interval gives at least one half in the
normalized concave quadratic objective. -/
theorem half_le_one_sub_half_mul_sq_of_nonneg_of_le_one
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haLe : a ≤ 1) :
    ((1 : ℝ) / 2) ≤ 1 - ((1 : ℝ) / 2) * a ^ 2 := by
  have hProduct : 0 ≤ a * (1 - a) :=
    mul_nonneg haNonneg (sub_nonneg.mpr haLe)
  nlinarith

/-- The canonical Green-dual unit witness attains the positive, not merely
absolute-value, support value. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenDualUnitWitnessL2_eq_greenEnergyNorm
    (f : Ω₀)
    (hf : f ≠ 0) :
    inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
          f) =
      GE₀ f := by
  have hEnergyNe : GE₀ f ≠ 0 := by
    intro hZero
    exact hf
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        f).1 hZero)
  have hInner :
      inner ℝ (f : H₀) ((G₀ f : Ω₀) : H₀) = GE₀ f ^ 2 := by
    calc
      inner ℝ (f : H₀) ((G₀ f : Ω₀) : H₀) =
          inner ℝ ((G₀ f : Ω₀) : H₀) (f : H₀) := real_inner_comm _ _
      _ =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            f f := rfl
      _ = GE₀ f ^ 2 :=
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
          f).symm
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
  change
    inner ℝ (f : H₀) ((GE₀ f)⁻¹ • ((G₀ f : Ω₀) : H₀)) = GE₀ f
  rw [real_inner_smul_right, hInner]
  field_simp [hEnergyNe]

/-- Every Poisson-energy unit-ball vector is bounded above by the Green support
value. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_le_greenEnergyNorm_of_poissonEnergy_le_one
    (f u : Ω₀)
    (hu : PE₀ u ≤ 1) :
    inner ℝ f u ≤ GE₀ f := by
  calc
    inner ℝ f u ≤ |inner ℝ f u| := le_abs_self _
    _ ≤ GE₀ f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_of_poissonEnergy_le_one
        f u hu

/-- On the Poisson-energy unit ball, the positive Green support value is
attained exactly at the normalized centered Green image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonEnergy_le_one_and_inner_eq_greenEnergyNorm_iff_eq_greenDualUnitWitnessL2
    (f u : Ω₀)
    (hf : f ≠ 0) :
    (PE₀ u ≤ 1 ∧ inner ℝ f u = GE₀ f) ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
          f := by
  constructor
  · rintro ⟨huUnit, hPair⟩
    have hEnergyNe : GE₀ f ≠ 0 := by
      intro hZero
      exact hf
        ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
          f).1 hZero)
    have hEnergyPos : 0 < GE₀ f :=
      lt_of_le_of_ne
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
          f)
        (Ne.symm hEnergyNe)
    let fOne : Ω₀ := (GE₀ f)⁻¹ • f
    have hFOneEnergy : GE₀ fOne = 1 := by
      dsimp [fOne]
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_smul,
        abs_of_pos (inv_pos.mpr hEnergyPos)]
      exact inv_mul_cancel₀ hEnergyNe
    have hPairOne : inner ℝ fOne u = 1 := by
      have hPairAmbient : inner ℝ (f : H₀) (u : H₀) = GE₀ f := hPair
      dsimp [fOne]
      change inner ℝ ((GE₀ f)⁻¹ • (f : H₀)) (u : H₀) = 1
      rw [real_inner_smul_left, hPairAmbient]
      exact inv_mul_cancel₀ hEnergyNe
    have hValueLower : ((1 : ℝ) / 2) ≤ Φ₀ fOne u := by
      have hEnergyNonneg :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
          u
      have hScalar :=
        half_le_one_sub_half_mul_sq_of_nonneg_of_le_one
          (PE₀ u) hEnergyNonneg huUnit
      unfold
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
      rw [hPairOne]
      exact hScalar
    have hValueUpper :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelValueL2_le_half_green_sq
        fOne u
    rw [hFOneEnergy] at hValueUpper
    norm_num at hValueUpper
    have hValueEq : Φ₀ fOne u = ((1 : ℝ) / 2) :=
      le_antisymm hValueUpper hValueLower
    have hFenchelEq :
        Φ₀ fOne u = ((1 : ℝ) / 2) * GE₀ fOne ^ 2 := by
      simpa [hFOneEnergy] using hValueEq
    have hCanonical : u = G₀ fOne :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelValueL2_eq_half_green_sq_iff
        fOne u).1 hFenchelEq
    have hGreenNormalized :
        G₀ fOne =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
            f := by
      unfold
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
      dsimp [fOne]
      rw [map_smul]
    exact hCanonical.trans hGreenNormalized
  · intro hWitness
    subst u
    constructor
    · exact le_of_eq
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenDualUnitWitnessL2_poissonEnergy_eq_one
          f hf)
    · exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenDualUnitWitnessL2_eq_greenEnergyNorm
          f hf

/-- The Green dual support point exists and is unique on the actual
Poisson-energy unit ball. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_poissonEnergy_unitBall_inner_eq_greenEnergyNorm
    (f : Ω₀)
    (hf : f ≠ 0) :
    ∃! u : Ω₀, PE₀ u ≤ 1 ∧ inner ℝ f u = GE₀ f := by
  let witness : Ω₀ :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
      f
  refine ⟨witness, ?_, ?_⟩
  · exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonEnergy_le_one_and_inner_eq_greenEnergyNorm_iff_eq_greenDualUnitWitnessL2
        f witness hf).2 rfl
  · intro u hu
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonEnergy_le_one_and_inner_eq_greenEnergyNorm_iff_eq_greenDualUnitWitnessL2
        f u hf).1 hu

/-- The canonical Poisson-dual unit witness attains the positive support value. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_poissonDualUnitWitnessL2_eq_poissonEnergyNorm
    (u : Ω₀)
    (hu : u ≠ 0) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
          u)
        u =
      PE₀ u := by
  have hEnergyNe : PE₀ u ≠ 0 := by
    intro hZero
    exact hu
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        u).1 hZero)
  have hInner : inner ℝ ((A₀ u : Ω₀) : H₀) (u : H₀) = PE₀ u ^ 2 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
      u).symm
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
  change inner ℝ ((PE₀ u)⁻¹ • ((A₀ u : Ω₀) : H₀)) (u : H₀) = PE₀ u
  rw [real_inner_smul_left, hInner]
  field_simp [hEnergyNe]

/-- Every Green-energy unit-ball vector is bounded above by the Poisson support
value. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_le_poissonEnergyNorm_of_greenEnergy_le_one
    (f u : Ω₀)
    (hf : GE₀ f ≤ 1) :
    inner ℝ f u ≤ PE₀ u := by
  calc
    inner ℝ f u ≤ |inner ℝ f u| := le_abs_self _
    _ ≤ PE₀ u :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_poissonEnergyNorm_of_greenEnergy_le_one
        f u hf

/-- On the Green-energy unit ball, the positive Poisson support value is
attained exactly at the normalized Poisson image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenEnergy_le_one_and_inner_eq_poissonEnergyNorm_iff_eq_poissonDualUnitWitnessL2
    (f u : Ω₀)
    (hu : u ≠ 0) :
    (GE₀ f ≤ 1 ∧ inner ℝ f u = PE₀ u) ↔
      f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
          u := by
  constructor
  · rintro ⟨hfUnit, hPair⟩
    have hEnergyNe : PE₀ u ≠ 0 := by
      intro hZero
      exact hu
        ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
          u).1 hZero)
    have hEnergyPos : 0 < PE₀ u :=
      lt_of_le_of_ne
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
          u)
        (Ne.symm hEnergyNe)
    let uOne : Ω₀ := (PE₀ u)⁻¹ • u
    have hUOneEnergy : PE₀ uOne = 1 := by
      dsimp [uOne]
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_smul,
        abs_of_pos (inv_pos.mpr hEnergyPos)]
      exact inv_mul_cancel₀ hEnergyNe
    have hPairOne : inner ℝ f uOne = 1 := by
      have hPairAmbient : inner ℝ (f : H₀) (u : H₀) = PE₀ u := hPair
      dsimp [uOne]
      change inner ℝ (f : H₀) ((PE₀ u)⁻¹ • (u : H₀)) = 1
      rw [real_inner_smul_right, hPairAmbient]
      exact inv_mul_cancel₀ hEnergyNe
    have hValueLower : ((1 : ℝ) / 2) ≤ Ψ₀ uOne f := by
      have hEnergyNonneg :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
          f
      have hScalar :=
        half_le_one_sub_half_mul_sq_of_nonneg_of_le_one
          (GE₀ f) hEnergyNonneg hfUnit
      unfold
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
      rw [hPairOne]
      exact hScalar
    have hValueUpper :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelValueL2_le_half_poisson_sq
        uOne f
    rw [hUOneEnergy] at hValueUpper
    norm_num at hValueUpper
    have hValueEq : Ψ₀ uOne f = ((1 : ℝ) / 2) :=
      le_antisymm hValueUpper hValueLower
    have hFenchelEq :
        Ψ₀ uOne f = ((1 : ℝ) / 2) * PE₀ uOne ^ 2 := by
      simpa [hUOneEnergy] using hValueEq
    have hCanonical : f = A₀ uOne :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelValueL2_eq_half_poisson_sq_iff
        uOne f).1 hFenchelEq
    have hPoissonNormalized :
        A₀ uOne =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
            u := by
      unfold
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
      dsimp [uOne]
      rw [map_smul]
    exact hCanonical.trans hPoissonNormalized
  · intro hWitness
    subst f
    constructor
    · exact le_of_eq
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDualUnitWitnessL2_greenEnergy_eq_one
          u hu)
    · exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_poissonDualUnitWitnessL2_eq_poissonEnergyNorm
          u hu

/-- The Poisson dual support point exists and is unique on the actual
Green-energy unit ball. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_greenEnergy_unitBall_inner_eq_poissonEnergyNorm
    (u : Ω₀)
    (hu : u ≠ 0) :
    ∃! f : Ω₀, GE₀ f ≤ 1 ∧ inner ℝ f u = PE₀ u := by
  let witness : Ω₀ :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
      u
  refine ⟨witness, ?_, ?_⟩
  · exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenEnergy_le_one_and_inner_eq_poissonEnergyNorm_iff_eq_poissonDualUnitWitnessL2
        witness u hu).2 rfl
  · intro f hf
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenEnergy_le_one_and_inner_eq_poissonEnergyNorm_iff_eq_poissonDualUnitWitnessL2
        f u hu).1 hf

/-- Structured receipt for the two uniquely exposed energy-dual unit-ball
support points on the actual beta-zero centered sector. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonUniqueDualMaximizersL2Receipt :
    Prop where
  green_support_bound :
    ∀ f u : Ω₀, PE₀ u ≤ 1 → inner ℝ f u ≤ GE₀ f
  green_positive_witness :
    ∀ (f : Ω₀) (hf : f ≠ 0),
      PE₀
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
            f) = 1 ∧
        inner ℝ f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
              f) =
          GE₀ f
  green_unique_support_point :
    ∀ (f u : Ω₀) (hf : f ≠ 0),
      (PE₀ u ≤ 1 ∧ inner ℝ f u = GE₀ f) ↔
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
            f
  green_exists_unique :
    ∀ (f : Ω₀) (hf : f ≠ 0),
      ∃! u : Ω₀, PE₀ u ≤ 1 ∧ inner ℝ f u = GE₀ f
  poisson_support_bound :
    ∀ f u : Ω₀, GE₀ f ≤ 1 → inner ℝ f u ≤ PE₀ u
  poisson_positive_witness :
    ∀ (u : Ω₀) (hu : u ≠ 0),
      GE₀
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
            u) = 1 ∧
        inner ℝ
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
              u)
            u =
          PE₀ u
  poisson_unique_support_point :
    ∀ (f u : Ω₀) (hu : u ≠ 0),
      (GE₀ f ≤ 1 ∧ inner ℝ f u = PE₀ u) ↔
        f =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
            u
  poisson_exists_unique :
    ∀ (u : Ω₀) (hu : u ≠ 0),
      ∃! f : Ω₀, GE₀ f ≤ 1 ∧ inner ℝ f u = PE₀ u
  claim_boundary :
    True

/-- The exact unique dual-maximizer receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonUniqueDualMaximizersL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonUniqueDualMaximizersL2Receipt := by
  refine
    { green_support_bound := ?_
      green_positive_witness := ?_
      green_unique_support_point := ?_
      green_exists_unique := ?_
      poisson_support_bound := ?_
      poisson_positive_witness := ?_
      poisson_unique_support_point := ?_
      poisson_exists_unique := ?_
      claim_boundary := trivial }
  · intro f u hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_le_greenEnergyNorm_of_poissonEnergy_le_one
        f u hu
  · intro f hf
    exact ⟨
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenDualUnitWitnessL2_poissonEnergy_eq_one
        f hf,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenDualUnitWitnessL2_eq_greenEnergyNorm
        f hf⟩
  · intro f u hf
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonEnergy_le_one_and_inner_eq_greenEnergyNorm_iff_eq_greenDualUnitWitnessL2
        f u hf
  · intro f hf
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_poissonEnergy_unitBall_inner_eq_greenEnergyNorm
        f hf
  · intro f u hf
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_le_poissonEnergyNorm_of_greenEnergy_le_one
        f u hf
  · intro u hu
    exact ⟨
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDualUnitWitnessL2_greenEnergy_eq_one
        u hu,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_poissonDualUnitWitnessL2_eq_poissonEnergyNorm
        u hu⟩
  · intro f u hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenEnergy_le_one_and_inner_eq_poissonEnergyNorm_iff_eq_poissonDualUnitWitnessL2
        f u hu
  · intro u hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_greenEnergy_unitBall_inner_eq_poissonEnergyNorm
        u hu

end
end MathlibAnalytic
end MGAP4D
