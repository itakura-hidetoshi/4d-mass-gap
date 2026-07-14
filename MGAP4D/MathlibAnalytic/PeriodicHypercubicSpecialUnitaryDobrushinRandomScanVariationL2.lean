import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanVariation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryDobrushinSchurL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Squared finite link-variation energy. -/
def continuousCompactOrientedGaugeWilsonVariationEnergy
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (variation : C.base.geometry.Edge → ℝ) : ℝ :=
  ∑ source : C.base.geometry.Edge, variation source ^ 2

namespace FiniteRandomScanSchur

/-- Weighted two-component square estimate used to retain the exact
random-scan contraction rate. -/
theorem alpha_mul_mix_sq_le
    (a b alpha x y : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    alpha * (a * x + b * y) ^ 2 ≤
      (a + b * alpha) * (a * alpha * x ^ 2 + b * y ^ 2) := by
  have hNonneg :
      0 ≤ a * b * (alpha * x - y) ^ 2 :=
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  nlinarith

/-- If a finite linear action has squared `ℓ²` norm at most `alpha²`, then its
convex random-scan mixture with the identity has the exact squared rate
`(a + b * alpha)²`. -/
theorem mix_l2_sq_le
    {ι : Type*}
    [Fintype ι]
    (matrix : ι → ι → ℝ)
    (alpha a b : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hAlpha : 0 ≤ alpha)
    (hSchur : ∀ vector : ι → ℝ,
      (∑ i, (∑ j, matrix i j * vector j) ^ 2) ≤
        alpha ^ 2 * ∑ j, vector j ^ 2)
    (vector : ι → ℝ) :
    (∑ i, (a * vector i + b * ∑ j, matrix i j * vector j) ^ 2) ≤
      (a + b * alpha) ^ 2 * ∑ i, vector i ^ 2 := by
  classical
  let action : ι → ℝ := fun i => ∑ j, matrix i j * vector j
  let energy : ℝ := ∑ i, vector i ^ 2
  let actionEnergy : ℝ := ∑ i, action i ^ 2
  by_cases hAlphaZero : alpha = 0
  · have hActionEnergyLe : actionEnergy ≤ 0 := by
      simpa [actionEnergy, action, hAlphaZero] using hSchur vector
    have hActionEnergyNonneg : 0 ≤ actionEnergy := by
      exact Finset.sum_nonneg fun i _ => sq_nonneg (action i)
    have hActionEnergyZero : actionEnergy = 0 :=
      le_antisymm hActionEnergyLe hActionEnergyNonneg
    have hActionZero (i : ι) : action i = 0 := by
      have hTerm : action i ^ 2 ≤ actionEnergy := by
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg (action j)) (Finset.mem_univ i)
      rw [hActionEnergyZero] at hTerm
      nlinarith [sq_nonneg (action i)]
    calc
      (∑ i, (a * vector i + b * ∑ j, matrix i j * vector j) ^ 2) =
          ∑ i, (a * vector i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        change (a * vector i + b * action i) ^ 2 = (a * vector i) ^ 2
        rw [hActionZero]
        ring
      _ = a ^ 2 * energy := by
        dsimp [energy]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ (a + b * alpha) ^ 2 * ∑ i, vector i ^ 2 := by
        simp [energy, hAlphaZero]
  · have hAlphaPos : 0 < alpha :=
      lt_of_le_of_ne hAlpha (Ne.symm hAlphaZero)
    let rate : ℝ := a + b * alpha
    have hRate : 0 ≤ rate :=
      add_nonneg ha (mul_nonneg hb hAlpha)
    have hPointwise (i : ι) :
        alpha * (a * vector i + b * action i) ^ 2 ≤
          rate * (a * alpha * vector i ^ 2 + b * action i ^ 2) := by
      exact alpha_mul_mix_sq_le a b alpha (vector i) (action i) ha hb
    have hActionEnergy : actionEnergy ≤ alpha ^ 2 * energy := by
      simpa [actionEnergy, action, energy] using hSchur vector
    have hSummed :
        alpha *
            (∑ i, (a * vector i + b * action i) ^ 2) ≤
          rate * (a * alpha * energy + b * actionEnergy) := by
      calc
        alpha * (∑ i, (a * vector i + b * action i) ^ 2) =
            ∑ i, alpha * (a * vector i + b * action i) ^ 2 := by
          rw [Finset.mul_sum]
        _ ≤ ∑ i,
            rate * (a * alpha * vector i ^ 2 + b * action i ^ 2) := by
          exact Finset.sum_le_sum fun i _ => hPointwise i
        _ = rate * (a * alpha * energy + b * actionEnergy) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hInside :
        a * alpha * energy + b * actionEnergy ≤
          a * alpha * energy + b * (alpha ^ 2 * energy) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hActionEnergy hb)
    have hScaled :
        alpha *
            (∑ i, (a * vector i + b * action i) ^ 2) ≤
          alpha * ((a + b * alpha) ^ 2 * energy) := by
      calc
        alpha * (∑ i, (a * vector i + b * action i) ^ 2) ≤
            rate * (a * alpha * energy + b * actionEnergy) := hSummed
        _ ≤ rate *
            (a * alpha * energy + b * (alpha ^ 2 * energy)) :=
          mul_le_mul_of_nonneg_left hInside hRate
        _ = alpha * ((a + b * alpha) ^ 2 * energy) := by
          dsimp [rate]
          ring
    have hFinal :
        (∑ i, (a * vector i + b * action i) ^ 2) ≤
          (a + b * alpha) ^ 2 * energy := by
      by_contra hNot
      have hLt :
          (a + b * alpha) ^ 2 * energy <
            ∑ i, (a * vector i + b * action i) ^ 2 :=
        lt_of_not_ge hNot
      have hMulLt := mul_lt_mul_of_pos_left hLt hAlphaPos
      exact (not_lt_of_ge hScaled) hMulLt
    simpa [action, energy] using hFinal

end FiniteRandomScanSchur

/-- For a symmetric compact-Haar Dobrushin matrix, the averaged sharp update is
the affine mixture of the original profile and the matrix action. -/
theorem continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_eq_affine
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hSymm : ∀ target source,
      D.influence target source = D.influence source target)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (variation : C.base.geometry.Edge → ℝ)
    (source : C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
        D variation source =
      (1 - (Fintype.card C.base.geometry.Edge : ℝ)⁻¹) * variation source +
        (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
          ∑ target, D.influence source target * variation target := by
  classical
  let n : ℝ := Fintype.card C.base.geometry.Edge
  have hNPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hNNe : n ≠ 0 := ne_of_gt hNPos
  have hUpdate (target : C.base.geometry.Edge) :
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source =
        variation source + D.influence source target * variation target -
          (if target = source then variation source else 0) := by
    by_cases h : source = target
    · subst target
      simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation,
        D.influence_diagonal_zero]
    · have h' : target ≠ source := Ne.symm h
      simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation,
        h, h', hSymm target source]
  unfold continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
  change n⁻¹ *
      (∑ target,
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source) =
    (1 - n⁻¹) * variation source +
      n⁻¹ * ∑ target, D.influence source target * variation target
  rw [show
      (∑ target,
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source) =
        ∑ target,
          (variation source + D.influence source target * variation target -
            (if target = source then variation source else 0)) by
      apply Finset.sum_congr rfl
      intro target _
      exact hUpdate target]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [n, nsmul_eq_mul]
  field_simp [hNNe]
  ring

/-- Symmetry plus a finite Schur estimate gives the exact squared random-scan
variation-energy contraction rate. -/
theorem continuous_compact_oriented_symmetricSchur_randomScanVariationEnergy_le
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hSymm : ∀ target source,
      D.influence target source = D.influence source target)
    (hSchur : ∀ variation : C.base.geometry.Edge → ℝ,
      (∑ source,
        (∑ target, D.influence source target * variation target) ^ 2) ≤
          D.coefficient ^ 2 * ∑ source, variation source ^ 2)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (variation : C.base.geometry.Edge → ℝ) :
    continuousCompactOrientedGaugeWilsonVariationEnergy
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
          D variation) ≤
      continuousCompactOrientedDobrushinRandomScanRate C D.coefficient ^ 2 *
        continuousCompactOrientedGaugeWilsonVariationEnergy variation := by
  classical
  let n : ℝ := Fintype.card C.base.geometry.Edge
  let b : ℝ := n⁻¹
  let a : ℝ := 1 - b
  have hNPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hNNe : n ≠ 0 := ne_of_gt hNPos
  have hB : 0 ≤ b := by
    dsimp [b]
    exact inv_nonneg.mpr hNPos.le
  have hNOneNat : 1 ≤ Fintype.card C.base.geometry.Edge :=
    Nat.succ_le_iff.mpr hEdge
  have hNOne : 1 ≤ n := by
    exact_mod_cast hNOneNat
  have hA : 0 ≤ a := by
    have hInvMul : b * n = 1 := by
      dsimp [b]
      exact inv_mul_cancel₀ hNNe
    have hAux : 0 ≤ (n - 1) * b :=
      mul_nonneg (sub_nonneg.mpr hNOne) hB
    dsimp [a]
    nlinarith
  have hMix := FiniteRandomScanSchur.mix_l2_sq_le
    D.influence D.coefficient a b hA hB D.coefficient_nonneg hSchur variation
  calc
    continuousCompactOrientedGaugeWilsonVariationEnergy
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
          D variation) =
      ∑ source,
        (a * variation source +
          b * ∑ target, D.influence source target * variation target) ^ 2 := by
      unfold continuousCompactOrientedGaugeWilsonVariationEnergy
      apply Finset.sum_congr rfl
      intro source _
      rw [continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_eq_affine
        D hSymm hEdge variation source]
    _ ≤ (a + b * D.coefficient) ^ 2 *
        ∑ source, variation source ^ 2 := hMix
    _ = continuousCompactOrientedDobrushinRandomScanRate C D.coefficient ^ 2 *
        continuousCompactOrientedGaugeWilsonVariationEnergy variation := by
      unfold continuousCompactOrientedGaugeWilsonVariationEnergy
        continuousCompactOrientedDobrushinRandomScanRate
        continuousCompactOrientedDobrushinHeatBathGap
      dsimp [a, b, n]
      ring

/-- Exact periodic compact-Haar `SU(N)` random-scan `ℓ²` variation-energy
contraction in the explicit strict Dobrushin region. -/
theorem periodicHypercubicSpecialUnitary_randomScanVariationEnergy_le
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (variation : PeriodicHypercubicEdge n → ℝ) :
    continuousCompactOrientedGaugeWilsonVariationEnergy
        (C := periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg)
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
          (periodicHypercubicSpecialUnitaryDobrushinMatrixData
            n N hn hN beta beta_nonneg hBetaLt)
          variation) ≤
      continuousCompactOrientedDobrushinRandomScanRate
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg)
          (periodicHypercubicSpecialUnitaryDobrushinCoefficient beta) ^ 2 *
        continuousCompactOrientedGaugeWilsonVariationEnergy
          (C := periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg) variation := by
  let D := periodicHypercubicSpecialUnitaryDobrushinMatrixData
    n N hn hN beta beta_nonneg hBetaLt
  have hSymm : ∀ target source, D.influence target source =
      D.influence source target := by
    intro target source
    exact periodicHypercubicSpecialUnitary_influence_symm
      n N hN beta beta_nonneg target source
  have hSchur : ∀ vector : PeriodicHypercubicEdge n → ℝ,
      (∑ source,
        (∑ target, D.influence source target * vector target) ^ 2) ≤
          D.coefficient ^ 2 * ∑ source, vector source ^ 2 := by
    intro vector
    exact periodicHypercubicSpecialUnitaryDobrushinInfluence_l2_sq_le
      n N hn hN beta beta_nonneg vector
  have hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n) :=
    Fintype.card_pos_iff.mpr ⟨(fun _ => 0), 0⟩
  simpa [D, periodicHypercubicSpecialUnitaryDobrushinCoefficient] using
    (continuous_compact_oriented_symmetricSchur_randomScanVariationEnergy_le
      D hSymm hSchur hEdge variation)

/-- The proof-relevant variation profile of the actual periodic `SU(N)`
random-scan observable obeys the same squared contraction. -/
theorem periodicHypercubicSpecialUnitary_randomScanObservableVariationEnergy_le
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg) O) :
    continuousCompactOrientedGaugeWilsonVariationEnergy
        (C := periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg)
        (P.randomScanVariationBound
          (periodicHypercubicSpecialUnitaryDobrushinMatrixData
            n N hn hN beta beta_nonneg hBetaLt)).variation ≤
      continuousCompactOrientedDobrushinRandomScanRate
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg)
          (periodicHypercubicSpecialUnitaryDobrushinCoefficient beta) ^ 2 *
        continuousCompactOrientedGaugeWilsonVariationEnergy
          (C := periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg) P.variation := by
  simpa using
    (periodicHypercubicSpecialUnitary_randomScanVariationEnergy_le
      n N hn hN beta beta_nonneg hBetaLt P.variation)

end

end MathlibAnalytic
end MGAP4D
