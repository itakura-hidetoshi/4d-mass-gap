import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualBCF

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace FiniteSchurOneSidedProfile

/-- A nonnegative finite profile satisfying the natural one-sided Dobrushin
inequality `u ≤ q + C u` obeys the squared coercive estimate. -/
theorem global_energy_coercive
    {ι : Type*}
    [Fintype ι]
    (matrix : ι → ι → ℝ)
    (alpha : ℝ)
    (hAlphaNonneg : 0 ≤ alpha)
    (hAlphaLtOne : alpha < 1)
    (hMatrixNonneg : ∀ i j, 0 ≤ matrix i j)
    (hSchur : ∀ vector : ι → ℝ,
      (∑ i, (∑ j, matrix i j * vector j) ^ 2) ≤
        alpha ^ 2 * ∑ i, vector i ^ 2)
    (profile localProfile : ι → ℝ)
    (hProfileNonneg : ∀ i, 0 ≤ profile i)
    (hLocalNonneg : ∀ i, 0 ≤ localProfile i)
    (hOneSided : ∀ i,
      profile i ≤ localProfile i + ∑ j, matrix i j * profile j) :
    (1 - alpha) ^ 2 * ∑ i, profile i ^ 2 ≤
      ∑ i, localProfile i ^ 2 := by
  classical
  let action : ι → ℝ := fun i => ∑ j, matrix i j * profile j
  let profileEnergy : ℝ := ∑ i, profile i ^ 2
  let localEnergy : ℝ := ∑ i, localProfile i ^ 2
  let actionEnergy : ℝ := ∑ i, action i ^ 2
  let cross : ℝ := ∑ i, localProfile i * action i
  have hActionNonneg : ∀ i, 0 ≤ action i := by
    intro i
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hMatrixNonneg i j) (hProfileNonneg j)
  have hActionEnergyNonneg : 0 ≤ actionEnergy := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (action i)
  have hActionEnergy : actionEnergy ≤ alpha ^ 2 * profileEnergy := by
    simpa [actionEnergy, action, profileEnergy] using hSchur profile
  have hOneSided' : ∀ i, profile i ≤ localProfile i + action i := by
    intro i
    simpa [action] using hOneSided i
  have hProfileLeExpanded :
      profileEnergy ≤ localEnergy + actionEnergy + 2 * cross := by
    calc
      profileEnergy ≤ ∑ i, (localProfile i + action i) ^ 2 := by
        dsimp [profileEnergy]
        apply Finset.sum_le_sum
        intro i _
        have hp := hProfileNonneg i
        have hqa := add_nonneg (hLocalNonneg i) (hActionNonneg i)
        have hle := hOneSided' i
        nlinarith
      _ = localEnergy + actionEnergy + 2 * cross := by
        dsimp [localEnergy, actionEnergy, cross]
        calc
          (∑ i, (localProfile i + action i) ^ 2) =
              ∑ i, (localProfile i ^ 2 + action i ^ 2 +
                2 * (localProfile i * action i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (∑ i, localProfile i ^ 2) +
              (∑ i, action i ^ 2) +
              2 * ∑ i, localProfile i * action i := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum]
  by_cases hAlphaZero : alpha = 0
  · subst alpha
    have hActionEnergyLe : actionEnergy ≤ 0 := by
      simpa using hActionEnergy
    have hActionEnergyZero : actionEnergy = 0 :=
      le_antisymm hActionEnergyLe hActionEnergyNonneg
    have hActionZero (i : ι) : action i = 0 := by
      have hTerm : action i ^ 2 ≤ actionEnergy := by
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg (action j)) (Finset.mem_univ i)
      rw [hActionEnergyZero] at hTerm
      nlinarith [sq_nonneg (action i)]
    have hProfileLeLocal : profileEnergy ≤ localEnergy := by
      dsimp [profileEnergy, localEnergy]
      apply Finset.sum_le_sum
      intro i _
      have hle := hOneSided' i
      rw [hActionZero] at hle
      have hp := hProfileNonneg i
      have hq := hLocalNonneg i
      nlinarith
    simpa [profileEnergy, localEnergy] using hProfileLeLocal
  · have hAlphaPos : 0 < alpha :=
      lt_of_le_of_ne hAlphaNonneg (Ne.symm hAlphaZero)
    have hOneSubPos : 0 < 1 - alpha := sub_pos.mpr hAlphaLtOne
    let gamma : ℝ := (1 - alpha) / alpha
    have hGammaPos : 0 < gamma := by
      dsimp [gamma]
      exact div_pos hOneSubPos hAlphaPos
    have hYoung (i : ι) :
        2 * localProfile i * action i ≤
          gamma * action i ^ 2 + gamma⁻¹ * localProfile i ^ 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (FiniteSchurResolvent.two_mul_le_alpha_mul_sq_add_inv_mul_sq
          gamma (action i) (localProfile i) hGammaPos)
    have hCrossBound :
        2 * cross ≤ gamma * actionEnergy + gamma⁻¹ * localEnergy := by
      calc
        2 * cross = ∑ i, 2 * localProfile i * action i := by
          dsimp [cross]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ∑ i,
            (gamma * action i ^ 2 + gamma⁻¹ * localProfile i ^ 2) :=
          Finset.sum_le_sum fun i _ => hYoung i
        _ = gamma * actionEnergy + gamma⁻¹ * localEnergy := by
          dsimp [actionEnergy, localEnergy]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
    have hGammaAction : 1 + gamma = alpha⁻¹ := by
      dsimp [gamma]
      field_simp [ne_of_gt hAlphaPos]
      ring
    have hGammaLocal : 1 + gamma⁻¹ = (1 - alpha)⁻¹ := by
      dsimp [gamma]
      field_simp [ne_of_gt hAlphaPos, ne_of_gt hOneSubPos]
      ring
    have hProfileBound :
        profileEnergy ≤ alpha⁻¹ * actionEnergy +
          (1 - alpha)⁻¹ * localEnergy := by
      rw [← hGammaAction, ← hGammaLocal]
      linarith [hProfileLeExpanded, hCrossBound]
    have hScaledAction :
        alpha⁻¹ * actionEnergy ≤ alpha * profileEnergy := by
      calc
        alpha⁻¹ * actionEnergy ≤
            alpha⁻¹ * (alpha ^ 2 * profileEnergy) :=
          mul_le_mul_of_nonneg_left hActionEnergy
            (inv_nonneg.mpr hAlphaNonneg)
        _ = alpha * profileEnergy := by
          field_simp [ne_of_gt hAlphaPos]
    have hRearranged :
        (1 - alpha) * profileEnergy ≤
          (1 - alpha)⁻¹ * localEnergy := by
      linarith [hProfileBound, hScaledAction]
    calc
      (1 - alpha) ^ 2 * ∑ i, profile i ^ 2 =
          (1 - alpha) * ((1 - alpha) * profileEnergy) := by
        dsimp [profileEnergy]
        ring
      _ ≤ (1 - alpha) * ((1 - alpha)⁻¹ * localEnergy) :=
        mul_le_mul_of_nonneg_left hRearranged hOneSubPos.le
      _ = ∑ i, localProfile i ^ 2 := by
        dsimp [localEnergy]
        field_simp [ne_of_gt hOneSubPos]

end FiniteSchurOneSidedProfile

/-- The canonical hybrid square-root profile is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridProfileBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridProfileBCF target O := by
  exact Real.sqrt_nonneg _

/-- The natural one-link coupling input for the canonical hybrid profile. -/
structure PeriodicHypercubicSpecialUnitaryHybridPairOneSidedDataBCF
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) where
  hybridProfile_le_localPair_add_influence :
    ∀ target : PeriodicHypercubicEdge n,
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).independentPairHybridProfileBCF target O ≤
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).singleLinkConditionalPairProfileBCF target O +
        ∑ source : PeriodicHypercubicEdge n,
          periodicHypercubicSpecialUnitaryDobrushinInfluence
            n N hN beta beta_nonneg target source *
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).independentPairHybridProfileBCF source O

/-- The one-sided estimate yields coercivity between global and local pair energies. -/
theorem periodicHypercubicSpecialUnitary_hybridOneSided_pairEnergy_coercive
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ)
    (R : PeriodicHypercubicSpecialUnitaryHybridPairOneSidedDataBCF
      n N hN beta beta_nonneg O) :
    periodicHypercubicSpecialUnitaryPairResidualCoreGap beta *
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).gibbsIndependentPairDifferenceEnergyBCF O ≤
      ∑ target : PeriodicHypercubicEdge n,
        ∫ A,
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).singleLinkConditionalIndependentPairDifferenceEnergyBCF
              target O A
          ∂(periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).gibbsMeasure := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta beta_nonneg
  let alpha := periodicHypercubicSpecialUnitaryDobrushinCoefficient beta
  have hAlphaNonneg : 0 ≤ alpha := by
    dsimp [alpha, periodicHypercubicSpecialUnitaryDobrushinCoefficient]
    exact mul_nonneg (by norm_num)
      (compactHaarOscillationInfluence_nonneg (by positivity))
  have hAlphaLt : alpha < 1 := by
    simpa [alpha, periodicHypercubicSpecialUnitaryDobrushinCoefficient] using
      periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_beta_lt
        beta hBetaLt
  have hProfileCoercive :
      (1 - alpha) ^ 2 *
          ∑ target : PeriodicHypercubicEdge n,
            (C.independentPairHybridProfileBCF target O) ^ 2 ≤
        ∑ target : PeriodicHypercubicEdge n,
          (C.singleLinkConditionalPairProfileBCF target O) ^ 2 := by
    exact FiniteSchurOneSidedProfile.global_energy_coercive
      (periodicHypercubicSpecialUnitaryDobrushinInfluence
        n N hN beta beta_nonneg)
      alpha hAlphaNonneg hAlphaLt
      (periodicHypercubicSpecialUnitaryDobrushinInfluence_nonneg
        n N hN beta beta_nonneg)
      (periodicHypercubicSpecialUnitaryDobrushinInfluence_l2_sq_le
        n N hn hN beta beta_nonneg)
      (fun target => C.independentPairHybridProfileBCF target O)
      (fun target => C.singleLinkConditionalPairProfileBCF target O)
      (fun target =>
        continuous_compact_oriented_independentPairHybridProfileBCF_nonneg
          C target O)
      (fun target =>
        continuous_compact_oriented_singleLinkConditionalPairProfileBCF_nonneg
          C target O)
      R.hybridProfile_le_localPair_add_influence
  unfold periodicHypercubicSpecialUnitaryPairResidualCoreGap
  change (1 - alpha) ^ 2 * C.gibbsIndependentPairDifferenceEnergyBCF O ≤ _
  calc
    (1 - alpha) ^ 2 * C.gibbsIndependentPairDifferenceEnergyBCF O ≤
        (1 - alpha) ^ 2 *
          ∑ target : PeriodicHypercubicEdge n,
            (C.independentPairHybridProfileBCF target O) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_le_sum_hybridProfile_sq
          C O) (sq_nonneg _)
    _ ≤ ∑ target : PeriodicHypercubicEdge n,
        (C.singleLinkConditionalPairProfileBCF target O) ^ 2 := hProfileCoercive
    _ = ∑ target : PeriodicHypercubicEdge n,
        ∫ A,
          C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
          ∂C.gibbsMeasure :=
      continuous_compact_oriented_sum_singleLinkConditionalPairProfileBCF_sq C O

/-- The one-sided coupling estimate produces the bounded-continuous-core
heat-bath Poincaré inequality. -/
theorem periodicHypercubicSpecialUnitary_hybridOneSided_boundedContinuousCorePoincare
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ)
    (R : PeriodicHypercubicSpecialUnitaryHybridPairOneSidedDataBCF
      n N hN beta beta_nonneg O) :
    periodicHypercubicSpecialUnitaryPairResidualCoreGap beta *
        ‖(periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).vacuumCenteredL2
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg).gibbsL2RepresentativeBCF O)‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).heatBathHamiltonianL2
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg).gibbsL2RepresentativeBCF O))
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).gibbsL2RepresentativeBCF O) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta beta_nonneg
  have hPair :=
    periodicHypercubicSpecialUnitary_hybridOneSided_pairEnergy_coercive
      n N hn hN beta beta_nonneg hBetaLt O R
  change periodicHypercubicSpecialUnitaryPairResidualCoreGap beta *
      C.gibbsIndependentPairDifferenceEnergyBCF O ≤
    ∑ target : PeriodicHypercubicEdge n,
      ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure at hPair
  rw [continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_eq_two_mul_centered_norm_sq
        C O,
      continuous_compact_oriented_sum_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_hamiltonian
        C O] at hPair
  change periodicHypercubicSpecialUnitaryPairResidualCoreGap beta *
      ‖C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)‖ ^ 2 ≤
    inner ℝ (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
      (C.gibbsL2RepresentativeBCF O)
  nlinarith

/-- One-sided coupling data for every bounded continuous observable. -/
structure PeriodicHypercubicSpecialUnitaryHybridPairOneSidedFamilyDataBCF
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) where
  oneSidedData :
    ∀ O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ,
      PeriodicHypercubicSpecialUnitaryHybridPairOneSidedDataBCF
        n N hN beta beta_nonneg O

/-- Family one-sided estimates generate the explicit positive core Poincaré property. -/
theorem periodicHypercubicSpecialUnitary_hybridOneSided_family_boundedContinuousCorePoincare
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (R : PeriodicHypercubicSpecialUnitaryHybridPairOneSidedFamilyDataBCF
      n N hN beta beta_nonneg) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).BoundedContinuousCoreHeatBathPoincare
        (periodicHypercubicSpecialUnitaryPairResidualCoreGap beta) := by
  intro O
  exact
    periodicHypercubicSpecialUnitary_hybridOneSided_boundedContinuousCorePoincare
      n N hn hN beta beta_nonneg hBetaLt O (R.oneSidedData O)

end

end MathlibAnalytic
end MGAP4D
