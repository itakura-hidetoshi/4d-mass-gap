import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairProfileEnergyBCF

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The sole remaining profile estimate after the canonical hybrid path has
supplied the global independent-pair majorant. -/
structure PeriodicHypercubicSpecialUnitaryHybridPairResidualDataBCF
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) where
  residual_sq_le_localPair :
    (∑ target : PeriodicHypercubicEdge n,
      ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).independentPairHybridProfileBCF target O -
        ∑ source : PeriodicHypercubicEdge n,
          periodicHypercubicSpecialUnitaryDobrushinInfluence
            n N hN beta beta_nonneg target source *
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).independentPairHybridProfileBCF source O) ^ 2) ≤
      ∑ target : PeriodicHypercubicEdge n,
        ∫ A,
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).singleLinkConditionalIndependentPairDifferenceEnergyBCF
              target O A
          ∂(periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).gibbsMeasure

/-- The canonical hybrid profile plus its residual estimate form the complete
pair-residual profile data consumed by the Schur/Poincaré bridge. -/
noncomputable def
    PeriodicHypercubicSpecialUnitaryHybridPairResidualDataBCF.toPairResidualProfileData
    {n N : ℕ}
    [NeZero n]
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℝ}
    {beta_nonneg : 0 ≤ beta}
    {O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ}
    (R : PeriodicHypercubicSpecialUnitaryHybridPairResidualDataBCF
      n N hN beta beta_nonneg O) :
    PeriodicHypercubicSpecialUnitaryPairResidualProfileDataBCF
      n N hN beta beta_nonneg O :=
  { profile := fun target =>
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).independentPairHybridProfileBCF target O
    globalPair_le_profile_sq :=
      continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_le_sum_hybridProfile_sq
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg) O
    residual_sq_le_localPair := R.residual_sq_le_localPair }

/-- A residual estimate for the canonical hybrid profile directly yields the
explicit pair-energy coercivity theorem. -/
theorem periodicHypercubicSpecialUnitary_hybridResidual_pairEnergy_coercive
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
    (R : PeriodicHypercubicSpecialUnitaryHybridPairResidualDataBCF
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
            n N hN beta beta_nonneg).gibbsMeasure :=
  periodicHypercubicSpecialUnitary_pairResidual_pairEnergy_coercive
    n N hn hN beta beta_nonneg hBetaLt O R.toPairResidualProfileData

/-- A residual estimate for the canonical hybrid profile yields the native
bounded-continuous-core heat-bath Poincaré inequality for that observable. -/
theorem periodicHypercubicSpecialUnitary_hybridResidual_boundedContinuousCorePoincare
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
    (R : PeriodicHypercubicSpecialUnitaryHybridPairResidualDataBCF
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
          n N hN beta beta_nonneg).gibbsL2RepresentativeBCF O) :=
  periodicHypercubicSpecialUnitary_pairResidual_boundedContinuousCorePoincare
    n N hn hN beta beta_nonneg hBetaLt O R.toPairResidualProfileData

/-- One canonical-hybrid residual estimate for every bounded continuous
observable. -/
structure PeriodicHypercubicSpecialUnitaryHybridPairResidualFamilyDataBCF
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) where
  residualData :
    ∀ O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ,
      PeriodicHypercubicSpecialUnitaryHybridPairResidualDataBCF
        n N hN beta beta_nonneg O

/-- Family canonical-hybrid residual data produce the complete profile family. -/
noncomputable def
    PeriodicHypercubicSpecialUnitaryHybridPairResidualFamilyDataBCF.toPairResidualProfileFamilyData
    {n N : ℕ}
    [NeZero n]
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℝ}
    {beta_nonneg : 0 ≤ beta}
    (R : PeriodicHypercubicSpecialUnitaryHybridPairResidualFamilyDataBCF
      n N hN beta beta_nonneg) :
    PeriodicHypercubicSpecialUnitaryPairResidualProfileFamilyDataBCF
      n N hN beta beta_nonneg :=
  { profileData := fun O => (R.residualData O).toPairResidualProfileData }

/-- Family canonical-hybrid residual estimates generate the explicit positive
bounded-continuous-core Poincaré property. -/
theorem periodicHypercubicSpecialUnitary_hybridResidual_family_boundedContinuousCorePoincare
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (R : PeriodicHypercubicSpecialUnitaryHybridPairResidualFamilyDataBCF
      n N hN beta beta_nonneg) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).BoundedContinuousCoreHeatBathPoincare
        (periodicHypercubicSpecialUnitaryPairResidualCoreGap beta) :=
  periodicHypercubicSpecialUnitary_pairResidual_family_boundedContinuousCorePoincare
    n N hn hN beta beta_nonneg hBetaLt R.toPairResidualProfileFamilyData

end

end MathlibAnalytic
end MGAP4D
