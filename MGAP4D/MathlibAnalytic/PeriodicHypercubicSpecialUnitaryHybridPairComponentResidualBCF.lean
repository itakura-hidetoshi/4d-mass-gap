import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairResidualBCF

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace FiniteComponentResidual

/-- Componentwise absolute residual control implies the corresponding finite
sum-of-squares estimate. -/
theorem sum_sq_le_sum_sq_of_abs_le
    {ι : Type*}
    [Fintype ι]
    (residual localProfile : ι → ℝ)
    (hLocalNonneg : ∀ i, 0 ≤ localProfile i)
    (hResidual : ∀ i, |residual i| ≤ localProfile i) :
    (∑ i, residual i ^ 2) ≤ ∑ i, localProfile i ^ 2 := by
  apply Finset.sum_le_sum
  intro i hi
  exact (sq_le_sq).2 <| by
    simpa [abs_of_nonneg (hLocalNonneg i)] using hResidual i

end FiniteComponentResidual

/-- Square-root profile of the native conditional independent-link-pair energy
at one physical link. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairProfileBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  Real.sqrt
    (∫ A,
      C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
      ∂C.gibbsMeasure)

/-- The Gibbs-averaged native conditional pair energy is nonnegative. -/
theorem continuous_compact_oriented_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ ∫ A,
      C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
      ∂C.gibbsMeasure := by
  exact integral_nonneg fun A =>
    continuous_compact_oriented_singleLinkConditionalIndependentPairDifferenceEnergyBCF_nonneg
      C target O A

/-- The native conditional-pair square-root profile is nonnegative. -/
theorem continuous_compact_oriented_singleLinkConditionalPairProfileBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.singleLinkConditionalPairProfileBCF target O := by
  exact Real.sqrt_nonneg _

/-- Squaring the native conditional-pair profile recovers exactly the Gibbs
average of the one-link conditional independent-pair energy. -/
theorem continuous_compact_oriented_singleLinkConditionalPairProfileBCF_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (C.singleLinkConditionalPairProfileBCF target O) ^ 2 =
      ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairProfileBCF
  exact Real.sq_sqrt <|
    continuous_compact_oriented_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_nonneg
      C target O

/-- The squared `ℓ²` norm of the native conditional-pair profile is exactly the
summed local conditional independent-pair energy. -/
theorem continuous_compact_oriented_sum_singleLinkConditionalPairProfileBCF_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ target : C.base.geometry.Edge,
      (C.singleLinkConditionalPairProfileBCF target O) ^ 2) =
      ∑ target : C.base.geometry.Edge,
        ∫ A,
          C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
          ∂C.gibbsMeasure := by
  apply Finset.sum_congr rfl
  intro target htarget
  exact continuous_compact_oriented_singleLinkConditionalPairProfileBCF_sq
    C target O

/-- One-link componentwise residual control for the canonical periodic compact-Haar
`SU(N)` hybrid profile. This is the local coupling inequality whose finite
sum-of-squares consequence is consumed by the residual bridge. -/
structure PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualDataBCF
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) where
  componentResidual_abs_le_localPairProfile :
    ∀ target : PeriodicHypercubicEdge n,
      |(periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).independentPairHybridProfileBCF target O -
        ∑ source : PeriodicHypercubicEdge n,
          periodicHypercubicSpecialUnitaryDobrushinInfluence
            n N hN beta beta_nonneg target source *
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).independentPairHybridProfileBCF source O| ≤
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).singleLinkConditionalPairProfileBCF target O

/-- Componentwise one-link residual estimates automatically supply the sole
aggregate residual field left by PR #852. -/
noncomputable def
    PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualDataBCF.toHybridPairResidualData
    {n N : ℕ}
    [NeZero n]
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℝ}
    {beta_nonneg : 0 ≤ beta}
    {O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ}
    (R : PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualDataBCF
      n N hN beta beta_nonneg O) :
    PeriodicHypercubicSpecialUnitaryHybridPairResidualDataBCF
      n N hN beta beta_nonneg O := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta beta_nonneg
  refine { residual_sq_le_localPair := ?_ }
  calc
    (∑ target : PeriodicHypercubicEdge n,
      (C.independentPairHybridProfileBCF target O -
        ∑ source : PeriodicHypercubicEdge n,
          periodicHypercubicSpecialUnitaryDobrushinInfluence
            n N hN beta beta_nonneg target source *
          C.independentPairHybridProfileBCF source O) ^ 2) ≤
        ∑ target : PeriodicHypercubicEdge n,
          (C.singleLinkConditionalPairProfileBCF target O) ^ 2 := by
      exact FiniteComponentResidual.sum_sq_le_sum_sq_of_abs_le
        (fun target =>
          C.independentPairHybridProfileBCF target O -
            ∑ source : PeriodicHypercubicEdge n,
              periodicHypercubicSpecialUnitaryDobrushinInfluence
                n N hN beta beta_nonneg target source *
              C.independentPairHybridProfileBCF source O)
        (fun target => C.singleLinkConditionalPairProfileBCF target O)
        (fun target =>
          continuous_compact_oriented_singleLinkConditionalPairProfileBCF_nonneg
            C target O)
        R.componentResidual_abs_le_localPairProfile
    _ = ∑ target : PeriodicHypercubicEdge n,
        ∫ A,
          C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
          ∂C.gibbsMeasure := by
      exact continuous_compact_oriented_sum_singleLinkConditionalPairProfileBCF_sq
        C O

/-- A componentwise canonical-hybrid residual estimate yields the explicit
pair-energy coercivity theorem. -/
theorem periodicHypercubicSpecialUnitary_hybridComponentResidual_pairEnergy_coercive
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
    (R : PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualDataBCF
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
  periodicHypercubicSpecialUnitary_hybridResidual_pairEnergy_coercive
    n N hn hN beta beta_nonneg hBetaLt O R.toHybridPairResidualData

/-- A componentwise canonical-hybrid residual estimate yields the native
bounded-continuous-core heat-bath Poincaré inequality. -/
theorem periodicHypercubicSpecialUnitary_hybridComponentResidual_boundedContinuousCorePoincare
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
    (R : PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualDataBCF
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
  periodicHypercubicSpecialUnitary_hybridResidual_boundedContinuousCorePoincare
    n N hn hN beta beta_nonneg hBetaLt O R.toHybridPairResidualData

/-- Componentwise one-link residual data for every bounded continuous observable. -/
structure PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualFamilyDataBCF
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) where
  componentResidualData :
    ∀ O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ,
      PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualDataBCF
        n N hN beta beta_nonneg O

/-- Componentwise residual family data generate the aggregate canonical-hybrid
residual family consumed by the existing Poincaré bridge. -/
noncomputable def
    PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualFamilyDataBCF.toHybridPairResidualFamilyData
    {n N : ℕ}
    [NeZero n]
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℝ}
    {beta_nonneg : 0 ≤ beta}
    (R : PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualFamilyDataBCF
      n N hN beta beta_nonneg) :
    PeriodicHypercubicSpecialUnitaryHybridPairResidualFamilyDataBCF
      n N hN beta beta_nonneg :=
  { residualData := fun O =>
      (R.componentResidualData O).toHybridPairResidualData }

/-- Family componentwise canonical-hybrid residual estimates generate the
explicit positive bounded-continuous-core Poincaré property. -/
theorem periodicHypercubicSpecialUnitary_hybridComponentResidual_family_boundedContinuousCorePoincare
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (R : PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualFamilyDataBCF
      n N hN beta beta_nonneg) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).BoundedContinuousCoreHeatBathPoincare
        (periodicHypercubicSpecialUnitaryPairResidualCoreGap beta) :=
  periodicHypercubicSpecialUnitary_hybridResidual_family_boundedContinuousCorePoincare
    n N hn hN beta beta_nonneg hBetaLt R.toHybridPairResidualFamilyData

end

end MathlibAnalytic
end MGAP4D
