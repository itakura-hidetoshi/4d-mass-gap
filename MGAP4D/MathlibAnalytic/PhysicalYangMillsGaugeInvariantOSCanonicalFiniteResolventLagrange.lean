import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteResolventLagrange
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventAlgebra

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Finite Lagrange combinations of below-half-mass rescaled-defect resolvents
converge strongly to the corresponding continuum Lagrange combination. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_finiteLagrangeCombination_tendsto_continuumFiniteLagrangeCombination
    {β : Type*}
    [DecidableEq β]
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ContinuousLinearMap.finiteLagrangeCombination
          s
          (fun b => (shift b).1)
          (fun b =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau (shift b).property)
          y)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (ContinuousLinearMap.finiteLagrangeCombination
          s
          (fun b => (shift b).1)
          (fun b =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf (shift b).property)
          y)) := by
  apply ContinuousLinearMap.tendsto_finiteLagrangeCombination_apply
  intro b x
  exact
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf (shift b).property x

/-- For an injective finite shift family, every coefficient in the canonical
Yang--Mills Lagrange resolvent combination is nonzero. -/
theorem VacuumSemigroupGapSlope.finiteLagrangeWeight_ne_zero
    {β : Type*}
    [DecidableEq β]
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (hInjective : Set.InjOn (fun b => (shift b).1) (s : Set β))
    {b : β}
    (hb : b ∈ s) :
    ContinuousLinearMap.finiteLagrangeWeight
        s (fun c => (shift c).1) b ≠ 0 := by
  exact
    ContinuousLinearMap.finiteLagrangeWeight_ne_zero
      s (fun c => (shift c).1) hInjective hb

/-- Each canonical finite Yang--Mills Lagrange coefficient is the leading
coefficient of the corresponding mathlib Lagrange basis polynomial. -/
theorem VacuumSemigroupGapSlope.finiteLagrangeWeight_eq_lagrangeBasis_leadingCoeff
    {β : Type*}
    [DecidableEq β]
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (hInjective : Set.InjOn (fun b => (shift b).1) (s : Set β))
    {b : β}
    (hb : b ∈ s) :
    ContinuousLinearMap.finiteLagrangeWeight
        s (fun c => (shift c).1) b =
      (Lagrange.basis s (fun c => (shift c).1) b).leadingCoeff := by
  exact
    ContinuousLinearMap.finiteLagrangeWeight_eq_lagrangeBasis_leadingCoeff
      s (fun c => (shift c).1) hInjective hb

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
