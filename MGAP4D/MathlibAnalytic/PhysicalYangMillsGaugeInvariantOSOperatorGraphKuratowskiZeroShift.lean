import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOperatorGraphKuratowskiConvergence
import Mathlib.Tactic

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

/-- Small-time convergence alone implies outer-limit containment in the
continuum Hamiltonian graph.  The proof internally chooses the constant shift
zero, which lies below the positive half-mass threshold. -/
theorem VacuumSemigroupGapSlope.rescaledDefectGraphFamily_kuratowskiOuterLimit_subset_continuumHamiltonianGraph_of_tendsto
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι)
    {tau : ι → G.AdmissibleRescaledDefectTime}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter) :
    FilterSet.kuratowskiOuterLimit l
        (G.rescaledDefectGraphFamily T hInnerSymmetric tau) ⊆
      G.continuumHamiltonianGraph T hSelf := by
  have hZero : (0 : ℝ) < G.mass / 2 := by
    nlinarith [G.mass_pos]
  have hLambda : Tendsto (fun _ : ι => (0 : ℝ)) l (nhds 0) :=
    tendsto_const_nhds
  exact
    G.rescaledDefectGraphFamily_kuratowskiOuterLimit_subset_continuumHamiltonianGraph
      T hP hInnerSymmetric hSelf l
        (lambdaNet := fun _ : ι => (0 : ℝ)) (lambda := 0)
        hZero hTau hLambda

/-- Every continuum Hamiltonian graph point has a recovery net along any
small-time filter, without exposing an auxiliary shift to the theorem user. -/
theorem VacuumSemigroupGapSlope.continuumHamiltonianGraph_subset_rescaledDefectGraphFamily_kuratowskiInnerLimit_of_tendsto
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι)
    {tau : ι → G.AdmissibleRescaledDefectTime}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter) :
    G.continuumHamiltonianGraph T hSelf ⊆
      FilterSet.kuratowskiInnerLimit l
        (G.rescaledDefectGraphFamily T hInnerSymmetric tau) := by
  have hZero : (0 : ℝ) < G.mass / 2 := by
    nlinarith [G.mass_pos]
  have hLambda : Tendsto (fun _ : ι => (0 : ℝ)) l (nhds 0) :=
    tendsto_const_nhds
  exact
    G.continuumHamiltonianGraph_subset_rescaledDefectGraphFamily_kuratowskiInnerLimit
      T hP hInnerSymmetric hSelf l
        (lambdaNet := fun _ : ι => (0 : ℝ)) (lambda := 0)
        hZero hTau hLambda

/-- The ordinary finite-time defect graphs converge to the closed continuum
Hamiltonian graph whenever the time net tends to the small-time filter.  The
statement has no source or shift parameter. -/
theorem VacuumSemigroupGapSlope.rescaledDefectGraphFamily_kuratowskiLimits_eq_continuumHamiltonianGraph_of_tendsto
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι) [NeBot l]
    {tau : ι → G.AdmissibleRescaledDefectTime}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter) :
    FilterSet.kuratowskiInnerLimit l
        (G.rescaledDefectGraphFamily T hInnerSymmetric tau) =
      G.continuumHamiltonianGraph T hSelf ∧
    FilterSet.kuratowskiOuterLimit l
        (G.rescaledDefectGraphFamily T hInnerSymmetric tau) =
      G.continuumHamiltonianGraph T hSelf := by
  have hZero : (0 : ℝ) < G.mass / 2 := by
    nlinarith [G.mass_pos]
  have hLambda : Tendsto (fun _ : ι => (0 : ℝ)) l (nhds 0) :=
    tendsto_const_nhds
  exact
    G.rescaledDefectGraphFamily_kuratowskiLimits_eq_continuumHamiltonianGraph
      T hP hInnerSymmetric hSelf l
        (lambdaNet := fun _ : ι => (0 : ℝ)) (lambda := 0)
        hZero hTau hLambda

/-- Direct formulation on the canonical admissible small-time filter. -/
theorem VacuumSemigroupGapSlope.rescaledDefectGraph_kuratowskiLimits_eq_continuumHamiltonianGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [NeBot G.admissibleRescaledDefectTimeFilter] :
    FilterSet.kuratowskiInnerLimit G.admissibleRescaledDefectTimeFilter
        (G.rescaledDefectGraphFamily T hInnerSymmetric
          (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
      G.continuumHamiltonianGraph T hSelf ∧
    FilterSet.kuratowskiOuterLimit G.admissibleRescaledDefectTimeFilter
        (G.rescaledDefectGraphFamily T hInnerSymmetric
          (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
      G.continuumHamiltonianGraph T hSelf := by
  exact
    G.rescaledDefectGraphFamily_kuratowskiLimits_eq_continuumHamiltonianGraph_of_tendsto
      T hP hInnerSymmetric hSelf G.admissibleRescaledDefectTimeFilter
        (tau := fun tau : G.AdmissibleRescaledDefectTime => tau)
        tendsto_id

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
