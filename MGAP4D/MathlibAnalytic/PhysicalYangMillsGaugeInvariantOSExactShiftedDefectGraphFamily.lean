import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSAutomaticNonemptyKuratowskiDefectGraphConvergence
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

def VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (i : ι) :
    Set (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) :=
  {z |
    z.2 = T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
      hInnerSymmetric (tau i).1 z.1 ∧
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 z.1 - lambdaNet i • z.1 = yNet i}

@[simp]
theorem VacuumSemigroupGapSlope.mem_exactShiftedDefectGraphFamily_iff
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (i : ι) (z : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) :
    z ∈ G.exactShiftedDefectGraphFamily
      T hInnerSymmetric tau lambdaNet yNet i ↔
      z.2 = T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 z.1 ∧
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 z.1 - lambdaNet i • z.1 = yNet i :=
  Iff.rfl

theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_eq_zeroTolerance
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (i : ι) :
    G.exactShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet i =
      G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet (fun _ => 0) i := by
  ext z
  constructor
  · rintro ⟨hGraph, hEquation⟩
    refine ⟨hGraph, ?_⟩
    have hResidual :
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1 z.1 - lambdaNet i • z.1 - yNet i = 0 := by
      rw [hEquation]
      abel
    rw [hResidual, norm_zero]
  · rintro ⟨hGraph, hNorm⟩
    refine ⟨hGraph, ?_⟩
    have hNormEq :
        ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1 z.1 - lambdaNet i • z.1 - yNet i‖ = 0 :=
      le_antisymm hNorm (norm_nonneg _)
    have hResidual :
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1 z.1 - lambdaNet i • z.1 - yNet i = 0 :=
      norm_eq_zero.mp hNormEq
    exact sub_eq_zero.mp hResidual

theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_eventually_nonempty
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (l : Filter ι) {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime}
    (hLambda : Tendsto lambdaNet l (nhds lambda)) :
    ∀ᶠ i in l,
      (G.exactShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet i).Nonempty := by
  have hApprox :
      ∀ᶠ i in l,
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet (fun _ => 0) i).Nonempty :=
    G.approximateShiftedDefectGraphFamily_eventually_nonempty_of_eventually_nonneg
      T hInnerSymmetric l hlambda hLambda
        (Eventually.of_forall fun _ => le_rfl)
  filter_upwards [hApprox] with i hi
  rw [G.exactShiftedDefectGraphFamily_eq_zeroTolerance
    T hInnerSymmetric tau lambdaNet yNet i]
  exact hi

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
