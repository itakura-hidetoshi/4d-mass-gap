import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExactShiftedDefectGraphKuratowskiConvergence
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullStrongGraphResolvent
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

/-- Below the half-mass threshold, the exact shifted-defect graph at one index
is the singleton finite-time resolvent graph point. -/
theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_eq_singleton_resolventGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (i : ι) (hLambdaI : lambdaNet i < G.mass / 2) :
    G.exactShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet i =
      {(G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau i) hLambdaI (yNet i),
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau i) hLambdaI (yNet i)))} := by
  ext z
  constructor
  · rintro ⟨hGraph, hEquation⟩
    have hFirst :
        z.1 = G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau i) hLambdaI (yNet i) := by
      calc
        z.1 = G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau i) hLambdaI
            (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 z.1 - lambdaNet i • z.1) :=
          (G.admissibleRescaledDefectResolvent_apply_shift
            T hInnerSymmetric (tau i) hLambdaI z.1).symm
        _ = G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau i) hLambdaI (yNet i) := by
          rw [hEquation]
    rw [Set.mem_singleton_iff]
    apply Prod.ext
    · exact hFirst
    · rw [hGraph, hFirst]
  · rw [Set.mem_singleton_iff]
    rintro rfl
    refine ⟨rfl, ?_⟩
    have hEquation :=
      G.vacuumOrthogonalRescaledDefect_apply_admissibleResolvent_eq
        T hInnerSymmetric (tau i) hLambdaI (yNet i)
    rw [hEquation]
    abel

/-- The finite-time exact shifted-defect graph is nonempty whenever the shift
lies below the half-mass threshold. -/
theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_nonempty_of_lt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (i : ι) (hLambdaI : lambdaNet i < G.mass / 2) :
    (G.exactShiftedDefectGraphFamily
      T hInnerSymmetric tau lambdaNet yNet i).Nonempty := by
  rw [G.exactShiftedDefectGraphFamily_eq_singleton_resolventGraphPoint
    T hInnerSymmetric tau lambdaNet yNet i hLambdaI]
  exact Set.singleton_nonempty _

/-- A convergent shift net below the limiting half-mass threshold makes every
sufficiently late exact graph a singleton resolvent graph point. -/
theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_eventually_exists_eq_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (l : Filter ι)
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    {yNet : ι → P.VacuumOrthogonalHilbert}
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hlambda : lambda < G.mass / 2) :
    ∀ᶠ i in l, ∃ hLambdaI : lambdaNet i < G.mass / 2,
      G.exactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet i =
        {(G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau i) hLambdaI (yNet i),
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1
            (G.admissibleRescaledDefectResolvent
              hInnerSymmetric (tau i) hLambdaI (yNet i)))} := by
  have hGap : ∀ᶠ i in l, lambdaNet i < G.mass / 2 :=
    hLambda.eventually (Iio_mem_nhds hlambda)
  filter_upwards [hGap] with i hLambdaI
  exact ⟨hLambdaI,
    G.exactShiftedDefectGraphFamily_eq_singleton_resolventGraphPoint
      T hInnerSymmetric tau lambdaNet yNet i hLambdaI⟩

/-- Consequently, exact shifted-defect graph members are eventually unique. -/
theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_eventually_subsingleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (l : Filter ι)
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    {yNet : ι → P.VacuumOrthogonalHilbert}
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hlambda : lambda < G.mass / 2) :
    ∀ᶠ i in l,
      (G.exactShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet i).Subsingleton := by
  have hGap : ∀ᶠ i in l, lambdaNet i < G.mass / 2 :=
    hLambda.eventually (Iio_mem_nhds hlambda)
  filter_upwards [hGap] with i hLambdaI
  rw [G.exactShiftedDefectGraphFamily_eq_singleton_resolventGraphPoint
    T hInnerSymmetric tau lambdaNet yNet i hLambdaI]
  intro z hz w hw
  rw [Set.mem_singleton_iff] at hz hw
  exact hz.trans hw.symm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
