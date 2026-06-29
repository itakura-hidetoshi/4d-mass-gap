import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRescaledDefectCoreGraphLimit

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

/-- Positive times at which the linear small-time defect estimate required by
the uniformly coercive rescaled-defect package already holds. -/
def VacuumSemigroupGapSlope.AdmissibleRescaledDefectTime
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope) :=
  {t : NNReal //
    0 < t ∧ (G.mass / 2) * (t : ℝ) ≤ 1 - G.decayFactor t}

/-- The small-positive-time filter pulled back to admissible rescaled-defect
times. -/
def VacuumSemigroupGapSlope.admissibleRescaledDefectTimeFilter
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope) :
    Filter G.AdmissibleRescaledDefectTime :=
  comap
    (fun tau : G.AdmissibleRescaledDefectTime => tau.1)
    (nhdsWithin 0 (Ioi 0))

/-- The coercive symmetric bounded-operator package at one admissible time. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectData
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime) :
    RealHilbertUniformCoerciveSymmetricStrongLimitData
      Unit P.VacuumOrthogonalHilbert (pure ()) :=
  G.vacuumOrthogonalRescaledDefectStrongLimitData
    T hSymmetric tau.1 tau.2.1 tau.2.2

/-- The bounded resolvent of the rescaled semigroup defect at one admissible
small time. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  (G.admissibleRescaledDefectData hSymmetric tau).limitResolvent hlambda

/-- The closed Hamiltonian shift applied to one canonical core vector. -/
def vacuumOrthogonalClosedRightHamiltonianCoreShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (lambda : ℝ)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    P.VacuumOrthogonalHilbert :=
  T.vacuumOrthogonalClosedRightHamiltonian
      (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hSymmetric)
      (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x) -
    lambda • (x : P.VacuumOrthogonalHilbert)

/-- The admissible bounded resolvent inverts its own shifted rescaled defect. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_apply_shift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : P.VacuumOrthogonalHilbert) :
    G.admissibleRescaledDefectResolvent hSymmetric tau hlambda
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hSymmetric tau.1 x - lambda • x) =
      x := by
  exact
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_apply_shift
      (G.admissibleRescaledDefectData hSymmetric tau)
      hlambda x

/-- Resolvent stability on a core shift: its error is the bounded resolvent
applied to the graph-approximation error of the rescaled defect. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_core_error_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    G.admissibleRescaledDefectResolvent hSymmetric tau hlambda
          (T.vacuumOrthogonalClosedRightHamiltonianCoreShift
            hSymmetric lambda x) -
        (x : P.VacuumOrthogonalHilbert) =
      G.admissibleRescaledDefectResolvent hSymmetric tau hlambda
        (T.vacuumOrthogonalClosedRightHamiltonian
            (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
              hSymmetric)
            (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x) -
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hSymmetric tau.1 (x : P.VacuumOrthogonalHilbert)) := by
  let R :=
    G.admissibleRescaledDefectResolvent hSymmetric tau hlambda
  have hInverse :
      R
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hSymmetric tau.1 (x : P.VacuumOrthogonalHilbert) -
            lambda • (x : P.VacuumOrthogonalHilbert)) =
        (x : P.VacuumOrthogonalHilbert) :=
    G.admissibleRescaledDefectResolvent_apply_shift
      T hSymmetric tau hlambda (x : P.VacuumOrthogonalHilbert)
  calc
    R (T.vacuumOrthogonalClosedRightHamiltonianCoreShift
          hSymmetric lambda x) -
        (x : P.VacuumOrthogonalHilbert) =
      R (T.vacuumOrthogonalClosedRightHamiltonianCoreShift
          hSymmetric lambda x) -
        R
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hSymmetric tau.1 (x : P.VacuumOrthogonalHilbert) -
            lambda • (x : P.VacuumOrthogonalHilbert)) := by
      rw [hInverse]
    _ = R
        (T.vacuumOrthogonalClosedRightHamiltonianCoreShift
            hSymmetric lambda x -
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hSymmetric tau.1 (x : P.VacuumOrthogonalHilbert) -
            lambda • (x : P.VacuumOrthogonalHilbert))) :=
      (R.map_sub _ _).symm
    _ = R
        (T.vacuumOrthogonalClosedRightHamiltonian
            (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
              hSymmetric)
            (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x) -
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hSymmetric tau.1 (x : P.VacuumOrthogonalHilbert)) := by
      congr 1
      unfold vacuumOrthogonalClosedRightHamiltonianCoreShift
      abel

/-- Quantitative core-range resolvent stability inherited from the uniform
`mass / 2` resolvent bound. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_core_error_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    ‖G.admissibleRescaledDefectResolvent hSymmetric tau hlambda
          (T.vacuumOrthogonalClosedRightHamiltonianCoreShift
            hSymmetric lambda x) -
        (x : P.VacuumOrthogonalHilbert)‖ ≤
      (G.mass / 2 - lambda)⁻¹ *
        ‖T.vacuumOrthogonalClosedRightHamiltonian
              (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
                hSymmetric)
              (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x) -
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hSymmetric tau.1 (x : P.VacuumOrthogonalHilbert)‖ := by
  rw [G.admissibleRescaledDefectResolvent_core_error_eq
    T hSymmetric tau hlambda x]
  exact
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_bound
      (G.admissibleRescaledDefectData hSymmetric tau)
      hlambda _

/-- Along admissible small times, bounded rescaled-defect resolvents converge
strongly on the shifted Hamiltonian core range. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_tendsto_on_coreShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        G.admissibleRescaledDefectResolvent hSymmetric tau hlambda
          (T.vacuumOrthogonalClosedRightHamiltonianCoreShift
            hSymmetric lambda x))
      G.admissibleRescaledDefectTimeFilter
      (nhds (x : P.VacuumOrthogonalHilbert)) := by
  have hTime :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime => tau.1)
        G.admissibleRescaledDefectTimeFilter
        (nhdsWithin 0 (Ioi 0)) := by
    exact tendsto_comap
  have hCore :=
    (T.vacuumOrthogonalRescaledDefect_tendsto_closedRightHamiltonian_on_core
      hSymmetric x).comp hTime
  have hConstant :
      Tendsto
        (fun _ : G.AdmissibleRescaledDefectTime =>
          T.vacuumOrthogonalClosedRightHamiltonian
            (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
              hSymmetric)
            (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x))
        G.admissibleRescaledDefectTimeFilter
        (nhds
          (T.vacuumOrthogonalClosedRightHamiltonian
            (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
              hSymmetric)
            (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x))) :=
    tendsto_const_nhds
  have hDifference :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          T.vacuumOrthogonalClosedRightHamiltonian
              (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
                hSymmetric)
              (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x) -
            T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hSymmetric tau.1 (x : P.VacuumOrthogonalHilbert))
        G.admissibleRescaledDefectTimeFilter
        (nhds 0) := by
    simpa using hConstant.sub hCore
  have hMajorant :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          (G.mass / 2 - lambda)⁻¹ *
            ‖T.vacuumOrthogonalClosedRightHamiltonian
                  (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
                    hSymmetric)
                  (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x) -
              T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hSymmetric tau.1 (x : P.VacuumOrthogonalHilbert)‖)
        G.admissibleRescaledDefectTimeFilter
        (nhds 0) := by
    have hNorm := hDifference.norm
    simpa using tendsto_const_nhds.mul hNorm
  have hError :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          G.admissibleRescaledDefectResolvent hSymmetric tau hlambda
              (T.vacuumOrthogonalClosedRightHamiltonianCoreShift
                hSymmetric lambda x) -
            (x : P.VacuumOrthogonalHilbert))
        G.admissibleRescaledDefectTimeFilter
        (nhds 0) :=
    squeeze_zero_norm'
      (Eventually.of_forall fun tau =>
        G.admissibleRescaledDefectResolvent_core_error_norm_le
          T hSymmetric tau hlambda x)
      hMajorant
  have hAdd := hError.add
    (tendsto_const_nhds :
      Tendsto
        (fun _ : G.AdmissibleRescaledDefectTime =>
          (x : P.VacuumOrthogonalHilbert))
        G.admissibleRescaledDefectTimeFilter
        (nhds (x : P.VacuumOrthogonalHilbert)))
  simpa only [sub_add_cancel, zero_add] using hAdd

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
