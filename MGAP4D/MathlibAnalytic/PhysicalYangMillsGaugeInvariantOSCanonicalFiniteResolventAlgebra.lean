import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalMixedResolventProductLimit

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

/-- Every finite real linear combination of finite mixed resolvent words
converges strongly from the rescaled defects to the continuum Hamiltonian. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_finsetWordSum_tendsto_continuumResolvent_finsetWordSum
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        s.sum (fun b => c b •
          ContinuousLinearMap.orderedProduct
            (fun sigma : G.BelowHalfMassShift =>
              G.admissibleRescaledDefectResolvent
                hInnerSymmetric tau sigma.property)
            (word b) y))
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (s.sum (fun b => c b •
          ContinuousLinearMap.orderedProduct
            (fun sigma : G.BelowHalfMassShift =>
              G.vacuumOrthogonalContinuumRealResolvent
                T hP hInnerSymmetric hSelf sigma.property)
            (word b) y))) := by
  let A : G.AdmissibleRescaledDefectTime → G.BelowHalfMassShift →
      P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
    fun tau sigma =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property
  let R : G.BelowHalfMassShift →
      P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
    fun sigma =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property
  let K : G.BelowHalfMassShift → ℝ :=
    fun sigma => (G.mass / 2 - sigma.1)⁻¹
  have hNorm : ∀ tau sigma, ‖A tau sigma‖ ≤ K sigma := by
    intro tau sigma
    simpa [A, K, VacuumSemigroupGapSlope.BelowHalfMassShift] using
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        (G.admissibleRescaledDefectData hInnerSymmetric tau)
        sigma.property
  have hPoint : ∀ sigma x,
      Tendsto (fun tau => A tau sigma x)
        G.admissibleRescaledDefectTimeFilter (𝓝 (R sigma x)) := by
    intro sigma x
    simpa [A, R] using
      G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
        T hP hInnerSymmetric hSelf sigma.property x
  simpa [A, R] using
    ContinuousLinearMap.tendsto_finset_sum_smul_orderedProduct_apply_of_pointwise_of_uniform_opNorm_le
      G.admissibleRescaledDefectTimeFilter A R K hNorm hPoint s word c y

/-- Norm-to-zero form of convergence for the finite mixed resolvent algebra. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_finsetWordSum_sub_continuumResolvent_finsetWordSum_norm_tendsto_zero
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ‖s.sum (fun b => c b •
              ContinuousLinearMap.orderedProduct
                (fun sigma : G.BelowHalfMassShift =>
                  G.admissibleRescaledDefectResolvent
                    hInnerSymmetric tau sigma.property)
                (word b) y) -
          s.sum (fun b => c b •
              ContinuousLinearMap.orderedProduct
                (fun sigma : G.BelowHalfMassShift =>
                  G.vacuumOrthogonalContinuumRealResolvent
                    T hP hInnerSymmetric hSelf sigma.property)
                (word b) y)‖)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 0) := by
  have hSum :=
    G.admissibleRescaledDefectResolvent_finsetWordSum_tendsto_continuumResolvent_finsetWordSum
      T hP hInnerSymmetric hSelf s word c y
  have hConst :
      Tendsto
        (fun _ : G.AdmissibleRescaledDefectTime =>
          s.sum (fun b => c b •
            ContinuousLinearMap.orderedProduct
              (fun sigma : G.BelowHalfMassShift =>
                G.vacuumOrthogonalContinuumRealResolvent
                  T hP hInnerSymmetric hSelf sigma.property)
              (word b) y))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (s.sum (fun b => c b •
            ContinuousLinearMap.orderedProduct
              (fun sigma : G.BelowHalfMassShift =>
                G.vacuumOrthogonalContinuumRealResolvent
                  T hP hInnerSymmetric hSelf sigma.property)
              (word b) y))) :=
    tendsto_const_nhds
  have hSub := hSum.sub hConst
  simpa using hSub.norm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
