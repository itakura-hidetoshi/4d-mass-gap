import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalMixedResolventProducts

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

/-- A real shift below the common half-mass coercivity threshold. -/
def VacuumSemigroupGapSlope.BelowHalfMassShift
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope) :=
  {lambda : ℝ // lambda < G.mass / 2}

/-- Finite ordered products of rescaled-defect resolvents at different real
shifts converge strongly to the corresponding continuum resolvent products. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_orderedProduct_tendsto_continuumResolvent_orderedProduct
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ContinuousLinearMap.orderedProduct
          (fun sigma : G.BelowHalfMassShift =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau sigma.property)
          shifts y)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (ContinuousLinearMap.orderedProduct
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          shifts y)) := by
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
    fun sigma => (G.mass / 2 - (sigma : ℝ))⁻¹
  have hNorm : ∀ tau sigma, ‖A tau sigma‖ ≤ K sigma := by
    intro tau sigma
    exact
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
    ContinuousLinearMap.tendsto_orderedProduct_apply_of_pointwise_of_uniform_opNorm_le
      G.admissibleRescaledDefectTimeFilter A R K hNorm hPoint shifts y

/-- Norm-to-zero form of mixed resolvent-product convergence. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_orderedProduct_sub_continuumResolvent_orderedProduct_norm_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ‖ContinuousLinearMap.orderedProduct
              (fun sigma : G.BelowHalfMassShift =>
                G.admissibleRescaledDefectResolvent
                  hInnerSymmetric tau sigma.property)
              shifts y -
          ContinuousLinearMap.orderedProduct
              (fun sigma : G.BelowHalfMassShift =>
                G.vacuumOrthogonalContinuumRealResolvent
                  T hP hInnerSymmetric hSelf sigma.property)
              shifts y‖)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 0) := by
  have hProduct :=
    G.admissibleRescaledDefectResolvent_orderedProduct_tendsto_continuumResolvent_orderedProduct
      T hP hInnerSymmetric hSelf shifts y
  have hConst :
      Tendsto
        (fun _ : G.AdmissibleRescaledDefectTime =>
          ContinuousLinearMap.orderedProduct
            (fun sigma : G.BelowHalfMassShift =>
              G.vacuumOrthogonalContinuumRealResolvent
                T hP hInnerSymmetric hSelf sigma.property)
            shifts y)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ContinuousLinearMap.orderedProduct
            (fun sigma : G.BelowHalfMassShift =>
              G.vacuumOrthogonalContinuumRealResolvent
                T hP hInnerSymmetric hSelf sigma.property)
            shifts y)) :=
    tendsto_const_nhds
  have hSub := hProduct.sub hConst
  simpa using hSub.norm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
