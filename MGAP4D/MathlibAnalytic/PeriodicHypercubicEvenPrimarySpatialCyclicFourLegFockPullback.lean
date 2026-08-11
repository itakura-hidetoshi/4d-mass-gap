import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialFourLegInvariantContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalTraceFockDualProbe
import Mathlib.Tactic.FunProp

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct InnerProduct InnerProductSpace

noncomputable section

local instance cyclicFourLegMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Cyclic four-leg contraction in the same physical `Fin 4` slots as the
natural contraction from #1660.  The signed legs are multiplied in the exact
cyclic Haar order `2,3,0,1`, so for the primary plaquette this returns
`x₂⁻¹ x₃⁻¹ x₀ x₁` rather than merely a conjugate natural word. -/
noncomputable def cyclicFourLegRealFeatureMultilinearMap
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    MultilinearMap ℝ
      (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)
      (SpecialUnitaryMatrixRealFeatureSpace N) := by
  classical
  refine MultilinearMap.mk'
    (fun v =>
      realFeatureMatrixMulLinearMap N
        (realFeatureMatrixMulLinearMap N
          (orientedRealFeatureLinearMap N (orientation 2) (v 2))
          (orientedRealFeatureLinearMap N (orientation 3) (v 3)))
        (realFeatureMatrixMulLinearMap N
          (orientedRealFeatureLinearMap N (orientation 0) (v 0))
          (orientedRealFeatureLinearMap N (orientation 1) (v 1)))) ?_ ?_
  · intro v i x y
    fin_cases i <;> simp [mul_add, add_mul]
  · intro v i r x
    fin_cases i <;> simp [smul_mul_assoc, mul_smul_comm]

/-- Bounded cyclic four-leg contraction on the Euclidean real matrix-feature
space. -/
noncomputable def cyclicFourLegRealFeatureContraction
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)
      (SpecialUnitaryMatrixRealFeatureSpace N) where
  toMultilinearMap := cyclicFourLegRealFeatureMultilinearMap N orientation
  cont := by
    change Continuous
      (fun v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N =>
        realFeatureMatrixMulContinuousBilinearMap N
          (realFeatureMatrixMulContinuousBilinearMap N
            ((orientedRealFeatureLinearMap N (orientation 2)).toContinuousLinearMap (v 2))
            ((orientedRealFeatureLinearMap N (orientation 3)).toContinuousLinearMap (v 3)))
          (realFeatureMatrixMulContinuousBilinearMap N
            ((orientedRealFeatureLinearMap N (orientation 0)).toContinuousLinearMap (v 0))
            ((orientedRealFeatureLinearMap N (orientation 1)).toContinuousLinearMap (v 1))))
    fun_prop

@[simp] theorem cyclicFourLegRealFeatureContraction_apply
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    cyclicFourLegRealFeatureContraction N orientation v =
      realFeatureMatrixMulLinearMap N
        (realFeatureMatrixMulLinearMap N
          (orientedRealFeatureLinearMap N (orientation 2) (v 2))
          (orientedRealFeatureLinearMap N (orientation 3) (v 3)))
        (realFeatureMatrixMulLinearMap N
          (orientedRealFeatureLinearMap N (orientation 0) (v 0))
          (orientedRealFeatureLinearMap N (orientation 1) (v 1))) := by
  rfl

/-- Primary-spatial specialization of the cyclic four-leg contraction. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteCyclicFourLegRealFeatureContraction
    (H N : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)
      (SpecialUnitaryMatrixRealFeatureSpace N) :=
  cyclicFourLegRealFeatureContraction N
    (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)

/-- On four defining `SU(N)` edge features the cyclic contraction is exactly
the real matrix feature of the canonical cyclic Haar plaquette word. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCyclicFourLegRealFeatureContraction_apply
    (H N : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCyclicFourLegRealFeatureContraction H N
        (fun k => specialUnitaryMatrixRealFeature N (x k)) =
      specialUnitaryMatrixRealFeature N (haarFinFourCyclicPlaquetteWord x) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteCyclicFourLegRealFeatureContraction
  rw [cyclicFourLegRealFeatureContraction_apply]
  change _ = complexMatrixRealFeature N
    ((haarFinFourCyclicPlaquetteWord x : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)
  rw [haarFinFourCyclicPlaquetteWord_eq]
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteOrientation,
    realFeatureMatrixMulLinearMap_apply, mul_assoc]

/-- Projective-tensor linearization of the cyclic contraction on the same
four-edge carrier introduced in #1660. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction
    (H N : ℕ) :
    SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  PiTensorProduct.liftIsometry ℝ
    (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)
    (SpecialUnitaryMatrixRealFeatureSpace N)
    (periodicHypercubicEvenPrimarySpatialPlaquetteCyclicFourLegRealFeatureContraction H N)

@[simp] theorem periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction_pure
    (H N : ℕ)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction H N
        (specialUnitaryFourLegProjectiveRealFeatureTensor N v) =
      periodicHypercubicEvenPrimarySpatialPlaquetteCyclicFourLegRealFeatureContraction H N v := by
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction,
    specialUnitaryFourLegProjectiveRealFeatureTensor]

/-- Continuous extension of the cyclic contraction to the completed projective
four-edge carrier. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction
    (H N : ℕ) :
    SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction H N).extend
    (UniformSpace.Completion.toComplL :
      SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
        SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N)

/-- The completed cyclic contraction agrees with the algebraic projective
contraction on the dense carrier. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction_coe
    (H N : ℕ)
    (t : SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction H N
        (t : SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N) =
      periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction H N t := by
  exact ContinuousLinearMap.extend_eq
    (periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction H N)
    (e := (UniformSpace.Completion.toComplL :
      SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
        SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        (UniformSpace.Completion.denseRange_coe :
          DenseRange fun x : SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N =>
            (x : SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N)))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        UniformSpace.Completion.isUniformInducing_coe
          (SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N))
    t

/-- The four actual primary-spatial boundary edges contract to the exact cyclic
boundary holonomy feature used by the Fock construction in #1655/#1656. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction_boundary
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction H N
        ((specialUnitaryFourLegProjectiveRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))) :
            SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H N b) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction_coe]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction_pure]
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy] using
    periodicHypercubicEvenPrimarySpatialPlaquetteCyclicFourLegRealFeatureContraction_apply
      H N (fun k => b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))

/-- Replacing the four boundary edges by the canonical temporal-companion
boundary legs leaves the exact same cyclic Fock carrier feature. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction_temporalCompanionBoundaryLegs
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction H N
        ((specialUnitaryFourLegProjectiveRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :
            SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H N b) := by
  simp_rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_fiberedBoundaryLeg_eq]
  exact periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction_boundary
    H N b

/-- Cyclic positive-half holonomy built from the four open three-edge paths of
the canonical temporal companions. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
    (H N : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  haarFinFourCyclicPlaquetteWord
    (fun k =>
      periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))

/-- The completed cyclic contraction on the four positive-half temporal paths
is exactly the real matrix feature of their cyclic holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction_temporalCompanionOpenHalf
    (H N : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction H N
        ((specialUnitaryFourLegProjectiveRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :
            SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
          H N x) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteCyclicCompletedProjectiveRealFeatureContraction_coe]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteCyclicProjectiveRealFeatureContraction_pure]
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy] using
    periodicHypercubicEvenPrimarySpatialPlaquetteCyclicFourLegRealFeatureContraction_apply
      H N
      (fun k =>
        periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))

private theorem cyclicFourLegFockTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- Degree-`n` normalized relative-trace feature on the actual positive-half
cyclic holonomy generated by the four temporal companions.  Its Hilbert carrier
is definitionally the same degree-`n` carrier used by the boundary feature from
#1655; only the comap changes. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
    (H n : ℕ) :
    RealHilbertKernelFeature
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (fun x y =>
        specialUnitaryNormalizedTraceRelativeKernel 2
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
            H 2 x)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
            H 2 y) ^ n) :=
  ((specialUnitaryNormalizedTraceRelativeKernelFeature
      2 cyclicFourLegFockTwoRankPositive).pow n).comap
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy H 2)

/-- The boundary and positive-half degree features use literally the same
completed Hilbert carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfDegreeFeatureHilbertEquiv
    (H n : ℕ) :
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert ≃ₗᵢ[ℝ]
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
        H n).FeatureHilbert :=
  LinearIsometryEquiv.refl ℝ _

/-- Pull a boundary degree-feature dual vector into the exact same Hilbert
carrier viewed from the actual positive-half temporal-companion cyclic
holonomy. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
      H n).FeatureHilbert :=
  periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfDegreeFeatureHilbertEquiv H n q

/-- Scalar positive-half probe induced by the transported degree-feature dual
vector.  This is the carrier-correct scalar interface to be bundled into
open-half Haar `L²` in the next analytic step. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  inner ℝ
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
      H n q)
    ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
      H n).feature x)

@[simp] theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_apply
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe H n q x =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
          H n q)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
          H n).feature x) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
