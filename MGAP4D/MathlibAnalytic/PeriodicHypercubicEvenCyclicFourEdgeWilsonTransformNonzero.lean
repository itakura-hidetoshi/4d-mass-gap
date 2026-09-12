import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonExactPSDStrictness
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureAddMomentStrictness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

local instance cyclicFourEdgeWilsonTransformNonzeroTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeWilsonTransformNonzeroCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeWilsonTransformNonzeroSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeWilsonTransformNonzeroMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeWilsonTransformNonzeroBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeWilsonTransformNonzeroSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- A nonzero selected common-degree four-edge Wilson moment forces a nonzero
**exact** four-edge Wilson transform at an actual boundary configuration.

The selected degree is first protected inside the exact decomposition
`remainder ⊕ selected`.  The resulting complete Hilbert moment is nonzero.
The generic kernel-value extraction theorem then produces a genuine boundary
point.  Finally the exact identity `K₄ = remainder + selected` identifies that
kernel value with the literal product of the four independent Wilson relative
kernels.  No sign is assigned to the remainder and no Taylor sector is
discarded. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundary_exists_exactFourEdgeWilsonTransform_ne_zero_of_selectedDegreeMoment
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (μ : Measure (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2))
    [IsFiniteMeasure μ]
    (p : C(PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2, ℝ))
    (hSelected :
      (∫ b,
        p b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
            H beta hbeta n).feature b
        ∂μ) ≠ 0) :
    ∃ c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2,
      (∫ b,
        p b *
          specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c)
        ∂μ) ≠ 0 := by
  let R :=
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedRemainderFeature
      H beta hbeta n
  let S :=
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
      H beta hbeta n
  let D :=
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
      H beta hbeta n
  have hIntegrable : Integrable (fun b => p b • D.feature b) μ := by
    have hContinuous : Continuous (fun b => p b • D.feature b) :=
      p.continuous.smul
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature_continuous
          H beta hbeta n)
    refine Integrable.of_bound hContinuous.aestronglyMeasurable ‖p‖ ?_
    filter_upwards [] with b
    rw [norm_smul,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature_norm]
    simpa using p.norm_coe_le_norm b
  have hFullMoment : (∫ b, p b • D.feature b ∂μ) ≠ 0 := by
    have hAdd :=
      RealHilbertKernelFeature.add_weighted_integral_ne_zero_of_right
        R S μ p
        (by
          simpa [D, R, S,
            periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature] using
            hIntegrable)
        (by simpa [S] using hSelected)
    simpa [D, R, S,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature] using
      hAdd
  rcases
    RealHilbertKernelFeature.exists_weighted_kernel_integral_ne_zero_of_integral_ne_zero
      D μ p hIntegrable hFullMoment with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hSum :
      (∫ b,
        p b *
          (specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta n
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c) +
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c))
        ∂μ) ≠ 0 := by
    simpa [D,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature,
      R, S] using hc
  have hEq :
      (∫ b,
        p b *
          specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c)
        ∂μ) =
      ∫ b,
        p b *
          (specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta n
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c) +
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c))
        ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with b
    rw [specialUnitaryTwoCyclicFourEdgeWilsonProductKernel_eq_remainder_add_selectedDegree]
  exact hEq.trans_ne hSum

end

end MathlibAnalytic
end MGAP4D
