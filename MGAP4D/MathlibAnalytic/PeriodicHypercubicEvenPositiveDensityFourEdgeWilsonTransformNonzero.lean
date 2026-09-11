import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonTransformNonzero
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonPositiveDensityStrictness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace Topology

noncomputable section

local instance positiveDensityFourEdgeWilsonTransformNonzeroTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveDensityFourEdgeWilsonTransformNonzeroCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveDensityFourEdgeWilsonTransformNonzeroSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveDensityFourEdgeWilsonTransformNonzeroMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveDensityFourEdgeWilsonTransformNonzeroBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveDensityFourEdgeWilsonTransformNonzeroSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- A nonzero genuine degree-`n` four-edge source moment forces a concrete
nonzero transform for the **exact** four-edge Wilson product whenever
`beta > 0`.

The source feature is first multiplied by the strictly positive selected
Taylor/Fock coefficient.  The resulting selected Wilson moment is nonzero and
is then protected through the exact PSD remainder by the concrete transform
extraction theorem. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundary_exists_exactFourEdgeWilsonTransform_ne_zero_of_sourceDegreeMoment
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (n : ℕ)
    (μ : Measure (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2))
    [IsFiniteMeasure μ]
    (p : C(PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2, ℝ))
    (hSource :
      (∫ b,
        p b •
          periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue H n b
        ∂μ) ≠ 0) :
    ∃ c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2,
      (∫ b,
        p b *
          specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c)
        ∂μ) ≠ 0 := by
  let C₀ :=
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).comap
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H)
  let S :=
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
      H beta hbeta.le n
  let s := specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n
  have hSource' : (∫ b, p b • C₀.feature b ∂μ) ≠ 0 := by
    simpa [C₀,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
      hSource
  have hTaylor : 0 < specialUnitaryWilsonSelectedTaylorCoefficient beta n := by
    unfold specialUnitaryWilsonSelectedTaylorCoefficient
    exact mul_pos (Real.exp_pos _)
      (div_pos (pow_pos hbeta _) (by positivity))
  have hs : 0 < s := by
    dsimp [s, specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient]
    exact pow_pos hTaylor _
  have hScaled : Real.sqrt s • (∫ b, p b • C₀.feature b ∂μ) ≠ 0 :=
    smul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hs)) hSource'
  have hEq :=
    RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul
      C₀ μ p s hs.le
  have hSelected : (∫ b, p b • S.feature b ∂μ) ≠ 0 := by
    simpa [S, C₀, s,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature] using
      hEq.trans_ne hScaled
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundary_exists_exactFourEdgeWilsonTransform_ne_zero_of_selectedDegreeMoment
      H beta hbeta.le n μ p hSelected

/-- Arbitrary equivalent positive reweighting of boundary Haar preserves a
concrete exact four-edge Wilson transform witness for every nonzero normalized-
trace polynomial.

This strengthens the existing positive-density strictness package from an
abstract/full Gram inequality to an actual boundary point `d` at which the
literal product of the four independent Wilson relative kernels has nonzero
weighted transform.  No centering hypothesis on the reweighted measure is
needed. -/
theorem
    periodicHypercubicEvenNormalizedTracePolynomial_withDensity_exists_positiveDegree_exactFourEdgeWilsonTransform_ne_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0)
    (w : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ≥0∞)
    (hwmeas : AEMeasurable w (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (hwne : ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2), w b ≠ 0)
    [IsFiniteMeasure
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w)] :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      ∃ d : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2,
        (∫ b,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
            specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)
          ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w)) ≠ 0 := by
  rcases
    periodicHypercubicEvenNormalizedTracePolynomial_withDensity_exists_positiveDegree_fullPositiveBoundaryWilsonGram_strict
      H beta hbeta k c hc w hwmeas hwne with
    ⟨i, hi, _q, _hq, hSource, _hFull⟩
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  have hSource' :
      (∫ b,
        p b •
          periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue
            H ((i : ℕ) + 1) b
        ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w)) ≠ 0 := by
    simpa [p] using hSource
  rcases
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundary_exists_exactFourEdgeWilsonTransform_ne_zero_of_sourceDegreeMoment
      H beta hbeta ((i : ℕ) + 1)
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w)
      p hSource' with
    ⟨d, hd⟩
  exact ⟨i, hi, d, by simpa [p] using hd⟩

end

end MathlibAnalytic
end MGAP4D
