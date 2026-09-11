import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalTraceFockDualProbe
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureBoundedContinuousProbe

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem boundaryMarginalTraceFockBoundedProbeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryMarginalTraceFockBoundedProbeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryMarginalTraceFockBoundedProbeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryMarginalTraceFockBoundedProbeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryMarginalTraceFockBoundedProbeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryMarginalTraceFockBoundedProbeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryMarginalTraceFockBoundedProbeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The actual degree-`n` normalized-trace feature on the reflection-fixed
boundary is continuous.  This is the reusable form of the continuity argument
already used internally in the Bochner-integrability proof: first prove
continuity of the degree feature on `SU(2)`, then pull it back along the actual
primary-plaquette boundary holonomy. -/
theorem
    continuous_periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature_feature
    (H n : ℕ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).feature := by
  let C₀ :=
    (specialUnitaryNormalizedTraceRelativeKernelFeature
      2 boundaryMarginalTraceFockBoundedProbeTwoRankPositive).pow n
  let hol := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2
  have hBaseKernel : Continuous fun q :
      Matrix.specialUnitaryGroup (Fin 2) ℂ ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      specialUnitaryNormalizedTraceRelativeKernel 2 q.1 q.2 ^ n :=
    continuous_specialUnitaryNormalizedTraceRelativeKernel_two.pow n
  have hBaseFeature : Continuous C₀.feature :=
    RealHilbertKernelFeature.continuous_feature_of_continuous_kernel C₀ hBaseKernel
  have hhol : Continuous hol :=
    continuous_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_two H
  simpa [C₀, hol,
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature] using
    hBaseFeature.comp hhol

/-- A Hilbert dual vector in the degree-`n` trace feature carrier determines a
canonical bounded continuous scalar observable on the actual reflection-fixed
boundary configuration space. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeBoundedContinuous
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) ℝ :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
    H n).dualProbeBoundedContinuous
      (continuous_periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature_feature
        H n)
      q

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeBoundedContinuous_apply
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeBoundedContinuous
        H n q b =
      inner ℝ q
        ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H n).feature b) := by
  rfl

/-- Every centered nonzero finite normalized-trace polynomial at positive
coupling is detected, in some strictly positive Taylor/Fock degree, by an
ordinary bounded continuous scalar boundary observable.

This is the scalar carrier normalization of the Hilbert-vector probe from the
preceding layer.  It still makes no identification with an open-half Haar
`L²` probe; the latter requires the separate boundary-moment realization
through the actual completed-positive Wilson kernel. -/
theorem
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_exists_positiveTaylorDegree_boundedContinuousDualFeatureProbe
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockBoundedProbeTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalTraceFockBoundedProbeTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      0 < beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ) ∧
      ∃ u : BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) ℝ,
        (∫ b,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
            u b
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockBoundedProbeTwoRankPositive beta hbeta.le)) ≠ 0 := by
  rcases
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_exists_positiveTaylorDegree_dualFeatureProbe
      H beta hbeta k c hc hzero with
    ⟨i, hi, hcoefficient, q, hq⟩
  let C :=
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
      H (i : ℕ)
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 boundaryMarginalTraceFockBoundedProbeTwoRankPositive beta hbeta.le
  have hC : Continuous C.feature := by
    simpa [C] using
      continuous_periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature_feature
        H (i : ℕ)
  let u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) ℝ :=
    C.dualProbeBoundedContinuous hC q
  have hq' :
      (∫ b, inner ℝ q (p b • C.feature b) ∂μ) ≠ 0 := by
    simpa [C, p, μ] using hq
  have hIntegral :
      (∫ b, inner ℝ q (p b • C.feature b) ∂μ) =
        ∫ b, p b * u b ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with b
    exact C.inner_smul_feature_eq_mul_dualProbeBoundedContinuous hC q (p b) b
  refine ⟨i, hi, hcoefficient, u, ?_⟩
  intro hzeroScalar
  exact hq' (hIntegral.trans hzeroScalar)

end

end MathlibAnalytic
end MGAP4D
