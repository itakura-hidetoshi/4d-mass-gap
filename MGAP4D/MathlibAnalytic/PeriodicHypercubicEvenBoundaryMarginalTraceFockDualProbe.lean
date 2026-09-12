import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalTraceFockFeatureMoment
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureKernelMomentNonzero

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem boundaryMarginalTraceFockDualProbeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryMarginalTraceFockDualProbeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryMarginalTraceFockDualProbeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryMarginalTraceFockDualProbeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryMarginalTraceFockDualProbeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryMarginalTraceFockDualProbeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryMarginalTraceFockDualProbeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Every centered nonzero finite normalized-trace polynomial at positive
coupling is detected by a scalar dual probe in some strictly positive tensor
/Fock degree.

The probe lives in the exact Hilbert carrier of the degree feature.  It is not
identified here with an open-half `L²` observable: that carrier bridge is the
next analytic step.  This theorem therefore records precisely the finite-degree
separation furnished by the actual interacting boundary marginal without
silently conflating boundary Fock coordinates with open-half probes. -/
theorem
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_exists_positiveTaylorDegree_dualFeatureProbe
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockDualProbeTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalTraceFockDualProbeTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      0 < beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ) ∧
      ∃ q :
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H (i : ℕ)).FeatureHilbert,
        (∫ b,
          inner ℝ q
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
              (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
                H (i : ℕ)).feature b)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockDualProbeTwoRankPositive beta hbeta.le)) ≠ 0 := by
  rcases
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_exists_positiveTaylorDegree_degreeFeatureMoment_ne_zero
      H beta hbeta k c hc hzero with
    ⟨i, hi, hcoefficient, hFeatureMoment, _⟩
  let C :=
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
      H (i : ℕ)
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 boundaryMarginalTraceFockDualProbeTwoRankPositive beta hbeta.le
  have hIntegrable : Integrable (fun b => p b • C.feature b) μ := by
    simpa [C, p, μ] using
      periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_degreeFeature_integrable
        H beta hbeta.le k c (i : ℕ)
  have hMoment : (∫ b, p b • C.feature b ∂μ) ≠ 0 := by
    simpa [C, p, μ] using hFeatureMoment
  rcases C.exists_dual_probe_of_integral_ne_zero μ (fun b => p b)
      hIntegrable hMoment with ⟨q, hq⟩
  refine ⟨i, hi, hcoefficient, q, ?_⟩
  simpa [C, p, μ] using hq

end

end MathlibAnalytic
end MGAP4D
