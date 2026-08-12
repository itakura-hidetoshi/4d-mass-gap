import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonProtectedSelectedSector
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonExactPSDStrictness

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

noncomputable section

private theorem positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- All literal positive-boundary temporal shared-boundary legs, viewed as one
configuration indexed by the actual plaquette carrier. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryLegConfiguration
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    PeriodicHypercubicEvenPlaquette H → Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  fun p => periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p

/-- On a canonical temporal companion, the full boundary-leg configuration is
literally the corresponding physical edge in the existing four-edge boundary
word. -/
@[simp]
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryLegConfiguration_companion
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (k : Fin 4) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryLegConfiguration H b
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) =
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k := by
  simpa [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryLegConfiguration,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord] using
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_fiberedBoundaryLeg_eq b k

/-- The literal full positive-boundary temporal Wilson kernel on two actual
shared-boundary configurations. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel
    (H : ℕ)
    (beta : ℝ)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) : ℝ :=
  ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
    specialUnitaryWilsonRelativeKernel 2 beta
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryLegConfiguration H b p)
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryLegConfiguration H c p)

/-- On the actual boundary carrier, the full literal positive-boundary Wilson
kernel minus the protected strictly-positive scalar multiple of the genuine
four-edge selected-degree kernel remains symmetric positive semidefinite. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel_sub_protectedFourEdgeSelectedDegree_positiveSemidefiniteCertificate
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (selected : ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
      (fun b c => periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel H beta b c -
        (Real.exp (-beta)) ^
            (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c)) := by
  have C :=
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonFullProduct_sub_residualScalar_mul_fourEdgeSelectedDegreeKernel_positiveSemidefiniteCertificate
      H beta hbeta selected
  have Cpull := C.comap
    (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryLegConfiguration H)
  simpa [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel] using Cpull

/-- The scalar weighted-Gram value of the protected selected degree.  Naming
this quantity keeps the strictness theorem reusable while retaining every
literal residual degree-zero factor. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalProtectedPositiveBoundaryWilsonSelectedDegreeGramValue
    (H : ℕ)
    (beta : ℝ)
    (k n : ℕ)
    (c : Fin (k + 1) → ℝ) : ℝ :=
  ((Real.exp (-beta)) ^
      (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n) *
    (∫ b₁, ∫ b₂,
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b₁)
        (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b₂)
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta
        (le_of_lt (lt_of_lt_of_le (Real.exp_pos (-beta)) (by positivity))))
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta
        (le_of_lt (lt_of_lt_of_le (Real.exp_pos (-beta)) (by positivity)))))

/-- A cyclic dual probe that detects the genuine degree-`n` source produces a
strictly positive protected component inside the full positive-boundary Wilson
sector. -/
theorem periodicHypercubicEvenBoundaryMarginal_protectedPositiveBoundaryWilsonSelectedDegreeGram_pos_of_cyclicDualProbe
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) (k n : ℕ) (c : Fin (k + 1) → ℝ)
    (q : (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature H n).FeatureHilbert)
    (hq : (∫ b, inner ℝ q
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature H n).feature b)
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
        positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta hbeta.le)) ≠ 0) :
    0 < ((Real.exp (-beta)) ^
      (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n) *
      (∫ b₁, ∫ b₂, inner ℝ
        (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b₁)
        (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b₂)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
          positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta hbeta.le)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
          positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta hbeta.le)) := by
  have hGram :=
    periodicHypercubicEvenBoundaryMarginal_weightedFourEdgeDegreeFeature_gram_pos_of_cyclicDualProbe
      H beta hbeta.le k n c q hq
  have hTaylor : 0 < specialUnitaryWilsonSelectedTaylorCoefficient beta n := by
    unfold specialUnitaryWilsonSelectedTaylorCoefficient
    exact mul_pos (Real.exp_pos _)
      (div_pos (pow_pos hbeta _) (by positivity))
  have hSelectedCoefficient :
      0 < specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n := by
    unfold specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient
    exact pow_pos hTaylor _
  have hResidual :=
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualDegreeZeroScalar_pos H beta
  exact mul_pos (mul_pos hResidual hSelectedCoefficient) hGram

/-- Every centered nonzero normalized-trace boundary polynomial at positive
coupling has a positive degree whose strict four-edge Fock Gram component is
protected inside the complete literal positive-boundary temporal Wilson
sector. -/
theorem periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_protectedPositiveBoundaryWilsonSelectedGram_strict
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero : inner ℝ
      (ContinuousMap.toLp (E := ℝ) 2
        (periodicHypercubicEvenBoundaryMarginalMeasure H 2
          positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta hbeta.le) ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^ (0 : ℕ)))
      (∑ j : Fin (k + 1), c j • ContinuousMap.toLp (E := ℝ) 2
        (periodicHypercubicEvenBoundaryMarginalMeasure H 2
          positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta hbeta.le) ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^ (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1), 0 < (i : ℕ) ∧ ∃ q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature H (i : ℕ)).FeatureHilbert,
      (∫ b, inner ℝ q
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature H (i : ℕ)).feature b)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
          positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta hbeta.le)) ≠ 0 ∧
      0 < ((Real.exp (-beta)) ^
        (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta (i : ℕ)) *
        (∫ b₁, ∫ b₂, inner ℝ
          (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c (i : ℕ) b₁)
          (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c (i : ℕ) b₂)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
            positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta hbeta.le)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
            positiveBoundaryTemporalWilsonBoundaryProtectedStrictnessTwoRankPositive beta hbeta.le)) := by
  rcases
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_fourEdgeDiagonalGram_strict
      H beta hbeta k c hc hzero with
    ⟨i, hi, _hTaylor, q, hq, _hDiagonalStrict⟩
  refine ⟨i, hi, q, hq, ?_⟩
  exact
    periodicHypercubicEvenBoundaryMarginal_protectedPositiveBoundaryWilsonSelectedDegreeGram_pos_of_cyclicDualProbe
      H beta hbeta k (i : ℕ) c q hq

end

end MathlibAnalytic
end MGAP4D
