import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveDensityTraceFockRobustness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullStrictness

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace ENNReal

noncomputable section

private theorem positiveDensityWilsonStrictnessTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveDensityWilsonStrictnessTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveDensityWilsonStrictnessCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveDensityWilsonStrictnessSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveDensityWilsonStrictnessMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveDensityWilsonStrictnessBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveDensityWilsonStrictnessSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance positiveDensityWilsonStrictnessHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance positiveDensityWilsonStrictnessBoundaryHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

/-- Arbitrary equivalent positive reweighting of boundary Haar measure preserves
an actual positive-degree Wilson/Fock witness and the strictness of the complete
literal positive-boundary temporal Wilson kernel.

Unlike the interacting-marginal theorem, no centering hypothesis is imposed on
the reweighted measure.  The shifted-polynomial Gram argument supplies a
possibly new but still strictly positive degree.  That same degree and a single
canonical dual probe are then transported through the genuine four-edge
Hilbert adjoint.  The selected Wilson degree is protected first inside the
four-edge source carrier and then inside the full literal boundary product by
the two nested Moore--Aronszajn direct sums.  Hence no non-diagonal Taylor/Fock
sector is discarded and no rectangular matrix-coefficient sign argument is
used. -/
theorem
    periodicHypercubicEvenNormalizedTracePolynomial_withDensity_exists_positiveDegree_fullPositiveBoundaryWilsonGram_strict
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
      ∃ q :
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H ((i : ℕ) + 1)).FeatureHilbert,
        (∫ b,
          inner ℝ q
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
              (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
                H ((i : ℕ) + 1)).feature b)
          ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w)) ≠ 0 ∧
        (∫ b,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
            periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue
              H ((i : ℕ) + 1) b
          ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w)) ≠ 0 ∧
        0 < ∫ b₁, ∫ b₂,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₁ *
            periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₂ *
            periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel
              H beta b₁ b₂
          ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w)
          ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w) := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let ν := μ.withDensity w
  let r := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  rcases
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial_withDensity_exists_positiveDegree_moment_ne_zero
      H k c hc w hwmeas hwne with
    ⟨i, hi, hInner⟩
  let n := (i : ℕ) + 1
  let T := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
    H n
  let hol := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2
  let b₀ := periodicHypercubicEvenPrimarySpatialPlaquetteTraceKernelBasepoint H
  let q : T.FeatureHilbert := T.feature b₀
  have hInner' :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ n))
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ p) ≠ 0 := by
    simpa [ν, μ, r, p, n] using hInner
  have hInnerEq :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ n))
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ p) =
      ∫ b, p b * r b ^ n ∂ν := by
    simpa using MeasureTheory.ContinuousMap.inner_toLp ν (r ^ n) p
  have hTraceMoment : (∫ b, p b * r b ^ n ∂ν) ≠ 0 := by
    rw [hInnerEq] at hInner'
    exact hInner'
  have hSection : ∀ b,
      specialUnitaryNormalizedTraceRelativeKernel 2 (hol b₀) (hol b) = r b := by
    intro b
    simpa [hol, b₀, r,
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel] using
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel_basepoint
        H b
  have hq :
      (∫ b, inner ℝ q (p b • T.feature b) ∂ν) ≠ 0 := by
    have hEq :
        (∫ b, inner ℝ q (p b • T.feature b) ∂ν) =
          ∫ b, p b * r b ^ n ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with b
      rw [real_inner_smul_right]
      change p b * inner ℝ (T.feature b₀) (T.feature b) = p b * r b ^ n
      rw [← T.kernel_eq_inner]
      change p b *
          (specialUnitaryNormalizedTraceRelativeKernel 2 (hol b₀) (hol b) ^ n) =
        p b * r b ^ n
      rw [hSection b]
    exact hEq.trans_ne hTraceMoment
  let C₀ :=
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).comap
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H)
  have hC₀Continuous : Continuous C₀.feature := by
    simpa [C₀,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue_continuous
        H n
  have hC₀Norm : ∀ b, ‖C₀.feature b‖ = 1 := by
    intro b
    simpa [C₀,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue_norm
        H n b
  have hSourceIntegrable : Integrable (fun b => p b • C₀.feature b) ν := by
    have hContinuous : Continuous (fun b => p b • C₀.feature b) :=
      p.continuous.smul hC₀Continuous
    refine Integrable.of_bound hContinuous.aestronglyMeasurable ‖p‖ ?_
    filter_upwards [] with b
    rw [norm_smul, hC₀Norm]
    simpa using p.norm_coe_le_norm b
  let q₄ := specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q
  have hSourceMoment : (∫ b, p b • C₀.feature b ∂ν) ≠ 0 := by
    intro hzero
    apply hq
    calc
      (∫ b, inner ℝ q (p b • T.feature b) ∂ν) =
          ∫ b, inner ℝ q₄ (p b • C₀.feature b) ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with b
        have hadj :=
          specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_boundaryFourEdgeDegreeFeatureValue
            H n q b
        rw [real_inner_smul_right, real_inner_smul_right]
        simpa [q₄, C₀,
          periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
          congrArg (fun z : ℝ => p b * z) hadj.symm
      _ = inner ℝ q₄ (∫ b, p b • C₀.feature b ∂ν) :=
        integral_inner hSourceIntegrable q₄
      _ = 0 := by rw [hzero, inner_zero_right]
  let S₀ := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
    H beta hbeta.le n
  let s := specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n
  have hTaylor : 0 < specialUnitaryWilsonSelectedTaylorCoefficient beta n := by
    unfold specialUnitaryWilsonSelectedTaylorCoefficient
    exact mul_pos (Real.exp_pos _)
      (div_pos (pow_pos hbeta _) (by positivity))
  have hs : 0 < s := by
    dsimp [s, specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient]
    exact pow_pos hTaylor _
  have hSelectedMoment : (∫ b, p b • S₀.feature b ∂ν) ≠ 0 := by
    have hScaled : Real.sqrt s • (∫ b, p b • C₀.feature b ∂ν) ≠ 0 :=
      smul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hs)) hSourceMoment
    have hEq :=
      RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul
        C₀ ν p s hs.le
    simpa [S₀, C₀, s,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature] using
      hEq.trans_ne hScaled
  let rho := (Real.exp (-beta)) ^
    (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card
  let S := periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedSelectedDegreeFeature
    H beta hbeta.le n
  have hrho : 0 < rho := by
    simpa [rho] using
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualDegreeZeroScalar_pos H beta
  have hProtectedMoment : (∫ b, p b • S.feature b ∂ν) ≠ 0 := by
    have hScaled : Real.sqrt rho • (∫ b, p b • S₀.feature b ∂ν) ≠ 0 :=
      smul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hrho)) hSelectedMoment
    have hEq :=
      RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul
        S₀ ν p rho hrho.le
    simpa [S, S₀, rho,
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedSelectedDegreeFeature] using
      hEq.trans_ne hScaled
  let R := periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedRemainderFeature
    H beta hbeta.le n
  let C := periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
    H beta hbeta.le n
  have hFullIntegrable : Integrable (fun b => p b • C.feature b) ν := by
    have hContinuous : Continuous (fun b => p b • C.feature b) :=
      p.continuous.smul
        (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_continuous
          H beta hbeta.le n)
    refine Integrable.of_bound hContinuous.aestronglyMeasurable ‖p‖ ?_
    filter_upwards [] with b
    rw [norm_smul,
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_norm]
    simpa using p.norm_coe_le_norm b
  have hFullMoment : (∫ b, p b • C.feature b ∂ν) ≠ 0 := by
    have hAdd := RealHilbertKernelFeature.add_weighted_integral_ne_zero_of_right
      R S ν p
      (by
        simpa [C, R, S,
          periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature] using
          hFullIntegrable)
      hProtectedMoment
    simpa [C, R, S,
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature] using hAdd
  have hFullGram :
      0 < ∫ b₁, ∫ b₂,
        inner ℝ (p b₁ • C.feature b₁) (p b₂ • C.feature b₂) ∂ν ∂ν :=
    C.weighted_inner_doubleIntegral_pos_of_integral_ne_zero
      ν p hFullIntegrable hFullMoment
  refine ⟨i, hi, q, ?_, ?_, ?_⟩
  · simpa [q, T, p, ν, μ, n] using hq
  · simpa [C₀, p, ν, μ, n,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
      hSourceMoment
  · have hKernelGram :
        0 < ∫ b₁, ∫ b₂,
          p b₁ * p b₂ *
            periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel
              H beta b₁ b₂ ∂ν ∂ν := by
      simpa only [
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_weighted_inner_eq_fullKernel] using
        hFullGram
    simpa [p, ν, μ, n] using hKernelGram

end

end MathlibAnalytic
end MGAP4D
