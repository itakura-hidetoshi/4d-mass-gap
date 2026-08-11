import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonCompletedPositiveFactor
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPartialBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private theorem cyclicFourEdgeCompletedPositiveBoundTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance cyclicFourEdgeCompletedPositiveBoundSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Every one-plaquette Wilson Boltzmann factor has the explicit lower bound
`exp (-2 beta)` at nonnegative coupling. -/
theorem specialUnitaryWilsonBoltzmannCentralFunction_exp_neg_two_mul_le
    {N : ℕ}
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-2 * beta) ≤
      specialUnitaryWilsonBoltzmannCentralFunction N beta U := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  apply Real.exp_le_exp.mpr
  have hE := specialUnitaryWilsonPlaquetteEnergy_le_two hN U
  calc
    -2 * beta = -(beta * 2) := by ring
    _ ≤ -(beta * specialUnitaryWilsonPlaquetteEnergy N U) :=
      neg_le_neg (mul_le_mul_of_nonneg_left hE hbeta)
    _ = -beta * specialUnitaryWilsonPlaquetteEnergy N U := by ring

/-- The product of the four selected temporal-companion Wilson factors is
uniformly bounded below by the fourth power of `exp (-2 beta)`. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct_lower
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (Real.exp (-2 * beta)) ^ 4 ≤
      periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
        H beta b x y := by
  let A :=
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y
  let c := Real.exp (-2 * beta)
  have hc : 0 ≤ c := Real.exp_nonneg _
  have hfactor (k : Fin 4) :
      c ≤ specialUnitaryWilsonBoltzmannCentralFunction 2 beta
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
    dsimp [c]
    exact specialUnitaryWilsonBoltzmannCentralFunction_exp_neg_two_mul_le
      cyclicFourEdgeCompletedPositiveBoundTwoRankPositive beta hbeta _
  have hnonneg (k : Fin 4) :
      0 ≤ specialUnitaryWilsonBoltzmannCentralFunction 2 beta
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
    unfold specialUnitaryWilsonBoltzmannCentralFunction
    exact Real.exp_nonneg _
  have h23 := mul_le_mul (hfactor 2) (hfactor 3) hc (hnonneg 2)
  have h01 := mul_le_mul (hfactor 0) (hfactor 1) hc (hnonneg 0)
  have hpairs := mul_le_mul h23 h01 (mul_nonneg hc hc)
    (mul_nonneg (hnonneg 2) (hnonneg 3))
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct,
    A, c, pow_succ] using hpairs

/-- The complete four-edge finite Wilson Fock kernel is uniformly bounded in
absolute value by one. -/
theorem specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel_abs_le_one
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    |specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree u v| ≤ 1 := by
  have hfactor (k : Fin 4) :
      |specialUnitaryWilsonRelativeKernelPartial 2 beta degree (u k) (v k)| ≤ 1 :=
    specialUnitaryWilsonRelativeKernelPartial_abs_le_one
      cyclicFourEdgeCompletedPositiveBoundTwoRankPositive beta hbeta degree (u k) (v k)
  have h23 := mul_le_mul (hfactor 2) (hfactor 3) (abs_nonneg _) zero_le_one
  have h01 := mul_le_mul (hfactor 0) (hfactor 1) (abs_nonneg _) zero_le_one
  have hpairs := mul_le_mul h23 h01
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
  simpa [specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel, abs_mul] using hpairs

/-- The residual completed-positive Gram factor is nonnegative. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    0 ≤ periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
      H beta hbeta b x := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
  apply mul_nonneg (Real.sqrt_nonneg _) ?_
  unfold periodicHypercubicEvenBoundaryResidualCompletedPositiveWilsonAmplitude
  unfold periodicHypercubicEvenResidualCompletedPositiveWilsonBoltzmannAmplitude
  apply mul_nonneg
  · unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
    exact Real.exp_nonneg _
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight
    exact Real.exp_nonneg _

/-- A degree-independent scalar bound for the residual-times-four-edge Taylor
approximants.  The denominator is strictly positive and comes from the exact
lower bound on the four selected Wilson factors. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : ℝ :=
  Real.sqrt
      (((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2
        cyclicFourEdgeCompletedPositiveBoundTwoRankPositive beta hbeta).base.partitionFunction)⁻¹) /
    (Real.exp (-2 * beta)) ^ 4

/-- The exact residual factor is uniformly bounded by the same constant used
for every finite four-edge Taylor truncation. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_le_partialBound
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor H beta hbeta b x ≤
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
        H beta hbeta := by
  let r := periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
    H beta hbeta b x
  let c := (Real.exp (-2 * beta)) ^ 4
  let B := Real.sqrt
    (((periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) 2
      cyclicFourEdgeCompletedPositiveBoundTwoRankPositive beta hbeta).base.partitionFunction)⁻¹)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_nonneg
      H beta hbeta b x
  have hc0 : 0 < c := by
    dsimp [c]
    positivity
  have hfour : c ≤
      periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
        H beta b x (fun _ => 1) := by
    dsimp [c]
    exact periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct_lower
      H beta hbeta b x (fun _ => 1)
  have hgram :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
      H 2 cyclicFourEdgeCompletedPositiveBoundTwoRankPositive beta hbeta b x
  have hmul : r * c ≤ B := by
    calc
      r * c ≤ r *
          periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
            H beta b x (fun _ => 1) :=
        mul_le_mul_of_nonneg_left hfour hr0
      _ = periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 cyclicFourEdgeCompletedPositiveBoundTwoRankPositive beta hbeta b x := by
        symm
        exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_residual_mul_fourCompanionProduct
          H beta hbeta b x
      _ ≤ B := by simpa [B] using hgram
  have hr : r ≤ B / c := (le_div_iff₀ hc0).2 hmul
  simpa [periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound,
    r, c, B] using hr

/-- Every finite four-edge Wilson Taylor approximation to the completed-positive
Gram feature obeys one degree-independent absolute bound. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_abs_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    |periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
        H beta hbeta degree b x| ≤
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
        H beta hbeta := by
  let r := periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
    H beta hbeta b x
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_nonneg
      H beta hbeta b x
  have hk := specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel_abs_le_one
    beta hbeta degree
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)
  calc
    |periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
        H beta hbeta degree b x| =
      r *
        |specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)| := by
        simp [periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial,
          r, abs_mul, abs_of_nonneg hr0]
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left hk hr0
    _ = r := by ring
    _ ≤ periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
        H beta hbeta :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_le_partialBound
        H beta hbeta b x

end

end MathlibAnalytic
end MGAP4D
