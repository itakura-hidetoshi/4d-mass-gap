import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonCompletedPositiveIntegralLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped Topology

noncomputable section

private theorem cyclicFourEdgeCompletedPositiveWeightedIntegralTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgeCompletedPositiveWeightedIntegralTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeCompletedPositiveWeightedIntegralCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeCompletedPositiveWeightedIntegralSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeCompletedPositiveWeightedIntegralMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeCompletedPositiveWeightedIntegralBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeCompletedPositiveWeightedIntegralSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Weighted open-half Haar integral of the finite four-edge Wilson Fock
approximation at fixed boundary configuration. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfWeightedIntegral
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (g : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) → ℝ) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
        H beta hbeta degree b x * g x
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)

/-- Weighted open-half Haar integral of the actual completed-positive Gram
feature at fixed boundary configuration. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfWeightedIntegral
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (g : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) → ℝ) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 cyclicFourEdgeCompletedPositiveWeightedIntegralTwoRankPositive beta hbeta b x * g x
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)

/-- Dominated-convergence bridge with an arbitrary integrable scalar weight.
This isolates all measure-theoretic work from the later cyclic-probe
specialization: the degree-independent Wilson bound controls the approximants,
while the exact algebraic residual factor remains untouched. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfWeightedIntegral_tendsto
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (g : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) → ℝ)
    (hg : Integrable g (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfWeightedIntegral
          H beta hbeta degree b g)
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfWeightedIntegral
          H beta hbeta b g)) := by
  let C := periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
    H beta hbeta
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfWeightedIntegral
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfWeightedIntegral
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x => C * ‖g x‖)
  · exact Filter.Eventually.of_forall fun degree =>
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_measurable
        hH beta hbeta degree b).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun degree =>
      Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_abs_le
            H beta hbeta degree b x)
          (abs_nonneg (g x))
  · simpa [C] using hg.norm.const_mul C
  · exact Filter.Eventually.of_forall fun x =>
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_tendsto
        hH beta hbeta b x).mul tendsto_const_nhds

end

end MathlibAnalytic
end MGAP4D
