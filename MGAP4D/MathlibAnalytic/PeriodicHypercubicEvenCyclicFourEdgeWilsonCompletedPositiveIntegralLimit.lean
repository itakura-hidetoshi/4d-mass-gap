import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonCompletedPositiveMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped Topology

noncomputable section

private theorem cyclicFourEdgeCompletedPositiveIntegralTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgeCompletedPositiveIntegralTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeCompletedPositiveIntegralCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeCompletedPositiveIntegralSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeCompletedPositiveIntegralMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeCompletedPositiveIntegralBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeCompletedPositiveIntegralSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Open-half Haar integral of the degree-truncated completed-positive
four-edge Wilson Fock approximation at a fixed boundary configuration. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfIntegral
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
      H beta hbeta degree b x
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)

/-- Open-half Haar integral of the actual completed-positive Gram feature at a
fixed boundary configuration. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfIntegral
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 cyclicFourEdgeCompletedPositiveIntegralTwoRankPositive beta hbeta b x
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)

/-- The full rectangular four-edge finite Wilson Taylor/Fock approximation can
be passed through the actual positive open-half Haar integral.  The proof uses
only pointwise convergence, the degree-independent bound already derived from
the exact Wilson factors, and the finite Haar measure; the algebraic residual
factor is retained exactly. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfIntegral_tendsto
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfIntegral
          H beta hbeta degree b)
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfIntegral
          H beta hbeta b)) := by
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  letI : IsFiniteMeasure halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfIntegral
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfIntegral
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun degree =>
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_measurable
        hH beta hbeta degree b).aestronglyMeasurable
  · refine ⟨
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
        H beta hbeta,
      Filter.Eventually.of_forall fun degree => ?_⟩
    exact Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_abs_le
          H beta hbeta degree b x)
  · exact Filter.Eventually.of_forall fun x =>
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_tendsto
        hH beta hbeta b x

end

end MathlibAnalytic
end MGAP4D
