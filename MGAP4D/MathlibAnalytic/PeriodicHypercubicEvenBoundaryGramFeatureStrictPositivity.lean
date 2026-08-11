import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryDensityGramKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The boundary-only spatial crossing Wilson Boltzmann factor is strictly
positive, for every real coupling. -/
theorem periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_pos
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 < periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
      H N beta b := by
  unfold periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
  unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
  exact Real.exp_pos _

/-- The scalar coefficient absorbed into the actual boundary/open-half Gram
feature is strictly positive.  This strengthens the previously used
nonnegativity theorem without changing the feature definition. -/
theorem periodicHypercubicEvenBoundaryGramCoefficient_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 < periodicHypercubicEvenBoundaryGramCoefficient H N hN beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryGramCoefficient
  apply div_pos
  · exact periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_pos
      H N beta b
  · exact compact_oriented_partitionFunction_pos
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base
      (continuous_compact_oriented_boltzmannIntegrable
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))

/-- The completed positive-half Wilson amplitude is strictly positive before
passing to boundary-fibered coordinates. -/
theorem periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_pos
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 < periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
      H N beta A := by
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  apply mul_pos
  · unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
    exact Real.exp_pos _
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
    exact Real.exp_pos _

/-- Therefore the boundary-conditioned completed positive-half amplitude is
strictly positive at every boundary/open-half configuration. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_pos
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 < periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
      H N beta b x := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  exact periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_pos
    H N beta _

/-- The actual scalar boundary/open-half Gram feature is everywhere strictly
positive.  Both factors are strictly positive: the square root of the
boundary coefficient and the completed positive-half amplitude. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 < periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta b x := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  apply mul_pos
  · exact Real.sqrt_pos.2
      (periodicHypercubicEvenBoundaryGramCoefficient_pos
        H N hN beta hbeta b)
  · exact periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_pos
      H N beta b x

/-- In particular, the actual scalar Gram feature never vanishes pointwise. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta b x ≠ 0 :=
  ne_of_gt
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
      H N hN beta hbeta b x)

/-- The squared feature, which is the natural pointwise density appearing after
pairing a kernel section with itself, is also strictly positive. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_sq_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 <
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x) ^ 2 := by
  positivity

end

end MathlibAnalytic
end MGAP4D
