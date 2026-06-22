import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedWilsonGibbsDensitySeparatedHalves
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedHalfAmplitudeReflection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- After orientation correction of the negative open half, the transported
Wilson Gibbs density is an outer product of the same positive-half amplitude. -/
theorem periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_gramKernel
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal =
      (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
          H N beta b *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b x *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b y) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_boundary_mul_separatedHalves_div_partition]
  rw [periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude_eq_positive_orientationCorrection]
  rw [periodicHypercubicEvenOpenHalfOrientationCorrection_involutive H y]

/-- Boundary-dependent scalar coefficient carried by the fixed-plane spatial
Wilson weight and the partition-function normalization. -/
noncomputable def periodicHypercubicEvenBoundaryGramCoefficient
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight H N beta b /
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction

/-- The boundary Gram coefficient is nonnegative. -/
theorem periodicHypercubicEvenBoundaryGramCoefficient_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ periodicHypercubicEvenBoundaryGramCoefficient H N hN beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryGramCoefficient
  apply div_nonneg
  · unfold periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
    unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
    exact Real.exp_nonneg _
  · exact le_of_lt
      (compact_oriented_partitionFunction_pos
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base
        (continuous_compact_oriented_boltzmannIntegrable
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)))

/-- Scalar Hilbert feature obtained by absorbing the square root of the boundary
coefficient into the completed positive-half Wilson amplitude. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  Real.sqrt (periodicHypercubicEvenBoundaryGramCoefficient
    H N hN beta hbeta b) *
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H N beta b x

/-- The orientation-corrected Gibbs density is exactly the real Hilbert inner
product of the two scalar boundary features. -/
theorem periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal =
      inner ℝ
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x)
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b y) := by
  rw [periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_gramKernel]
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  let c : ℝ := periodicHypercubicEvenBoundaryGramCoefficient
    H N hN beta hbeta b
  have hc : 0 ≤ c := by
    dsimp [c]
    exact periodicHypercubicEvenBoundaryGramCoefficient_nonneg
      H N hN beta hbeta b
  have hInner :
      inner ℝ
        (Real.sqrt c *
          periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
            H N beta b x)
        (Real.sqrt c *
          periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
            H N beta b y) =
      (Real.sqrt c *
          periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
            H N beta b x) *
        (Real.sqrt c *
          periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
            H N beta b y) := by
    simp
  rw [show periodicHypercubicEvenBoundaryGramCoefficient
      H N hN beta hbeta b = c by rfl]
  rw [hInner]
  calc
    (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
          H N beta b *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b x *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b y) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction =
      c *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b x *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b y := by
      dsimp [c, periodicHypercubicEvenBoundaryGramCoefficient]
      ring
    _ = (Real.sqrt c * Real.sqrt c) *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b x *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b y := by
      rw [Real.mul_self_sqrt hc]
    _ = (Real.sqrt c *
          periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
            H N beta b x) *
        (Real.sqrt c *
          periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
            H N beta b y) := by
      ring

end

end MathlibAnalytic
end MGAP4D
