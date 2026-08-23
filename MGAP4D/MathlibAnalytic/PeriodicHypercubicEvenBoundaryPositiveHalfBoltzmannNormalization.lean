import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryDensityGramKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact positive-half closure action already latent in the OS boundary
Gram factorization.  The fixed-plane spatial sector carries half weight, while
the strict-positive bulk and positive temporal-boundary sectors carry full
weight. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  let A :=
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      b x (fun _ => 1)
  (1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
    periodicHypercubicEvenPositiveWilsonAction H N A +
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A

/-- The completed positive OS amplitude is exactly the Boltzmann factor of the
strict-positive bulk plus the positive temporal-boundary action. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_eq_boltzmann
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H N beta b x =
      Real.exp
        (-beta *
          (periodicHypercubicEvenPositiveWilsonAction H N
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                b x (fun _ => 1)) +
            periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                b x (fun _ => 1)))) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  rw [← Real.exp_add]
  congr 1
  ring

/-- The boundary-only fixed-plane weight can be evaluated on the same positive
closure representative used by the completed positive amplitude. -/
theorem periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_eq_closure_boltzmann
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight H N beta b =
      Real.exp
        (-beta * periodicHypercubicEvenSpatialCrossingWilsonAction H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1))) := by
  rw [← periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight_boundaryFiberedAssemble_eq_boundary
    H N beta b x (fun _ => 1)]
  rfl

/-- Partition normalization written in the same square-root form carried by the
OS Gram feature. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : ℝ :=
  Real.sqrt
    (1 /
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)

/-- The normalized positive-half closure Boltzmann amplitude.  The next
geometric bridge only has to identify its closure action with the unfixed
positive-half-cylinder action; no boundary square-root coefficient remains. -/
noncomputable def periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
      H N hN beta hbeta *
    Real.exp
      (-beta * periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction
        H N b x)

/-- The existing OS scalar Gram feature is exactly the partition-normalized
Boltzmann amplitude of the concrete positive-half closure action.

This is the normalization bridge needed before comparing the OS closure action
with the transfer-theoretic positive-half-cylinder action. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedClosureBoltzmann
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x =
      periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
        H N hN beta hbeta b x := by
  let A :=
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      b x (fun _ => 1)
  let Z :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction
  let Sfixed := periodicHypercubicEvenSpatialCrossingWilsonAction H N A
  let Splus := periodicHypercubicEvenPositiveWilsonAction H N A
  let St := periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A
  let Sclosure := (1 / 2 : ℝ) * Sfixed + Splus + St
  have hZ : 0 < Z := by
    dsimp [Z]
    exact
      compact_oriented_partitionFunction_pos
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base
        (continuous_compact_oriented_boltzmannIntegrable
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
  have hboundary :
      periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
          H N beta b = Real.exp (-beta * Sfixed) := by
    simpa [A, Sfixed] using
      periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_eq_closure_boltzmann
        H N beta b x
  have hamp :
      periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H N beta b x =
        Real.exp (-beta * (Splus + St)) := by
    simpa [A, Splus, St] using
      periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_eq_boltzmann
        H N beta b x
  have hc :
      0 ≤ periodicHypercubicEvenBoundaryGramCoefficient H N hN beta hbeta b :=
    periodicHypercubicEvenBoundaryGramCoefficient_nonneg
      H N hN beta hbeta b
  have hInvZ : 0 ≤ (1 / Z : ℝ) := by
    positivity
  have hfeatureSq :
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x) ^ 2 =
        Real.exp (-2 * beta * Sclosure) / Z := by
    unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    rw [show periodicHypercubicEvenBoundaryGramCoefficient H N hN beta hbeta b =
        periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight H N beta b / Z by
      rfl]
    rw [hboundary, hamp]
    calc
      (Real.sqrt (Real.exp (-beta * Sfixed) / Z) *
          Real.exp (-beta * (Splus + St))) ^ 2 =
        (Real.exp (-beta * Sfixed) / Z) *
          (Real.exp (-beta * (Splus + St))) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt]
            · rfl
            · exact div_nonneg (Real.exp_nonneg _) (le_of_lt hZ)
      _ = Real.exp (-2 * beta * Sclosure) / Z := by
        rw [pow_two, ← Real.exp_add]
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        congr 1
        dsimp [Sclosure]
        ring
  have hnormalizedSq :
      (periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
          H N hN beta hbeta b x) ^ 2 =
        Real.exp (-2 * beta * Sclosure) / Z := by
    unfold periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
    unfold periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
    change
      (Real.sqrt (1 / Z) *
        Real.exp
          (-beta * periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction
            H N b x)) ^ 2 = _
    have hclosure :
        periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction H N b x =
          Sclosure := by
      rfl
    rw [hclosure]
    calc
      (Real.sqrt (1 / Z) * Real.exp (-beta * Sclosure)) ^ 2 =
          (1 / Z) * (Real.exp (-beta * Sclosure)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hInvZ]
      _ = Real.exp (-2 * beta * Sclosure) / Z := by
        rw [pow_two, ← Real.exp_add]
        field_simp [ne_of_gt hZ]
        congr 1
        ring
  have hfeatureNonneg :
      0 ≤ periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x := by
    unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    exact mul_nonneg (Real.sqrt_nonneg _) (by rw [hamp]; exact Real.exp_nonneg _)
  have hnormalizedNonneg :
      0 ≤ periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
        H N hN beta hbeta b x := by
    unfold periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
    unfold periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  have hsq :
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x) ^ 2 =
        (periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
          H N hN beta hbeta b x) ^ 2 :=
    hfeatureSq.trans hnormalizedSq.symm
  nlinarith

end

end MathlibAnalytic
end MGAP4D
