import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMoment

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

local instance boundaryVacuumPositivityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryVacuumPositivityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryVacuumPositivityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryVacuumPositivitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryVacuumPositivityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryVacuumPositivityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance boundaryVacuumPositivityOpenHalfNeZero (H N : ℕ) :
    NeZero (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  unfold periodicHypercubicEvenOpenHalfHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure
  infer_instance

/-- The boundary-only coefficient in the reflected Wilson Gram kernel is
strictly positive. -/
theorem periodicHypercubicEvenBoundaryGramCoefficient_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    0 < periodicHypercubicEvenBoundaryGramCoefficient
      H N hN beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryGramCoefficient
  apply div_pos
  · unfold periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
    unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
    exact Real.exp_pos _
  · exact compact_oriented_partitionFunction_pos
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base
      (continuous_compact_oriented_boltzmannIntegrable
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))

/-- Every completed positive-half Wilson amplitude is strictly positive. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_pos
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    0 < periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
      H N beta b x := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  apply mul_pos
  · unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
    exact Real.exp_pos _
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
    exact Real.exp_pos _

/-- The scalar boundary Gram feature is pointwise strictly positive. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    0 < periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta b x := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  exact mul_pos
    (Real.sqrt_pos.2
      (periodicHypercubicEvenBoundaryGramCoefficient_pos
        H N hN beta hbeta b))
    (periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_pos
      H N beta b x)

/-- The finite Wilson OS boundary vacuum wavefunction is pointwise strictly
positive. Hence division by it is available on the full boundary Haar space,
not merely almost everywhere under the interacting marginal. -/
theorem periodicHypercubicEvenBoundaryVacuumMoment_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    0 < periodicHypercubicEvenBoundaryVacuumMoment
      H N hN beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryVacuumMoment
  rw [integral_pos_iff_support_of_nonneg]
  · have hsupport :
        Function.support
            (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta b) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
          H N hN beta hbeta b x)
    rw [hsupport]
    have hne :
        periodicHypercubicEvenOpenHalfHaarMeasure H N Set.univ ≠ 0 :=
      MeasureTheory.measure_univ_ne_zero.mpr
        (NeZero.ne (periodicHypercubicEvenOpenHalfHaarMeasure H N))
    exact lt_of_le_of_ne (zero_le _) hne.symm
  · exact fun x => le_of_lt
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
        H N hN beta hbeta b x)
  · exact periodicHypercubicEvenBoundaryVacuumGramFeature_integrable
      H N hN beta hbeta b

end

end MathlibAnalytic
end MGAP4D
