import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryBetaZeroGeneratorInvariance
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanRayleighL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryBetaZeroSemigroupNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryBetaZeroSemigroupTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryBetaZeroSemigroupCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryBetaZeroSemigroupSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryBetaZeroSemigroupMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryBetaZeroSemigroupBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At beta zero, compression preserves the Hamiltonian second moment exactly. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMoment_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    realHilbertIsometricAdjointCompression
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN 0 (by norm_num))
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).heatBathHamiltonianL2 *
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).heatBathHamiltonianL2) =
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN 0 (by norm_num) *
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN 0 (by norm_num) := by
  have h := periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMoment_decomposition
    H N hN 0 (by norm_num)
  rw [periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_betaZero]
    at h
  simpa using h

/-- Product-Haar tensorization transfers the sharp beta-zero Poincare constant
one to the canonical boundary Hamiltonian. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_poincare_one_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    ‖periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
      H N hN 0 (by norm_num) f‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN 0 (by norm_num) f) f := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  have hPoincare : C.HeatBathPoincareL2 1 :=
    continuous_compact_oriented_heatBathPoincareL2_one_of_beta_eq_zero
      C (by rfl)
  simpa using
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_poincare
      H N hN 0 (by norm_num) 1 hPoincare f

/-- The canonical beta-zero boundary Hamiltonian is coercive with constant one
on the concrete boundary-vacuum orthogonal sector. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_coercive_one_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hf : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2
        H N hN 0 (by norm_num)) f = 0) :
    ‖f‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN 0 (by norm_num) f) f := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  have hPoincare : C.HeatBathPoincareL2 1 :=
    continuous_compact_oriented_heatBathPoincareL2_one_of_beta_eq_zero
      C (by rfl)
  simpa using
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_coercive
      H N hN 0 (by norm_num) 1 hPoincare f hf

/-- No nonzero vacuum-orthogonal beta-zero boundary vector can have zero
heat-bath energy. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_kernel_eq_zero_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hfOrth : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2
        H N hN 0 (by norm_num)) f = 0)
    (hfZero : periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
      H N hN 0 (by norm_num) f = 0) :
    f = 0 := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  have hPoincare : C.HeatBathPoincareL2 1 :=
    continuous_compact_oriented_heatBathPoincareL2_one_of_beta_eq_zero
      C (by rfl)
  exact
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_kernel_eq_zero
      H N hN 0 (by norm_num) 1 (by norm_num) hPoincare f hfOrth hfZero

/-- The compressed full beta-zero heat-bath evolution is exactly the bounded
operator exponential of the canonical boundary generator at every real time. -/
theorem periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_boundaryExponential_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (t : ℝ) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 (by norm_num) t =
      realContinuousLinearOperatorExponentialSemigroup
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
          H N hN 0 (by norm_num)) t :=
  periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_boundaryExponential_of_generatorDefect_eq_zero
    H N hN 0 (by norm_num)
    (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
      H N hN) t

/-- Exact ambient-boundary intertwining holds at every real beta-zero
heat-bath time. -/
theorem periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (t : ℝ) (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN 0 (by norm_num)
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 (by norm_num) t f) =
      ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)) t
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN 0 (by norm_num) f) :=
  periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply_of_generatorDefect_eq_zero
    H N hN 0 (by norm_num)
    (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
      H N hN) t f

/-- The analyzed boundary range is invariant under every real beta-zero
heat-bath time. -/
theorem periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant
      H N hN 0 (by norm_num) :=
  periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant_of_generatorDefect_eq_zero
    H N hN 0 (by norm_num)
    (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
      H N hN)

/-- The compressed beta-zero boundary family satisfies the exact additive
semigroup law without a separate range hypothesis. -/
theorem periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (s t : ℝ) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 (by norm_num) (s + t) =
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 (by norm_num) s *
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 (by norm_num) t :=
  periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add_of_generatorDefect_eq_zero
    H N hN 0 (by norm_num)
    (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
      H N hN) s t

/-- The complete beta-zero boundary evolution is operator-norm continuous. -/
theorem periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_continuous_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Continuous
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 (by norm_num)) :=
  periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_continuous_of_generatorDefect_eq_zero
    H N hN 0 (by norm_num)
    (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
      H N hN)

/-- The beta-zero operator-norm derivative exists at every real time and is
generated by `-(1/2) H_boundary`. -/
theorem periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_hasDerivAt_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (t : ℝ) :
    HasDerivAt
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 (by norm_num))
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 (by norm_num) t *
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
          H N hN 0 (by norm_num)) t :=
  periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_hasDerivAt_of_generatorDefect_eq_zero
    H N hN 0 (by norm_num)
    (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
      H N hN) t

end

end MathlibAnalytic
end MGAP4D