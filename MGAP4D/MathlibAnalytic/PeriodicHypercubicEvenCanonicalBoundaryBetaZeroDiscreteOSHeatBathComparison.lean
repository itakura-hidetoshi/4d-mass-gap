import MGAP4D.MathlibAnalytic.RealHilbertDiscreteSemigroupComparisonDefect
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryBetaZeroSemigroupPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryBetaZeroDiscreteComparisonNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryBetaZeroDiscreteComparisonTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryBetaZeroDiscreteComparisonCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryBetaZeroDiscreteComparisonSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryBetaZeroDiscreteComparisonMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryBetaZeroDiscreteComparisonBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Sample the complete beta-zero canonical boundary heat-bath family at a
fixed real time spacing `a`.  This is a bounded-operator discrete group sample;
its Markov interpretation is restricted to nonnegative sampled times. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (n : ℕ) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
    H N hN 0 le_rfl ((n : ℝ) * a)

@[simp] theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
        H N hN a 0 = 1 := by
  simp [periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2,
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_zero]

/-- The sampled family satisfies the exact natural-time additive law. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_add
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (m n : ℕ) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
        H N hN a (m + n) =
      periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a m *
        periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a n := by
  unfold periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
  have htime : (((m + n : ℕ) : ℝ) * a) =
      (m : ℝ) * a + (n : ℝ) * a := by
    push_cast
    ring
  rw [htime]
  exact
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add_betaZero
      H N hN ((m : ℝ) * a) ((n : ℝ) * a)

/-- Sampling a beta-zero bounded exponential at a fixed spacing gives exactly
the natural powers of its one-step sample. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_eq_pow
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (n : ℕ) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
        H N hN a n =
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a) ^ n := by
  induction n with
  | zero =>
      simp [periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2,
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_zero]
  | succ n ih =>
      rw [periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_add,
        ih, pow_succ]
      simp [periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2]

/-- Every sampled beta-zero heat-bath operator fixes the concrete boundary
vacuum. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_vacuum
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (n : ℕ) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
        H N hN a n
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN 0 le_rfl) =
      periodicHypercubicEvenBoundaryVacuumL2 H N hN 0 le_rfl := by
  unfold periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
  exact
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_vacuum
      H N hN 0 le_rfl ((n : ℝ) * a)

/-- Exact comparison defect between a proposed geometric temporal OS one-step
operator and the beta-zero canonical boundary heat-bath sample at spacing `a`.
The bridge is oriented from the canonical boundary carrier into the proposed OS
carrier, so no equality of Hilbert spaces is hidden in notation. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (osTransfer : K →L[ℝ] K) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ] K :=
  realHilbertIsometricDiscreteStepComparisonDefect
    boundaryToOS osTransfer
    (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
      H N hN 0 le_rfl a)

/-- Vanishing of the concrete OS/heat-bath defect is exactly the one-step
intertwining statement. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2_eq_zero_iff
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (osTransfer : K →L[ℝ] K) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer = 0 ↔
      ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
        osTransfer (boundaryToOS f) =
          boundaryToOS
            (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
              H N hN 0 le_rfl a f) := by
  exact realHilbertIsometricDiscreteStepComparisonDefect_eq_zero_iff
    boundaryToOS osTransfer
    (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
      H N hN 0 le_rfl a)

/-- A zero one-step defect identifies every natural OS power with the sampled
beta-zero heat-bath evolution at physical comparison time `n * a`. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransfer_pow_analysis_apply_of_defect_eq_zero
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (osTransfer : K →L[ℝ] K)
    (hD :
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer = 0)
    (n : ℕ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    (osTransfer ^ n) (boundaryToOS f) =
      boundaryToOS
        (periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a n f) := by
  rw [periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_eq_pow]
  exact
    realHilbertIsometricDiscreteStepComparison_pow_apply_of_defect_eq_zero
      boundaryToOS osTransfer
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a)
      hD n f

/-- Under zero defect, adjoint compression of every proposed OS transfer power
is exactly the sampled beta-zero canonical boundary heat-bath operator. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransfer_compression_pow_eq_sampled_of_defect_eq_zero
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (osTransfer : K →L[ℝ] K)
    (hD :
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer = 0)
    (n : ℕ) :
    realHilbertIsometricAdjointCompression boundaryToOS (osTransfer ^ n) =
      periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
        H N hN a n := by
  rw [periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_eq_pow]
  exact
    realHilbertIsometricAdjointCompression_pow_eq_of_discreteStepComparisonDefect_eq_zero
      boundaryToOS osTransfer
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a)
      hD n

/-- A nonzero concrete one-step defect rules out equality of the full proposed
OS natural-time family with the sampled beta-zero heat-bath family through the
chosen bridge. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBath_no_go
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (osTransfer : K →L[ℝ] K)
    (hD :
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer ≠ 0) :
    ¬ (∀ n : ℕ, ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      (osTransfer ^ n) (boundaryToOS f) =
        boundaryToOS
          (periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
            H N hN a n f)) := by
  intro hAll
  apply hD
  apply
    (periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2_eq_zero_iff
      H N hN a boundaryToOS osTransfer).2
  intro f
  simpa [periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2]
    using hAll 1 f

end

end MathlibAnalytic
end MGAP4D
