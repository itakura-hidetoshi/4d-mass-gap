import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFullHeatBathSemigroupPackage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolution
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryFullSemigroupNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryFullSemigroupTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryFullSemigroupCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryFullSemigroupSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryFullSemigroupMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryFullSemigroupBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical boundary compression of the full, vacuum-preserving actual
finite Wilson heat-bath semigroup.  Unlike the previously constructed centered
compression, its zero-time slice is the identity on the entire boundary
carrier. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : ℝ) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  realHilbertIsometricAdjointCompression
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)

@[simp] theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_apply
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : ℝ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta t f =
      periodicHypercubicEvenCanonicalBoundarySynthesisL2
        H N hN beta hbeta
        (ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f)) :=
  rfl

/-- Boundary matrix coefficients are the corresponding full Gibbs-semigroup
matrix coefficients of the canonically analyzed vectors. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : ℝ)
    (f g : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t f) g =
      inner ℝ
        (ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f))
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta g) := by
  exact realHilbertIsometricAdjointCompression_inner
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)
    f g

/-- The full boundary compression starts from the identity on the complete
boundary Haar `L²` carrier. -/
@[simp] theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta 0 = 1 := by
  unfold periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
  rw [continuous_compact_oriented_fullHeatBathEvolutionRealL2_zero]
  exact realHilbertIsometricAdjointCompression_id
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)

/-- The concrete OS boundary vacuum is fixed at every real time. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_vacuum
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : ℝ) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta t
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) =
      periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta := by
  rw [periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_apply,
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum,
    continuous_compact_oriented_fullHeatBathEvolutionRealL2_vacuum,
    periodicHypercubicEvenCanonicalBoundarySynthesisL2_vacuum]

/-- The strong time-zero derivative of the full boundary evolution is exactly
minus one half of the canonical compressed boundary Hamiltonian. -/
set_option maxHeartbeats 1000000 in
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_hasDerivAt_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    HasDerivAt
      (fun t : ℝ =>
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t f)
      (-(1 / 2 : ℝ) •
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta f) 0 := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN beta hbeta
  let S := periodicHypercubicEvenCanonicalBoundarySynthesisL2
    H N hN beta hbeta
  have hE :=
    continuous_compact_oriented_fullHeatBathEvolutionRealL2_hasDerivAt_zero_apply
      C (A f)
  have hS : HasDerivAt (fun _ : ℝ => S) 0 0 :=
    hasDerivAt_const (0 : ℝ) S
  have hcomp := hS.clm_apply hE
  simpa [C, A, S,
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_apply,
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_apply,
    map_smul] using hcomp

/-- At nonnegative time, the full boundary compression agrees with the earlier
centered compression on the concrete vacuum-orthogonal sector. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_centered_of_orthogonal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : NNReal)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hf : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f = 0) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta (t : ℝ) f =
      periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
        H N hN beta hbeta t f := by
  rw [periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_apply,
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2_apply]
  apply congrArg
    (periodicHypercubicEvenCanonicalBoundarySynthesisL2
      H N hN beta hbeta)
  have hfA :
      inner ℝ
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsVacuumL2
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) = 0 := by
    rw [periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum_inner]
    exact hf
  rw [continuous_compact_oriented_centeredHeatBathEvolutionL2_eq_full_of_orthogonal
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta f)
      hfA]
  exact continuous_compact_oriented_fullHeatBathEvolutionRealL2_nnreal
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
    t

/-- Global invariance of the analyzed boundary range under the full real-time
heat-bath semigroup.  This is the exact model-specific condition needed for
adjoint compression to become an honest boundary semigroup. -/
def periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop :=
  ∀ t : ℝ, ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
    ∃ g : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f) =
        periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta g

/-- Under analyzed-range invariance, the full boundary compression satisfies
exact ambient intertwining at every real time. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hRange : periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant
      H N hN beta hbeta)
    (t : ℝ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t f) =
      ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
        t
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) := by
  exact realHilbertIsometricAdjointCompression_analysis_apply_of_range
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)
    (hRange t) f

/-- Under the exact model-specific range-invariance condition, the canonical
boundary family is a genuine real-time semigroup. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hRange : periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant
      H N hN beta hbeta)
    (s t : ℝ) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta (s + t) =
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta s *
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t := by
  ext f
  apply
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta).injective
  rw [periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply
      H N hN beta hbeta hRange (s + t) f,
    ContinuousLinearMap.mul_apply,
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply
      H N hN beta hbeta hRange s
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta t f),
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply
      H N hN beta hbeta hRange t f,
    continuous_compact_oriented_fullHeatBathEvolutionRealL2_add]

/-- Exact intertwining also uniquely characterizes the canonical full boundary
semigroup among bounded boundary operator families. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_of_intertwines
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : ℝ)
    (B : PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hintertwine : ∀ f,
      ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f) =
        periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta (B f)) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta t = B := by
  exact realHilbertIsometricAdjointCompression_eq_of_intertwines
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)
    B hintertwine

end

end MathlibAnalytic
end MGAP4D
