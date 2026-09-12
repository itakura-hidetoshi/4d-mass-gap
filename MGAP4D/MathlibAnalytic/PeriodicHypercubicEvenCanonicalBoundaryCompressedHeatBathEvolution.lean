import MGAP4D.MathlibAnalytic.RealHilbertIsometricAdjointCompression
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryZeroTimeIntertwining

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance canonicalBoundaryCompressedNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryCompressedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryCompressedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryCompressedSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryCompressedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryCompressedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical boundary compression of the actual centered finite Wilson
heat-bath evolution.  It is defined without assuming that the analyzed
boundary range is dynamically invariant. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : NNReal) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  realHilbertIsometricAdjointCompression
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)

@[simp] theorem
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2_apply
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : NNReal)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
        H N hN beta hbeta t f =
      periodicHypercubicEvenCanonicalBoundarySynthesisL2
        H N hN beta hbeta
        (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f)) :=
  rfl

/-- Boundary matrix coefficients of the compressed evolution are exactly the
ambient Gibbs matrix coefficients between canonically analyzed vectors. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : NNReal)
    (f g : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
          H N hN beta hbeta t f) g =
      inner ℝ
        (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
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
    (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)
    f g

/-- At zero time the compressed centered evolution fixes every vector
orthogonal to the concrete boundary vacuum. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2_zero_of_orthogonal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hf : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2
        H N hN beta hbeta) f = 0) :
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
        H N hN beta hbeta 0 f = f := by
  change
    periodicHypercubicEvenCanonicalBoundarySynthesisL2
        H N hN beta hbeta
        (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          0
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f)) = f
  exact periodicHypercubicEvenCanonicalBoundary_centeredHeatBath_zero_roundTrip
    H N hN beta hbeta f hf

/-- Pointwise dynamic invariance of one analyzed boundary vector makes the
canonical compression recover its exact evolved boundary representative. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2_apply_eq_of_analysis_eq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : NNReal)
    (f g : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hfg :
      ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f) =
        periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta g) :
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
        H N hN beta hbeta t f = g := by
  exact realHilbertIsometricAdjointCompression_apply_eq_of_analysis_eq
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)
    f g hfg

/-- If the analyzed boundary range is invariant at time `t`, the canonical
compression itself satisfies exact positive-time intertwining. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2_analysis_apply_of_range
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : NNReal)
    (hRange : ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      ∃ g : PeriodicHypercubicEvenBoundaryHaarL2 H N,
        ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
            (periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
            t
            (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
              H N hN beta hbeta f) =
          periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta g)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
          H N hN beta hbeta t f) =
      ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
        t
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) := by
  exact realHilbertIsometricAdjointCompression_analysis_apply_of_range
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)
    hRange f

/-- Any independently constructed boundary evolution satisfying exact
positive-time intertwining is forced to equal the canonical adjoint
compression. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2_eq_of_intertwines
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : NNReal)
    (B : PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hintertwine : ∀ f,
      ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f) =
        periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta (B f)) :
    periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
        H N hN beta hbeta t = B := by
  exact realHilbertIsometricAdjointCompression_eq_of_intertwines
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
      t)
    B hintertwine

end

end MathlibAnalytic
end MGAP4D
