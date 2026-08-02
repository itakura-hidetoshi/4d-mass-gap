import MGAP4D.MathlibAnalytic.RealHilbertIsometricAdjointCompressionGeneratorDefect
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryFullHeatBathSemigroupPackage

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryGeneratorDefectNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryGeneratorDefectTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryGeneratorDefectCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryGeneratorDefectSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryGeneratorDefectMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryGeneratorDefectBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The exact finite Wilson generator leakage away from the canonical analyzed
boundary subspace. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).GibbsRealL2 :=
  realHilbertIsometricAdjointCompressionGeneratorDefect
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2

@[simp] theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_apply
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta f =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f) -
        periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f) :=
  rfl

/-- The actual Gibbs heat-bath generator action on an analyzed boundary state
has a canonical orthogonal decomposition. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_decomposition
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) =
      periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f) +
        periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
          H N hN beta hbeta f := by
  exact realHilbertIsometricAdjointCompressionGeneratorDefect_decomposition
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
    f

/-- The finite Wilson generator defect is orthogonal to the complete analyzed
boundary range. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_inner_analysis
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
          H N hN beta hbeta f)
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta g) = 0 := by
  exact realHilbertIsometricAdjointCompressionGeneratorDefect_inner_analysis
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
    f g

/-- Canonical adjoint synthesis discards precisely the orthogonal generator
leakage. -/
theorem
    periodicHypercubicEvenCanonicalBoundarySynthesisL2_generatorDefect
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundarySynthesisL2
        H N hN beta hbeta
        (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
          H N hN beta hbeta f) = 0 := by
  exact realHilbertAdjointSynthesis_generatorDefect
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
    f

/-- Exact energy decomposition: the ambient generator energy consists of the
boundary Hamiltonian energy plus the generator-defect energy. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_energy_decomposition
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f))
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f)) =
      inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f)
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f) +
        inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
            H N hN beta hbeta f)
          (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
            H N hN beta hbeta f) := by
  exact
    realHilbertIsometricAdjointCompressionGeneratorDefect_inner_self_decomposition
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
      f

/-- Generator-level invariance of the concrete analyzed boundary range. -/
def periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop :=
  realHilbertIsometricAdjointCompressionGeneratorRangeInvariant
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2

/-- The previously open generator-range condition is equivalent to one
explicit finite Wilson operator equation. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant_iff_defect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant
        H N hN beta hbeta ↔
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0 := by
  exact
    realHilbertIsometricAdjointCompressionGeneratorRangeInvariant_iff_defect_eq_zero
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2

/-- The finite Wilson generator defect vanishes exactly when all of its state
energies vanish. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_eq_zero_iff_energy
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0 ↔
      ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
        inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
            H N hN beta hbeta f)
          (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
            H N hN beta hbeta f) = 0 := by
  exact
    realHilbertIsometricAdjointCompressionGeneratorDefect_eq_zero_iff_inner_self
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2

/-- The concrete boundary vacuum has no generator leakage. -/
@[simp] theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_vacuum
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) = 0 := by
  rw [periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_apply,
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum,
    continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_vacuum]
  simp

/-- Zero generator defect gives exact intertwining for every natural power of
the actual finite Wilson heat-bath Hamiltonian. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_pow_analysis_apply_of_defect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0)
    (n : ℕ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    ((periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2 ^ n)
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) =
      periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta
        ((periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta ^ n) f) := by
  exact
    realHilbertIsometricAdjointCompression_pow_analysis_apply_of_defect_eq_zero
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
      hDefect n f

/-- Under zero generator defect, every ambient Hamiltonian moment compresses
to the corresponding boundary Hamiltonian moment. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_pow_compression_of_defect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0)
    (n : ℕ) :
    realHilbertIsometricAdjointCompression
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta)
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2 ^ n) =
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
        H N hN beta hbeta ^ n := by
  exact realHilbertIsometricAdjointCompression_pow_of_defect_eq_zero
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
    hDefect n

end

end MathlibAnalytic
end MGAP4D