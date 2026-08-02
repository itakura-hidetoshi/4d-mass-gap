import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectPackage

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryGeneratorDefectFinalNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryGeneratorDefectFinalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryGeneratorDefectFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryGeneratorDefectFinalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryGeneratorDefectFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryGeneratorDefectFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Final unconditional finite Wilson generator-defect package: every ambient
generator state splits into its canonical boundary Hamiltonian component and
an orthogonal leakage component, and the concrete vacuum leakage is zero. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryHeatBathGeneratorDefectPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f) =
        periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta
            (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
              H N hN beta hbeta f) +
          periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
            H N hN beta hbeta f) ∧
    (∀ f g : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
            H N hN beta hbeta f)
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta g) = 0) ∧
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_decomposition
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_inner_analysis
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_vacuum
        H N hN beta hbeta

/-- Final exact characterization of the remaining finite Wilson boundary
invariance obligation.  It is equivalent both to zero generator leakage and
to vanishing of every leakage energy. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryHeatBathGeneratorInvarianceCharacterization
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant
        H N hN beta hbeta ↔
      (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
          H N hN beta hbeta = 0 ∧
        ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
          inner ℝ
            (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
              H N hN beta hbeta f)
            (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
              H N hN beta hbeta f) = 0) := by
  constructor
  · intro hRange
    have hDefect :
        periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
          H N hN beta hbeta = 0 :=
      (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant_iff_defect_eq_zero
        H N hN beta hbeta).mp hRange
    refine ⟨hDefect, ?_⟩
    exact
      (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_eq_zero_iff_energy
        H N hN beta hbeta).mp hDefect
  · rintro ⟨hDefect, _⟩
    exact
      (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant_iff_defect_eq_zero
        H N hN beta hbeta).mpr hDefect

/-- Under the now-isolated zero-defect condition, every finite Hamiltonian
moment intertwines and compresses exactly. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryHeatBathGeneratorMomentPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0) :
    (∀ n : ℕ, ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2 ^ n)
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f) =
        periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta
          ((periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta ^ n) f)) ∧
    (∀ n : ℕ,
      realHilbertIsometricAdjointCompression
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta)
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2 ^ n) =
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta ^ n) := by
  constructor
  · intro n f
    exact
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_pow_analysis_apply_of_defect_eq_zero
        H N hN beta hbeta hDefect n f
  · intro n
    exact
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_pow_compression_of_defect_eq_zero
        H N hN beta hbeta hDefect n

end

end MathlibAnalytic
end MGAP4D