import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalReflectionCovariance

/-!
# Finite rational-cylinder reflection covariance

The merged pointwise reflection theorem applies whenever one rational physical
time is an exact lattice multiple.  This file packages the corresponding finite
cylinder statement and proves that the canonical factorial spacing aligns every
fixed finite rational cylinder simultaneously after finitely many scales.

The result is still deterministic: it compares readouts of one finite Wilson
configuration and its geometric reflection.  No Gibbs-measure reflection
invariance or continuum OS positivity is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

local instance finiteRationalCylinderReflectionCovarianceNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance finiteRationalCylinderReflectionCovarianceTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteRationalCylinderReflectionCovarianceCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteRationalCylinderReflectionCovarianceSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteRationalCylinderReflectionCovarianceMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteRationalCylinderReflectionCovarianceBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every fixed finite set of rational physical times is simultaneously an exact
subset of the factorial lattice subgroup at all sufficiently large scales. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_finsetRational_eventually_latticeMultiple
    (J : Finset ℚ) :
    ∀ᶠ s : ℕ in atTop,
      ∀ q ∈ J,
        ∃ k : ℤ,
          (q : ℝ) =
            (k : ℝ) *
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing s := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      simp
  | @insert q J hq ih =>
      filter_upwards [
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_eventually_latticeMultiple
          q,
        ih] with s hqs hJs
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrJ
      · exact hqs
      · exact hJs r hrJ

/-- Finite labelled rational insertion tuples are simultaneously factorial-lattice
aligned eventually. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_finRational_eventually_latticeMultiple
    (m : ℕ) (time : Fin m → ℚ) :
    ∀ᶠ s : ℕ in atTop,
      ∀ i : Fin m,
        ∃ k : ℤ,
          (time i : ℝ) =
            (k : ℝ) *
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing s := by
  classical
  filter_upwards [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_finsetRational_eventually_latticeMultiple
      (Finset.univ.image time)] with s hs
  intro i
  exact hs (time i) (by simp)

/-- If every coordinate of a finite rational cylinder is exactly lattice aligned,
then reflecting the finite Wilson configuration is exactly the same as reflecting
all rational cylinder times. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_finset_configurationReflection_of_latticeMultiple
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ s, 0 < latticeSpacing s)
    (s : ℕ) (J : Finset ℚ)
    (hAlign : ∀ q ∈ J,
      ∃ k : ℤ, (q : ℝ) = (k : ℝ) * latticeSpacing s)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (fun q : J =>
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing s
        (periodicHypercubicEvenConfigurationReflection H A) (q : ℚ)) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReflectionReadout
        J
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
          H N hN beta hbeta latticeSpacing s A) := by
  funext q
  rcases hAlign (q : ℚ) q.property with ⟨k, hk⟩
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_apply_configurationReflection_of_latticeMultiple
      H N hN beta hbeta latticeSpacing latticeSpacing_pos s (q : ℚ) k hk A

/-- Labelled-slot form of finite rational-cylinder reflection covariance. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_fin_configurationReflection_of_latticeMultiple
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ s, 0 < latticeSpacing s)
    (s m : ℕ) (time : Fin m → ℚ)
    (hAlign : ∀ i : Fin m,
      ∃ k : ℤ, (time i : ℝ) = (k : ℝ) * latticeSpacing s)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (fun i : Fin m =>
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing s
        (periodicHypercubicEvenConfigurationReflection H A) (time i)) =
      (fun i : Fin m =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
          H N hN beta hbeta latticeSpacing s A (-time i)) := by
  funext i
  rcases hAlign i with ⟨k, hk⟩
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_apply_configurationReflection_of_latticeMultiple
      H N hN beta hbeta latticeSpacing latticeSpacing_pos s (time i) k hk A

/-- For a fixed labelled finite rational cylinder, factorial spacing makes the
full finite-cylinder reflection covariance exact at every sufficiently large
scale. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_finRational_configurationReflection_eventually
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ s, 0 ≤ beta s)
    (m : ℕ) (time : Fin m → ℚ) :
    ∀ᶠ s : ℕ in atTop,
      ∀ A : PeriodicHypercubicEvenEdge (H s) →
          Matrix.specialUnitaryGroup (Fin N) ℂ,
        (fun i : Fin m =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
            (H s) N hN (beta s) (hbeta s)
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing s
            (periodicHypercubicEvenConfigurationReflection (H s) A) (time i)) =
          (fun i : Fin m =>
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
              (H s) N hN (beta s) (hbeta s)
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing s
              A (-time i)) := by
  filter_upwards [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_finRational_eventually_latticeMultiple
      m time] with s hs
  intro A
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_fin_configurationReflection_of_latticeMultiple
      (H s) N hN (beta s) (hbeta s)
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      s m time hs A

end
end MathlibAnalytic
end MGAP4D
