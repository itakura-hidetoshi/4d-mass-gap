import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathLaw
import MGAP4D.MathlibAnalytic.KolmogorovPolishExtension

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRealProjectiveNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRealProjectiveTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRealProjectiveCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRealProjectiveSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRealProjectiveMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRealProjectiveBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Finite-dimensional real-time marginal of the directly constructed floor
path law. Every coordinate is indexed by an actual physical real time. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ)
    (J : Finset ℝ) : Measure (∀ t : J, ℝ) :=
  Measure.map J.restrict
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
      H N hN beta hbeta latticeSpacing n)

/-- Probability-measure packaging of each finite real-time marginal. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteProbabilityMarginal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ)
    (J : Finset ℝ) : ProbabilityMeasure (∀ t : J, ℝ) :=
  (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure
    H N hN beta hbeta latticeSpacing n).map
      J.measurable_restrict.aemeasurable

@[simp]
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteProbabilityMarginal_toMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ)
    (J : Finset ℝ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteProbabilityMarginal
      H N hN beta hbeta latticeSpacing n J : Measure (∀ t : J, ℝ)) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal
        H N hN beta hbeta latticeSpacing n J := by
  rfl

instance
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ)
    (J : Finset ℝ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal
        H N hN beta hbeta latticeSpacing n J) := by
  rw [←
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteProbabilityMarginal_toMeasure
      H N hN beta hbeta latticeSpacing n J]
  infer_instance

/-- Finite real-time marginals from one directly constructed path law are
projectively consistent under coordinate restriction.

This is a same-source theorem: consistency follows from restriction of one
measure, not from an independently postulated family of finite-dimensional
laws. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal_projective
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ => ℝ)
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal
        H N hN beta hbeta latticeSpacing n) := by
  intro I J hJI
  let μ :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
      H N hN beta hbeta latticeSpacing n
  let r : (∀ t : I, ℝ) → (∀ t : J, ℝ) := Finset.restrict₂ hJI
  have hI : Measurable I.restrict := I.measurable_restrict
  have hr : Measurable r :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  change μ.map J.restrict = (μ.map I.restrict).map r
  calc
    μ.map J.restrict = μ.map (r ∘ I.restrict) := by
      apply congrArg (fun f => μ.map f)
      funext x
      ext t
      rfl
    _ = (μ.map I.restrict).map r := (Measure.map_map hr hI).symm

/-- The directly constructed full real-indexed floor path law is already a
projective limit of its finite-dimensional real-time marginals. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_isProjectiveLimit
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    IsProjectiveLimit (α := fun _ : ℝ => ℝ)
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
        H N hN beta hbeta latticeSpacing n)
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal
        H N hN beta hbeta latticeSpacing n) := by
  intro J
  rfl

/-- Canonical Kolmogorov reconstruction from the finite real-time cylinder laws.

This definition is included as a compatibility bridge to the existing Polish
Kolmogorov infrastructure; the next theorem shows that it does not create a new
finite-scale law. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathKolmogorovMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) : Measure (ℝ → ℝ) :=
  kolmogorovProjectiveLimit (α := fun _ : ℝ => ℝ)
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal
      H N hN beta hbeta latticeSpacing n)
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal_projective
      H N hN beta hbeta latticeSpacing n)

/-- At finite scale, applying the repository's Polish Kolmogorov extension to
the cylinder laws reconstructs exactly the direct same-Wilson-source floor path
measure.

Thus no independent Kolmogorov existence assumption is needed or introduced in
the finite temporal path construction. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathKolmogorovMeasure_eq_direct
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathKolmogorovMeasure
        H N hN beta hbeta latticeSpacing n =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  let P :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal
      H N hN beta hbeta latticeSpacing n
  have hP : IsProjectiveMeasureFamily (α := fun _ : ℝ => ℝ) P :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathFiniteMarginal_projective
      H N hN beta hbeta latticeSpacing n
  have hKolmogorov :
      IsProjectiveLimit (α := fun _ : ℝ => ℝ)
        (kolmogorovProjectiveLimit (α := fun _ : ℝ => ℝ) P hP) P :=
    isProjectiveLimit_kolmogorovProjectiveLimit (α := fun _ : ℝ => ℝ) hP
  have hDirect :
      IsProjectiveLimit (α := fun _ : ℝ => ℝ)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n) P :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_isProjectiveLimit
      H N hN beta hbeta latticeSpacing n
  exact hKolmogorov.unique hDirect

end

end MathlibAnalytic
end MGAP4D
