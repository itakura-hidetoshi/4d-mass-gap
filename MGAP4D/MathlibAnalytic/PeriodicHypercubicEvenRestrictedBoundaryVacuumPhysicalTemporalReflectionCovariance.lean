import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReflectionAlignment
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTimeReflection

/-!
# Temporal reflection covariance of the actual boundary-vacuum readout

This file proves the finite geometric identity that Euclidean reflection reverses
integer temporal translations.  No measure argument is used: reflection acts on
vertices/positive links explicitly, while integer temporal translation is the
existing coordinate reindexing action.

Combining that conjugacy with the already proved reflection invariance of the
reflection-fixed boundary readout yields

`Psi_t (R A) = Psi_{-t} A`.

At a rational physical time exactly aligned with the lattice spacing, the same
identity becomes literal reflection covariance of the finite rational floor
readout.  Together with factorial eventual alignment, this is the deterministic
bridge needed before passing finite Wilson reflection statements to rational
continuum cylinders.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance restrictedBoundaryVacuumTemporalReflectionCovarianceNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumTemporalReflectionCovarianceTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumTemporalReflectionCovarianceCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumTemporalReflectionCovarianceSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumTemporalReflectionCovarianceMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumTemporalReflectionCovarianceBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Site reflection reverses an arbitrary integer displacement in the temporal
coordinate. -/
theorem periodicHypercubicEvenTimeReflection_add_integerTemporalDisplacement
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H)
    (k : ℤ) :
    periodicHypercubicEvenTimeReflection H
        (v + periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) k) =
      periodicHypercubicEvenTimeReflection H v +
        periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) (-k) := by
  funext i
  by_cases hi : i = (0 : PeriodicHypercubicAxis)
  · subst i
    simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicIntegerTemporalDisplacement]
    ring
  · simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicIntegerTemporalDisplacement, hi]

/-- Physical positive-link reflection conjugates integer temporal edge
translation to the inverse translation. -/
theorem periodicHypercubicEvenEdgeReflection_integerTemporalTranslation
    (H : ℕ) (k : ℤ) (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenEdgeReflection H
        (periodicHypercubicEdgeTranslationEquiv
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicIntegerTemporalDisplacement
            (PeriodicHypercubicEvenSideLength H) k) e) =
      periodicHypercubicEdgeTranslationEquiv
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) (-k))
        (periodicHypercubicEvenEdgeReflection H e) := by
  rcases e with ⟨v, mu⟩
  by_cases hmu : mu = (0 : PeriodicHypercubicAxis)
  · subst mu
    rw [periodicHypercubicEdgeTranslationEquiv_apply]
    rw [periodicHypercubicEvenEdgeReflection_time]
    rw [periodicHypercubicEvenEdgeReflection_time]
    rw [periodicHypercubicEdgeTranslationEquiv_apply]
    apply Prod.ext
    · rw [periodicHypercubicEvenTimeReflection_add_integerTemporalDisplacement]
      unfold periodicHypercubicUnshift
      ac_rfl
    · rfl
  · rw [periodicHypercubicEdgeTranslationEquiv_apply]
    rw [periodicHypercubicEvenEdgeReflection_spatial H _ hmu]
    rw [periodicHypercubicEvenEdgeReflection_spatial H (v, mu) hmu]
    rw [periodicHypercubicEdgeTranslationEquiv_apply]
    apply Prod.ext
    · exact
        periodicHypercubicEvenTimeReflection_add_integerTemporalDisplacement
          H v k
    · rfl

/-- Configuration reflection conjugates the actual integer temporal
configuration action to its inverse. -/
theorem periodicHypercubicEvenConfigurationReflection_integerTemporalTranslation
    {Gauge : Type} [Group Gauge] [MeasurableSpace Gauge]
    (H : ℕ) (k : ℤ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenConfigurationReflection H
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) k A) =
      periodicHypercubicIntegerTemporalConfigurationTranslation
        (PeriodicHypercubicEvenSideLength H) (-k)
        (periodicHypercubicEvenConfigurationReflection H A) := by
  funext e'
  obtain ⟨e, rfl⟩ :=
    (periodicHypercubicEdgeTranslationEquiv
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicIntegerTemporalDisplacement
        (PeriodicHypercubicEvenSideLength H) (-k))).surjective e'
  rw [periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge]
  unfold periodicHypercubicEvenConfigurationReflection
  have hdir :
      (periodicHypercubicEdgeTranslationEquiv
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) (-k)) e).2 = e.2 := by
    rfl
  by_cases htime : e.2 = (0 : PeriodicHypercubicAxis)
  · rw [if_pos (hdir.trans htime), if_pos htime]
    have href :=
      periodicHypercubicEvenEdgeReflection_integerTemporalTranslation
        H (-k) e
    simp only [Int.neg_neg] at href
    rw [href]
    rw [periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge]
  · rw [if_neg (fun h => htime (hdir.symm.trans h)), if_neg htime]
    have href :=
      periodicHypercubicEvenEdgeReflection_integerTemporalTranslation
        H (-k) e
    simp only [Int.neg_neg] at href
    rw [href]
    rw [periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge]

/-- The actual time-indexed boundary-vacuum scalar readout is covariant under
physical Euclidean reflection: reflection sends time `t` to `-t`. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_timeReflection_covariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : ℤ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
        H N hN beta hbeta t
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
        H N hN beta hbeta (-t) A := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
  rw [← periodicHypercubicEvenConfigurationReflection_integerTemporalTranslation
    H t A]
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumMoment_timeReflectionInvariant]
  simp

/-- At an exactly aligned rational physical time, finite rational floor readout
reflection is literal rational time reflection. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_apply_configurationReflection_of_latticeMultiple
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (q : ℚ) (k : ℤ)
    (hq : (q : ℝ) = (k : ℝ) * latticeSpacing n)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing n
        (periodicHypercubicEvenConfigurationReflection H A) q =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing n A (-q) := by
  rw [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_apply_of_latticeMultiple
      H N hN beta hbeta latticeSpacing latticeSpacing_pos n q k hq]
  rw [
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_timeReflection_covariant
      H N hN beta hbeta k A]
  exact
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_apply_neg_of_latticeMultiple
      H N hN beta hbeta latticeSpacing latticeSpacing_pos n q k hq A).symm

end
end MathlibAnalytic
end MGAP4D
