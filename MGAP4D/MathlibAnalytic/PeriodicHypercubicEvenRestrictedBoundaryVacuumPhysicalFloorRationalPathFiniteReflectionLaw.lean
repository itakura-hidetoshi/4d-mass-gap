import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFiniteReflectionCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryWilsonReflectionInvariance

/-!
# Finite rational-cylinder reflection laws from the actual Wilson Gibbs measure

The deterministic finite-cylinder covariance layer already proves that, once a
fixed rational insertion tuple is exactly aligned with the lattice spacing,
reflecting the finite Wilson configuration sends every labelled time `t_i` to
`-t_i`.

The actual finite even-periodic `SU(N)` Wilson Gibbs measure is independently
known to be exactly reflection invariant.  Combining these two same-source
facts gives equality of the reflected and unreflected finite-dimensional path
laws.  For the canonical factorial spacing, every fixed finite rational tuple is
simultaneously aligned at all sufficiently large scales, hence this equality is
eventually exact along every Prokhorov subsequence.

This file deliberately stops at the finite-dimensional law level.  No continuum
reflection invariance, OS positivity, spectral theorem, decay estimate, or new
physical hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance finiteRationalCylinderReflectionLawNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance finiteRationalCylinderReflectionLawTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteRationalCylinderReflectionLawCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteRationalCylinderReflectionLawSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteRationalCylinderReflectionLawMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteRationalCylinderReflectionLawBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At one finite Wilson scale, exact alignment of a labelled rational cylinder
turns deterministic reflection covariance plus Gibbs reflection invariance into
literal equality of the reflected and unreflected joint laws. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_map_fin_reflection_eq_self_of_latticeMultiple
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ s, 0 < latticeSpacing s)
    (s m : ℕ) (time : Fin m → ℚ)
    (hAlign : ∀ i : Fin m,
      ∃ k : ℤ, (time i : ℝ) = (k : ℝ) * latticeSpacing s) :
    Measure.map
        (fun x : ℚ → ℝ => fun i : Fin m => x (-time i))
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
          H N hN beta hbeta latticeSpacing s) =
      Measure.map
        (fun x : ℚ → ℝ => fun i : Fin m => x (time i))
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
          H N hN beta hbeta latticeSpacing s) := by
  let readout :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
      H N hN beta hbeta latticeSpacing s
  let slot : (ℚ → ℝ) → (Fin m → ℝ) := fun x i => x (time i)
  let slotRef : (ℚ → ℝ) → (Fin m → ℝ) := fun x i => x (-time i)
  let R :
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) →
        (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    periodicHypercubicEvenConfigurationReflection
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H
  let μ :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  have hreadout : Measurable readout :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_measurable
      H N hN beta hbeta latticeSpacing s
  have hslot : Measurable slot := by
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply (time i))
  have hslotRef : Measurable slotRef := by
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply (-time i))
  have hR : Measurable R :=
    (periodicHypercubicEvenSpecialUnitary_gibbs_measurePreserving_reflection
      H N hN beta hbeta).measurable
  have hμR : Measure.map R μ = μ := by
    simpa [R, μ] using
      periodicHypercubicEvenSpecialUnitary_gibbs_map_reflection_eq_self
        H N hN beta hbeta
  have hcov : slotRef ∘ readout = (slot ∘ readout) ∘ R := by
    funext A
    have h :=
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_fin_configurationReflection_of_latticeMultiple
        H N hN beta hbeta latticeSpacing latticeSpacing_pos s m time hAlign A
    simpa [readout, slot, slotRef, R, Function.comp_def] using h.symm
  change Measure.map slotRef (Measure.map readout μ) =
    Measure.map slot (Measure.map readout μ)
  calc
    Measure.map slotRef (Measure.map readout μ) =
        Measure.map (slotRef ∘ readout) μ :=
      Measure.map_map hslotRef hreadout
    _ = Measure.map ((slot ∘ readout) ∘ R) μ := by
      rw [hcov]
    _ = Measure.map (slot ∘ readout) (Measure.map R μ) :=
      (Measure.map_map (hslot.comp hreadout) hR).symm
    _ = Measure.map (slot ∘ readout) μ := by
      rw [hμR]
    _ = Measure.map slot (Measure.map readout μ) :=
      (Measure.map_map hslot hreadout).symm

/-- For factorial spacing, the finite-dimensional reflected/unreflected law
identity is eventually exact along every strict Prokhorov subsequence.  The
statement keeps labelled slots, so repeated rational times remain allowed. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_subsequence_fin_reflection_jointLaw_eventually_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (m : ℕ) (time : Fin m → ℚ) :
    ∀ᶠ n : ℕ in atTop,
      Measure.map
          (fun x : ℚ → ℝ => fun i : Fin m => x (-time i))
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) =
        Measure.map
          (fun x : ℚ → ℝ => fun i : Fin m => x (time i))
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) := by
  have hAligned :
      ∀ᶠ n : ℕ in atTop,
        ∀ i : Fin m,
          ∃ k : ℤ,
            (time i : ℝ) =
              (k : ℝ) *
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                  (L.subsequence n) :=
    L.subsequence_strictMono.tendsto_atTop.eventually
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_finRational_eventually_latticeMultiple
        m time)
  filter_upwards [hAligned] with n hn
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_map_fin_reflection_eq_self_of_latticeMultiple
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      (L.subsequence n) m time hn

end
end MathlibAnalytic
end MGAP4D
