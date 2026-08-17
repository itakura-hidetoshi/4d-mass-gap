import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFiniteReflectionLaw
import Mathlib.Tactic

/-!
# Continuum finite rational-cylinder reflection law from the same Wilson root

The preceding finite layer proves that every fixed labelled rational cylinder
has, along the canonical factorial Prokhorov subsequence, eventually exact
reflection symmetry of its finite Wilson pushforward law.

This file passes that equality through the actual path-valued weak limit.  Both
the reflected and unreflected finite-slot maps are continuous on the countable
product carrier `ℚ → ℝ`, so Mathlib's continuous mapping theorem sends the two
subsequence laws to the corresponding pushforwards of `L.continuumMeasure`.
Eventual equality of the finite mapped laws makes the reflected sequence converge
to the unreflected continuum law as well.  Hausdorff uniqueness of weak limits
then identifies the two continuum finite-dimensional laws exactly.

This is still only a finite-cylinder reflection statement.  No full path-measure
reflection invariance, OS reflection positivity, Hilbert reconstruction,
spectral theorem, decay estimate, or new physical hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance continuumFiniteReflectionLawNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuumFiniteReflectionLawTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuumFiniteReflectionLawCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuumFiniteReflectionLawSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuumFiniteReflectionLawMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuumFiniteReflectionLawBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every labelled finite rational cylinder of the same-root continuum path law
is exactly invariant under simultaneous Euclidean time reflection `t ↦ -t`.

The proof uses only:
* path-valued Prokhorov weak convergence from the actual Wilson sequence;
* the continuous mapping theorem for the two finite-slot readouts;
* eventual exact finite-cylinder reflection equality from the finite Wilson
  Gibbs reflection symmetry; and
* uniqueness of limits in the weak topology of probability measures. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_fin_reflection_jointLaw_eq_self
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
    Measure.map
        (fun x : ℚ → ℝ => fun i : Fin m => x (-time i))
        L.continuumMeasure =
      Measure.map
        (fun x : ℚ → ℝ => fun i : Fin m => x (time i))
        L.continuumMeasure := by
  let E :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop
  let slot : (ℚ → ℝ) → (Fin m → ℝ) := fun x i => x (time i)
  let slotRef : (ℚ → ℝ) → (Fin m → ℝ) := fun x i => x (-time i)
  have hslot : Continuous slot := by
    fun_prop
  have hslotRef : Continuous slotRef := by
    fun_prop
  have hUnreflected :
      Tendsto
        (fun n : ℕ =>
          (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
            hslot.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map hslot.measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n : ℕ => E.toLatticeEmbedding.embeddedMeasure (L.subsequence n))
      L.continuumMeasure L.weakConvergence hslot
  have hReflected :
      Tendsto
        (fun n : ℕ =>
          (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
            hslotRef.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map hslotRef.measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n : ℕ => E.toLatticeEmbedding.embeddedMeasure (L.subsequence n))
      L.continuumMeasure L.weakConvergence hslotRef
  have hFiniteMeasure :
      ∀ᶠ n : ℕ in atTop,
        Measure.map slotRef
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
              (H (L.subsequence n)) N hN
              (beta (L.subsequence n)) (hbeta (L.subsequence n))
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
              (L.subsequence n)) =
          Measure.map slot
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
              (H (L.subsequence n)) N hN
              (beta (L.subsequence n)) (hbeta (L.subsequence n))
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
              (L.subsequence n)) := by
    simpa [slot, slotRef] using
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_subsequence_fin_reflection_jointLaw_eventually_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L m time
  have hFiniteProbability :
      ∀ᶠ n : ℕ in atTop,
        (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
            hslotRef.measurable.aemeasurable =
          (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
            hslot.measurable.aemeasurable := by
    filter_upwards [hFiniteMeasure] with n hn
    rw [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding_embeddedMeasure_eq]
    apply Subtype.ext
    simpa [slot, slotRef] using hn
  have hReflectedToUnreflectedLimit :
      Tendsto
        (fun n : ℕ =>
          (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
            hslotRef.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map hslot.measurable.aemeasurable)) := by
    refine Tendsto.congr' ?_ hUnreflected
    filter_upwards [hFiniteProbability] with n hn
    exact hn.symm
  have hProbabilityEq :
      L.continuumMeasure.map hslotRef.measurable.aemeasurable =
        L.continuumMeasure.map hslot.measurable.aemeasurable :=
    tendsto_nhds_unique hReflected hReflectedToUnreflectedLimit
  have hMeasureEq :=
    congrArg
      (fun μ : ProbabilityMeasure (Fin m → ℝ) => (μ : Measure (Fin m → ℝ)))
      hProbabilityEq
  simpa [slot, slotRef] using hMeasureEq

end

end MathlibAnalytic
end MGAP4D
