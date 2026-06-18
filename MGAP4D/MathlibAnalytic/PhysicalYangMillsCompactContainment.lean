import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeEmbedding
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Tight

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- A quantitative compact-containment certificate for a family of measures.

The compact sets may vary with `n`; their common tail bounds tend to zero.
This is exactly the analytic input required to prove uniform tightness. -/
structure UniformCompactContainmentCertificate
    (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    (S : Set (Measure X)) where
  compactSet : ℕ → Set X
  tailBound : ℕ → ENNReal
  compact_compactSet : ∀ n, IsCompact (compactSet n)
  tailBound_tendsto_zero : Tendsto tailBound atTop (nhds 0)
  measure_compl_le : ∀ n μ, μ ∈ S → μ (compactSet n)ᶜ ≤ tailBound n

namespace UniformCompactContainmentCertificate

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable {S : Set (Measure X)}

/-- Compact containment with a tail bound tending to zero implies tightness. -/
theorem isTight
    (C : UniformCompactContainmentCertificate X S) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hEventually : ∀ᶠ n in atTop, C.tailBound n < ε :=
    (tendsto_order.1 C.tailBound_tendsto_zero).2 ε hε
  obtain ⟨n, hn⟩ := hEventually.exists
  exact ⟨C.compactSet n, C.compact_compactSet n, fun μ hμ =>
    (C.measure_compl_le n μ hμ).trans hn.le⟩

end UniformCompactContainmentCertificate

/-- A coercive `ℝ≥0∞`-valued functional whose compact sublevel sets and uniform
first-moment estimate produce compact containment by Markov's inequality.

The final field isolates the elementary asymptotic calculation that the Markov
tail `momentBound / radius n` tends to zero. In concrete Sobolev/Besov
applications this follows by choosing radii tending to infinity. -/
structure UniformCoerciveMomentCertificate
    (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    (S : Set (Measure X)) where
  functional : X → ENNReal
  functional_measurable : Measurable functional
  radius : ℕ → ENNReal
  radius_ne_zero : ∀ n, radius n ≠ 0
  radius_ne_top : ∀ n, radius n ≠ ⊤
  compact_sublevel : ∀ n, IsCompact {x | functional x ≤ radius n}
  momentBound : ENNReal
  uniform_lintegral_le :
    ∀ μ ∈ S, ∫⁻ x, functional x ∂μ ≤ momentBound
  markovTail_tendsto_zero :
    Tendsto (fun n => momentBound / radius n) atTop (nhds 0)

namespace UniformCoerciveMomentCertificate

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable {S : Set (Measure X)}

/-- Markov's inequality controls the complement of every compact sublevel set. -/
theorem measure_compl_sublevel_le
    (C : UniformCoerciveMomentCertificate X S)
    (n : ℕ) (μ : Measure X) (hμ : μ ∈ S) :
    μ ({x | C.functional x ≤ C.radius n})ᶜ ≤
      C.momentBound / C.radius n := by
  calc
    μ ({x | C.functional x ≤ C.radius n})ᶜ ≤
        μ {x | C.radius n ≤ C.functional x} := by
      apply measure_mono
      intro x hx
      have hx' : ¬ C.functional x ≤ C.radius n := by
        simpa only [Set.mem_compl_iff, Set.mem_setOf_eq] using hx
      exact (lt_of_not_ge hx').le
    _ ≤ (∫⁻ x, C.functional x ∂μ) / C.radius n :=
      MeasureTheory.meas_ge_le_lintegral_div
        C.functional_measurable.aemeasurable
        (C.radius_ne_zero n) (C.radius_ne_top n)
    _ ≤ C.momentBound / C.radius n :=
      ENNReal.div_le_div_right (C.uniform_lintegral_le μ hμ) (C.radius n)

/-- Convert a coercive moment estimate into the compact-containment certificate
consumed by the generic tightness theorem. -/
def toCompactContainmentCertificate
    (C : UniformCoerciveMomentCertificate X S) :
    UniformCompactContainmentCertificate X S :=
  { compactSet := fun n => {x | C.functional x ≤ C.radius n}
    tailBound := fun n => C.momentBound / C.radius n
    compact_compactSet := C.compact_sublevel
    tailBound_tendsto_zero := C.markovTail_tendsto_zero
    measure_compl_le := fun n μ hμ => C.measure_compl_sublevel_le n μ hμ }

/-- Uniform coercive moments with compact sublevels imply tightness. -/
theorem isTight
    (C : UniformCoerciveMomentCertificate X S) :
    IsTightMeasureSet S :=
  C.toCompactContainmentCertificate.isTight

end UniformCoerciveMomentCertificate

/-- The exact family of pushed-forward lattice probability measures viewed as
ordinary measures on the fixed physical configuration space. -/
def PhysicalFourDimensionalYangMillsLatticeEmbedding.embeddedMeasureSet
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) :
    Set (Measure E.PhysicalConfiguration) :=
  {((μ : ProbabilityMeasure E.PhysicalConfiguration) :
      Measure E.PhysicalConfiguration) |
    μ ∈ Set.range E.embeddedMeasure}

/-- Compact-containment data specialized to the physical embedded lattice laws. -/
abbrev PhysicalFourDimensionalYangMillsLatticeEmbedding.CompactContainmentCertificate
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) :=
  UniformCompactContainmentCertificate E.PhysicalConfiguration E.embeddedMeasureSet

/-- Coercive moment data specialized to the physical embedded lattice laws. -/
abbrev PhysicalFourDimensionalYangMillsLatticeEmbedding.CoerciveMomentCertificate
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) :=
  UniformCoerciveMomentCertificate E.PhysicalConfiguration E.embeddedMeasureSet

end

end MathlibAnalytic
end MGAP4D
