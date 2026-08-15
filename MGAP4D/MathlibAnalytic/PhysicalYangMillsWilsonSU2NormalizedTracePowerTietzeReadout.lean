import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization
import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerTietzeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerTietzeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerTietzeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerTietzeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerTietzeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerTietzeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerTietzeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerTietzeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev normalizedTracePowerTietzeFullConfiguration
    (halfExtent : ℕ → ℕ) (n : ℕ) :=
  PeriodicHypercubicEvenEdge (halfExtent n) →
    Matrix.specialUnitaryGroup (Fin 2) ℂ

private abbrev normalizedTracePowerTietzeOpenConfiguration
    (halfExtent : ℕ → ℕ) (n : ℕ) :=
  PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
    (halfExtent n) 2

private abbrev normalizedTracePowerTietzeOpenTarget
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n j : ℕ) :=
  periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
    (halfExtent n) (beta n) (hbeta n) j

/-- Restriction from a full finite Wilson configuration to its positive open
half is a canonical continuous map for the product topologies. -/
noncomputable def normalizedTracePowerTietzePositiveRestrictionContinuousMap
    (halfExtent : ℕ → ℕ) (n : ℕ) :
    C(normalizedTracePowerTietzeFullConfiguration halfExtent n,
      normalizedTracePowerTietzeOpenConfiguration halfExtent n) :=
  ⟨(periodicHypercubicEvenEdgeOrbitPartition
      (halfExtent n)).positiveRestriction,
    by fun_prop⟩

/-- The finite normalized-trace-power cylinder viewed directly on the full
finite Wilson configuration. -/
noncomputable def normalizedTracePowerTietzeFullTarget
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n j : ℕ) :
    BoundedContinuousFunction
      (normalizedTracePowerTietzeFullConfiguration halfExtent n) ℝ :=
  (normalizedTracePowerTietzeOpenTarget halfExtent beta hbeta n j).compContinuous
    (normalizedTracePowerTietzePositiveRestrictionContinuousMap halfExtent n)

@[simp] theorem normalizedTracePowerTietzeFullTarget_apply
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n j : ℕ)
    (A : normalizedTracePowerTietzeFullConfiguration halfExtent n) :
    normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A =
      normalizedTracePowerTietzeOpenTarget halfExtent beta hbeta n j
        ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A) :=
  rfl

/-- Tietze turns a closed finite-Wilson embedding into a genuine bounded
continuous scalar observable on the physical carrier with exact same-root
readout and no global continuum-to-link coordinate map.

Gauge invariance and positive-time membership are intentionally not asserted by
this topological theorem: an arbitrary Tietze extension need not preserve the
physical gauge action. -/
theorem exists_normalizedTracePower_physicalExtension_of_isClosedEmbedding
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerTietzeTwoRankPositive beta hbeta)
    (n j : ℕ)
    (he : IsClosedEmbedding (Q.interpolate n)) :
    ∃ O : BoundedContinuousFunction S.Configuration ℝ,
      ‖O‖ = ‖normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j‖ ∧
      ∀ A : normalizedTracePowerTietzeFullConfiguration halfExtent n,
        O (Q.interpolate n A) =
          normalizedTracePowerTietzeOpenTarget halfExtent beta hbeta n j
            ((periodicHypercubicEvenEdgeOrbitPartition
              (halfExtent n)).positiveRestriction A) := by
  rcases
      (normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j).
        exists_extension_norm_eq_of_isClosedEmbedding he with
    ⟨O, hnorm, hreadout⟩
  refine ⟨O, hnorm, ?_⟩
  intro A
  have hA := congrFun hreadout A
  simpa using hA

/-- For the actual finite Wilson source, continuity and injectivity of the
interpolation already imply the closed-embedding hypothesis needed by Tietze:
the source is compact and the physical Polish carrier is Hausdorff. -/
theorem exists_normalizedTracePower_physicalExtension_of_continuous_injective
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerTietzeTwoRankPositive beta hbeta)
    (n j : ℕ)
    (hcontinuous : Continuous (Q.interpolate n))
    (hinjective : Function.Injective (Q.interpolate n)) :
    ∃ O : BoundedContinuousFunction S.Configuration ℝ,
      ‖O‖ = ‖normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j‖ ∧
      ∀ A : normalizedTracePowerTietzeFullConfiguration halfExtent n,
        O (Q.interpolate n A) =
          normalizedTracePowerTietzeOpenTarget halfExtent beta hbeta n j
            ((periodicHypercubicEvenEdgeOrbitPartition
              (halfExtent n)).positiveRestriction A) := by
  exact exists_normalizedTracePower_physicalExtension_of_isClosedEmbedding
    Q n j (hcontinuous.isClosedEmbedding hinjective)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
