import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovSummableAdjacentDefect
import Mathlib.Tactic

/-!
# Geometric majorants for adjacent SU(2) Krylov refinement defects

PR #5098 reduces H1-C3 strong-limit existence to summability of the consecutive
finite union-marginal Krylov defects.

For applications, summability should itself be theorem-generated from a
quantitative one-step refinement estimate.  This file isolates the standard
geometric form:

  d_n^{m,k} <= C_{m,k} q_{m,k}^n,
  0 <= C_{m,k},
  0 <= q_{m,k} < 1.

The geometric majorant is summable, and the finite defect is nonnegative
because it is a norm.  Mathlib's comparison theorem Summable.of_nonneg_of_le
therefore yields the adjacent-defect summability required by #5098.

Thus the model-facing H1-C3 existence frontier is sharpened to proving a
geometric one-step refinement estimate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2KrylovGeometricAdjacentTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovGeometricAdjacentCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovGeometricAdjacentSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovGeometricAdjacentMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovGeometricAdjacentBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovGeometricAdjacentSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovGeometricAdjacentSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2KrylovGeometricAdjacentNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section KrylovGeometricAdjacent

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

theorem physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_nonneg
    (n m : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
        (Q := Q) (R := R) n m k := by
  unfold physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
  unfold physicalYangMillsSU2ThreeModeFiniteCommonMarginalKrylovDefect
  exact norm_nonneg _

/-- Quantitative one-step refinement input with a geometric scale majorant. -/
structure PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovGeometricInput where
  prefactor : ℕ → Fin 3 → ℝ
  ratio : ℕ → Fin 3 → ℝ
  prefactor_nonneg :
    ∀ (m : ℕ) (k : Fin 3), 0 ≤ prefactor m k
  ratio_nonneg :
    ∀ (m : ℕ) (k : Fin 3), 0 ≤ ratio m k
  ratio_lt_one :
    ∀ (m : ℕ) (k : Fin 3), ratio m k < 1
  defect_le_geometric :
    ∀ (n m : ℕ) (k : Fin 3),
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n m k ≤
        prefactor m k * (ratio m k) ^ n

namespace PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovGeometricInput

variable
    (G :
      PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovGeometricInput
        (Q := Q) (R := R))

include G

/-- The geometric majorant is summable for every fixed natural time and
first-three basis mode. -/
theorem majorant_summable
    (m : ℕ) (k : Fin 3) :
    Summable
      (fun n : ℕ =>
        G.prefactor m k * (G.ratio m k) ^ n) := by
  exact
    (summable_geometric_of_lt_one
      (G.ratio_nonneg m k)
      (G.ratio_lt_one m k)).mul_left
        (G.prefactor m k)

/-- The adjacent finite Krylov defects are summable by geometric comparison. -/
theorem adjacentDefect_summable
    (m : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n m k) := by
  refine Summable.of_nonneg_of_le
    (fun n =>
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_nonneg
        Q R n m k)
    (fun n => G.defect_le_geometric n m k)
    (majorant_summable Q R G m k)

/-- Geometric refinement data theorem-generate the #5098 adjacent-summability
package. -/
noncomputable def toFiniteAdjacentKrylovSummableInput :
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput
      (Q := Q) (R := R) where
  adjacentDefect_summable :=
    adjacentDefect_summable Q R G

/-- Geometric one-step refinement control theorem-generates all fixed-time
strong limits of the exact theorem-generated excitation. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
            (fun j =>
              physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                Q R L hInvariant (phi j) m)
            atTop
            (𝓝
              (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L (toFiniteAdjacentKrylovSummableInput Q R G))
                m cInf)) := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (toFiniteAdjacentKrylovSummableInput Q R G)
      hInvariant

/-- The same geometric refinement control retains the scale-uniform q0^m
decay after passage to continuum. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝
                (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                  Q R L
                  (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                    Q R L (toFiniteAdjacentKrylovSummableInput Q R G))
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L (toFiniteAdjacentKrylovSummableInput Q R G))
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (toFiniteAdjacentKrylovSummableInput Q R G)
      hInvariant s hs hcut

end PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovGeometricInput

end KrylovGeometricAdjacent

end

end MathlibAnalytic
end MGAP4D
