import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitMismatch
import Mathlib.Tactic

/-!
# Geometric control of the finite SU(2) Krylov orbit mismatch

PR #5106 reduces fixed-natural-time strong-limit existence to summability, in
the refinement scale n, of the vector-wise quantities

  ||(A_n^L - A_n^R) ((A_n^R)^r v_{n,k}^R)||

for each fixed orbit depth r and mode k.

This file packages the directly quantitative version of that weaker frontier.
For every fixed r,k it is enough to have constants C_{r,k} >= 0 and
0 <= q_{r,k} < 1 with

  orbitMismatch(n,r,k) <= C_{r,k} q_{r,k}^n.

Geometric-series summability then produces the #5106 orbit-summability package,
hence all fixed-natural-time strong limits and the existing q0^m continuum
decay.

This is strictly weaker than requiring geometric decay of the whole-space
operator norm ||A_n^L - A_n^R||.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentOrbitGeometricTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentOrbitGeometricCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentOrbitGeometricSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentOrbitGeometricMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentOrbitGeometricBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentOrbitGeometricSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentOrbitGeometricSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentOrbitGeometricNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section AdjacentKrylovOrbitGeometric

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

/-- Geometric scale control of each fixed finite-Krylov-orbit mismatch. -/
structure PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchGeometricInput where
  prefactor : ℕ → Fin 3 → ℝ
  ratio : ℕ → Fin 3 → ℝ
  prefactor_nonneg : ∀ r k, 0 ≤ prefactor r k
  ratio_nonneg : ∀ r k, 0 ≤ ratio r k
  ratio_lt_one : ∀ r k, ratio r k < 1
  orbitMismatch_le_geometric :
    ∀ (n r : ℕ) (k : Fin 3),
      physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k ≤
        prefactor r k * (ratio r k) ^ n

namespace PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchGeometricInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchGeometricInput
        (Q := Q) (R := R))

include G

/-- The geometric majorant for each fixed orbit depth and mode is summable. -/
theorem majorant_summable
    (r : ℕ) (k : Fin 3) :
    Summable (fun n : ℕ => G.prefactor r k * (G.ratio r k) ^ n) := by
  exact
    (summable_geometric_of_lt_one
      (G.ratio_nonneg r k) (G.ratio_lt_one r k)).mul_left
      (G.prefactor r k)

/-- Geometric orbit mismatch implies scale summability for every fixed r,k. -/
theorem orbitMismatch_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  refine Summable.of_nonneg_of_le
    (fun n => ?_)
    (fun n => G.orbitMismatch_le_geometric n r k)
    (majorant_summable Q R G r k)
  unfold physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
  exact norm_nonneg _

/-- Geometric orbit control produces the #5106 orbit-summability package. -/
noncomputable def toOrbitMismatchSummableInput :
    PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput
      (Q := Q) (R := R) where
  orbitMismatch_summable := orbitMismatch_summable Q R G

/-- Geometric vector-wise orbit mismatch control gives all fixed-natural-time
strong limits of the theorem-generated norm-one excitation. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
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
                  Q R L
                  (PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                    Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C))
                m cInf)) := by
  exact
    PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C

/-- The same geometric orbit-wise hypothesis preserves the uniform q0^m
continuum decay. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
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
                    Q R L
                    (PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                      Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C))
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L
                  (PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                    Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C))
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C s hs hcut

end PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchGeometricInput

end AdjacentKrylovOrbitGeometric

end

end MathlibAnalytic
end MGAP4D
