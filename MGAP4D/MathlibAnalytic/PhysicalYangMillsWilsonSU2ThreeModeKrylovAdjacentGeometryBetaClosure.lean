import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCouplingBetaMajorant
import Mathlib.Tactic

/-!
# Close the SU(2) coupling lane by explicit beta increments

PR #5108 reduced the fixed-time strong-limit problem to two summable pieces:

* the vector-wise cross-volume geometry residual
  `g_{n,r,k}`;
* the same-volume coupling residual `c_n`.

PR #5115 bounds `c_n` by the explicit weighted beta increment

  C_norm(H_{n+1}, beta_n, beta_{n+1}) * ||beta_{n+1} - beta_n||.

This file removes `c_n` from the model-facing input entirely.  It is enough
to supply

  Summable (fun n => g_{n,r,k})

for every fixed Krylov depth and mode, together with summability of the explicit
weighted beta increments.  The existing #5108 geometry-plus-coupling package is
then theorem-generated, hence so are all fixed-natural-time strong limits and
the existing q0^m continuum decay.

A geometric sufficient condition for the weighted beta increments is also
packaged here.  After this reduction the only non-scalar H1-C3 input is the
orbit-wise cross-volume geometry/refinement residual.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentGeometryBetaClosureTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentGeometryBetaClosureCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentGeometryBetaClosureSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentGeometryBetaClosureMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentGeometryBetaClosureBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentGeometryBetaClosureSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentGeometryBetaClosureSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentGeometryBetaClosureNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section GeometryBetaClosure

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

/-- Final separated H1-C3 input after eliminating the actual coupling residual:
summable vector-wise geometry plus summable explicit weighted beta increments. -/
structure PhysicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput where
  orbitGeometry_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
            Q R n r k)
  betaMajorant_summable :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCouplingBetaMajorant halfExtent beta n)

namespace PhysicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput
        (Q := Q) (R := R))

include G

/-- Convert the explicit-beta input into the exact #5108
geometry-plus-coupling summability package. -/
noncomputable def toGeometryCouplingSummableInput :
    PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput
      (Q := Q) (R := R) where
  orbitGeometry_summable := G.orbitGeometry_summable
  coupling_summable :=
    physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_summable_of_betaMajorant
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      G.betaMajorant_summable

/-- Geometry summability plus explicit beta-increment summability implies every
fixed Krylov-orbit mismatch is summable. -/
theorem orbitMismatch_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput.orbitMismatch_summable
      Q R (toGeometryCouplingSummableInput Q R G) r k

/-- Produce the exact #5106 orbit-summability package directly from geometry
and explicit beta increments. -/
noncomputable def toOrbitMismatchSummableInput :
    PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput
      (Q := Q) (R := R) :=
  PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput.toOrbitMismatchSummableInput
    Q R (toGeometryCouplingSummableInput Q R G)

/-- The coupling residual no longer appears as an external hypothesis:
geometry summability plus explicit beta-increment summability gives all
fixed-natural-time evolved strong limits. -/
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
    PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L (toGeometryCouplingSummableInput Q R G) hInvariant C

/-- The same explicit-beta reduction retains the already proved uniform q0^m
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
    PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L (toGeometryCouplingSummableInput Q R G) hInvariant C s hs hcut

end PhysicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput

/-- A geometric majorant for the explicit weighted beta increments is a direct
constructor for the final separated H1-C3 input. -/
noncomputable def
    physicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput_of_geometricBetaMajorant
    (hGeometry :
      ∀ (r : ℕ) (k : Fin 3),
        Summable
          (fun n =>
            physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
              Q R n r k))
    (Cbeta qbeta : ℝ)
    (hq_nonneg : 0 ≤ qbeta)
    (hq_lt_one : qbeta < 1)
    (hBetaGeometric :
      ∀ n : ℕ,
        physicalYangMillsSU2AdjacentCouplingBetaMajorant halfExtent beta n ≤
          Cbeta * qbeta ^ n) :
    PhysicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput
      (Q := Q) (R := R) := by
  refine
    { orbitGeometry_summable := hGeometry
      betaMajorant_summable := ?_ }
  have hGeomSummable : Summable (fun n : ℕ => Cbeta * qbeta ^ n) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left Cbeta
  exact
    Summable.of_nonneg_of_le
      (fun n =>
        physicalYangMillsSU2AdjacentCouplingBetaMajorant_nonneg
          halfExtent beta n)
      hBetaGeometric
      hGeomSummable

end GeometryBetaClosure

end

end MathlibAnalytic
end MGAP4D
