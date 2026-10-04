import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionBoundaryHaarConditionalTransport
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression
import Mathlib.Tactic

/-!
# Move the SU(2) raw conditional tail to the ordered pair-Haar carrier

PR #5131 moves the raw residual to boundary Haar L².  The boundary Haar carrier
is already canonically isometric to the ordered spatial-slice pair-Haar L²
carrier.  The actual frozen Krylov vector is defined on that pair-Haar carrier.

This file transports an arbitrary bounded pair-Haar candidate through the
existing pair-Haar-to-boundary isometry and proves exact preservation of the
raw residual.  Therefore the raw model-facing estimate is reduced all the way
to the underlying finite pair-Haar L² space.

This is the natural carrier for the next weighted-measure step: the genuine
ground-state joint law is a positive density with respect to the same pair-Haar
measure.  No equality of the corresponding L² norms is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentPairHaarTransportTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentPairHaarTransportCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentPairHaarTransportSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentPairHaarTransportMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentPairHaarTransportBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentPairHaarTransportSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentPairHaarTransportSpatialHaarSFinite (H : ℕ) :
    SFinite
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentPairHaarTransportNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section PairHaarConditionalTransport

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

/-- Transport a bounded pair-Haar operator to boundary Haar L². -/
noncomputable def physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate
    (n : ℕ)
    (candidate :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2) :
    PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 :=
  realLinearIsometryProjectedCompression
    (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent (n + 1)) 2)
    candidate

/-- Exact conjugation on the pair-Haar image. -/
@[simp] theorem
    physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate_apply_embedding
    (n : ℕ)
    (candidate :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2) :
    physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate (halfExtent := halfExtent) n candidate
        (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
          (halfExtent (n + 1)) 2 x) =
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent (n + 1)) 2 (candidate x) := by
  unfold physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate
  exact
    realLinearIsometryProjectedCompression_apply_map
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent (n + 1)) 2)
      candidate x

/-- Boundary-Haar frozen vector is exactly the image of the original finite
pair-Haar frozen Krylov vector. -/
@[simp] theorem physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector_eq_pairEmbedding
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k =
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent (n + 1)) 2
        (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) := by
  rfl

/-- Raw residual is preserved exactly when a pair-Haar candidate is transported
to boundary Haar L². -/
theorem
    physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidateResidual_norm_eq
    (n r : ℕ) (k : Fin 3)
    (candidate :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2) :
    ‖physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k -
        physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate (halfExtent := halfExtent) n candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)‖ =
      ‖physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k -
        candidate
          (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)‖ := by
  let J :=
    periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent (n + 1)) 2
  let x :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  rw [
    physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector_eq_pairEmbedding (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k,
    physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate_apply_embedding (halfExtent := halfExtent) n candidate x]
  change ‖J x - J (candidate x)‖ = ‖x - candidate x‖
  rw [← J.map_sub, J.norm_map]

/-- Squared residual form. -/
theorem
    physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidateResidual_sq_eq
    (n r : ℕ) (k : Fin 3)
    (candidate :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2) :
    ‖physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k -
        physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate (halfExtent := halfExtent) n candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)‖ ^ 2 =
      ‖physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k -
        candidate
          (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)‖ ^ 2 := by
  rw [
    physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidateResidual_norm_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k candidate]

/-- Fully transport a pair-Haar candidate through boundary, selected-projective,
and adjacent-common carriers. -/
noncomputable def physicalYangMillsSU2AdjacentCommonPairHaarCandidate
    (n : ℕ)
    (candidate :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) →L[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  physicalYangMillsSU2AdjacentCommonBoundaryHaarCandidate
    Q R n
    (physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate (halfExtent := halfExtent) n candidate)

/-- Final raw-tail receiver on ordered pair-Haar L². -/
structure PhysicalYangMillsSU2AdjacentPairHaarConditionalPhysicalityTailInput where
  candidate :
    (n : ℕ) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent (n + 1)) 2
  splitResidual_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Craw Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Craw ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          ‖physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r k -
              candidate n
                (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                  n r k)‖ ^ 2 ≤
            Craw * (rho ^ distance n / (1 - rho))) ∧
        ∀ n,
          let Cn :=
            physicalYangMillsSU2AdjacentCommonPairHaarCandidate
              Q R n (candidate n)
          let Y :=
            physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
              Q R n r k
          ‖Cn Y -
              physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
                Q R n (Cn Y)‖ ^ 2 ≤
            Cphys * (rho ^ distance n / (1 - rho))

namespace PhysicalYangMillsSU2AdjacentPairHaarConditionalPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentPairHaarConditionalPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- Exact pair-Haar-to-boundary transport gives the #5131 boundary-Haar
receiver with unchanged raw tail constants. -/
noncomputable def toBoundaryHaarConditionalPhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentBoundaryHaarConditionalPhysicalityTailInput
      (Q := Q) (R := R) where
  candidate := fun n =>
    physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidate (halfExtent := halfExtent) n (G.candidate n)
  splitResidual_tail := by
    intro r k
    rcases G.splitResidual_tail r k with
      ⟨Craw, Cphys, rho, distance,
        hCraw, hCphys, hrho0, hrho1, hDistance, hRaw, hPhys⟩
    refine
      ⟨Craw, Cphys, rho, distance,
        hCraw, hCphys, hrho0, hrho1, hDistance, ?_, ?_⟩
    · intro n
      rw [
        physicalYangMillsSU2AdjacentFineBoundaryPairHaarCandidateResidual_sq_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k (G.candidate n)]
      exact hRaw n
    · intro n
      simpa only [
        physicalYangMillsSU2AdjacentCommonPairHaarCandidate
      ] using hPhys n

theorem totalVariance_tail
    (r : ℕ) (k : Fin 3) :
    ∃ (C rho : ℝ) (distance : ℕ → ℕ),
      0 ≤ C ∧
      0 ≤ rho ∧
      rho < 1 ∧
      (∀ n, n ≤ distance n) ∧
      ∀ n,
        physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
            Q R n r k ≤
          C * (rho ^ distance n / (1 - rho)) := by
  exact
    PhysicalYangMillsSU2AdjacentBoundaryHaarConditionalPhysicalityTailInput.totalVariance_tail
      Q R
      (toBoundaryHaarConditionalPhysicalityTailInput Q R G)
      r k

theorem orbitMismatch_summable
    (physicalCommutation_geometric :
      ∀ (r : ℕ) (k : Fin 3),
        ∃ C q : ℝ,
          0 ≤ q ∧ q < 1 ∧
            ∀ n : ℕ,
              physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
                  Q R n r k ≤
                C * q ^ n)
    (betaMajorant_geometric :
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentCouplingBetaMajorant
                halfExtent beta n ≤
              C * q ^ n)
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentBoundaryHaarConditionalPhysicalityTailInput.orbitMismatch_summable
      Q R
      (toBoundaryHaarConditionalPhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentPairHaarConditionalPhysicalityTailInput

end PairHaarConditionalTransport

end

end MathlibAnalytic
end MGAP4D
