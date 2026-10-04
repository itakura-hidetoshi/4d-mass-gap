import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionRightSelectedConditionalTransport
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryHaarProjectiveCylinderOrthonormal
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePair
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression
import Mathlib.Tactic

/-!
# Transport boundary-Haar conditional candidates into the adjacent SU(2) receiver

PR #5130 moves the raw conditional residual from the adjacent common marginal
to the fine selected projective marginal at scale n+1.

The selected pair embedding already factors canonically as

  pair Haar L²
    -> boundary Haar L²
    -> selected interacting projective marginal L².

This file uses the second isometry to move the raw residual one layer earlier.
An arbitrary bounded operator on boundary Haar L² is transported to the
selected marginal by projected compression.  On the actual frozen Krylov
vector the residual norm is preserved exactly.

Thus the raw model-facing tail can now be proved entirely on the finite
boundary-Haar carrier.  The only term left on the adjacent common marginal is
the physicality defect of the fully transported candidate.

No surjectivity of the boundary/projective readout, no exact identification
with the ground-state joint carrier, and no H1-D5-style descent is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentBoundaryHaarTransportTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentBoundaryHaarTransportCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentBoundaryHaarTransportSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentBoundaryHaarTransportMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentBoundaryHaarTransportBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentBoundaryHaarTransportSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentBoundaryHaarTransportSpatialHaarSFinite (H : ℕ) :
    SFinite
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentBoundaryHaarTransportNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section BoundaryHaarConditionalTransport

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

/-- Boundary-Haar representative of the actual fine frozen Krylov output. -/
noncomputable def physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
    (n r : ℕ) (k : Fin 3) :
    PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 :=
  periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent (n + 1)) 2
    (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)

/-- The fine selected projective representative is exactly the
boundary-Haar/projective isometric image of the corresponding boundary-Haar
vector. -/
@[simp] theorem
    physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector_eq_boundaryHaarProjective
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector Q R n r k =
      R.boundaryHaarProjectiveL2Isometry (n + 1)
        (physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k) := by
  rfl

/-- Transport a bounded boundary-Haar operator to the fine selected projective
marginal by canonical projected compression. -/
noncomputable def physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate
    (n : ℕ)
    (candidate :
      PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2) :
    Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) →L[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) :=
  realLinearIsometryProjectedCompression
    (R.boundaryHaarProjectiveL2Isometry (n + 1))
    candidate

/-- Exact action of the transported boundary-Haar candidate on the image of
the boundary-Haar/projective isometry. -/
@[simp] theorem
    physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate_apply_embedding
    (n : ℕ)
    (candidate :
      PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2)
    (x : PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2) :
    physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate
        Q R n candidate
        (R.boundaryHaarProjectiveL2Isometry (n + 1) x) =
      R.boundaryHaarProjectiveL2Isometry (n + 1) (candidate x) := by
  unfold physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate
  exact
    realLinearIsometryProjectedCompression_apply_map
      (R.boundaryHaarProjectiveL2Isometry (n + 1))
      candidate x

/-- The selected-marginal raw residual of a transported boundary-Haar
candidate is exactly its boundary-Haar residual on the actual frozen vector. -/
theorem
    physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidateResidual_norm_eq
    (n r : ℕ) (k : Fin 3)
    (candidate :
      PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2) :
    ‖physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector Q R n r k -
        physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate
          Q R n candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector
            Q R n r k)‖ =
      ‖physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k -
        candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)‖ := by
  let J := R.boundaryHaarProjectiveL2Isometry (n + 1)
  let x :=
    physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  rw [
    physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector_eq_boundaryHaarProjective
      Q R n r k,
    physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate_apply_embedding
      Q R n candidate x]
  change ‖J x - J (candidate x)‖ = ‖x - candidate x‖
  rw [← J.map_sub, J.norm_map]

/-- Squared residual form consumed by the geometric tail package. -/
theorem
    physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidateResidual_sq_eq
    (n r : ℕ) (k : Fin 3)
    (candidate :
      PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2) :
    ‖physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector Q R n r k -
        physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate
          Q R n candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector
            Q R n r k)‖ ^ 2 =
      ‖physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k -
        candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)‖ ^ 2 := by
  rw [
    physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidateResidual_norm_eq
      Q R n r k candidate]

/-- Fully transported boundary-Haar candidate on the adjacent common marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonBoundaryHaarCandidate
    (n : ℕ)
    (candidate :
      PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) →L[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  physicalYangMillsSU2AdjacentCommonRightSelectedCandidate
    Q R n
    (physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate
      Q R n candidate)

/-- Model-facing receiver with the raw conditional tail entirely on boundary
Haar L².

The physicality term remains on the common marginal because it is precisely the
cross-scale comparison with the coarse completed physical pair carrier. -/
structure PhysicalYangMillsSU2AdjacentBoundaryHaarConditionalPhysicalityTailInput where
  candidate :
    (n : ℕ) →
      PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2 →L[ℝ]
        PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent (n + 1)) 2
  splitResidual_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Craw Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Craw ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          ‖physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k -
              candidate n
                (physicalYangMillsSU2AdjacentFineFrozenStepBoundaryHaarVector
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)‖ ^ 2 ≤
            Craw * (rho ^ distance n / (1 - rho))) ∧
        ∀ n,
          let Cn :=
            physicalYangMillsSU2AdjacentCommonBoundaryHaarCandidate
              Q R n (candidate n)
          let Y :=
            physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
              Q R n r k
          ‖Cn Y -
              physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
                Q R n (Cn Y)‖ ^ 2 ≤
            Cphys * (rho ^ distance n / (1 - rho))

namespace PhysicalYangMillsSU2AdjacentBoundaryHaarConditionalPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentBoundaryHaarConditionalPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- Transport the boundary-Haar tail package to the fine-selected package from
#5130.  Exact isometry preserves the raw tail without changing its constant. -/
noncomputable def toRightSelectedConditionalPhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentRightSelectedConditionalPhysicalityTailInput
      (Q := Q) (R := R) where
  candidate := fun n =>
    physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidate
      Q R n (G.candidate n)
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
        physicalYangMillsSU2AdjacentFineSelectedBoundaryHaarCandidateResidual_sq_eq
          Q R n r k (G.candidate n)]
      exact hRaw n
    · intro n
      simpa only [
        physicalYangMillsSU2AdjacentCommonBoundaryHaarCandidate
      ] using hPhys n

/-- Boundary-Haar raw tails plus common physicality tails generate the single
#5123 reconstruction-variance tail. -/
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
    PhysicalYangMillsSU2AdjacentRightSelectedConditionalPhysicalityTailInput.totalVariance_tail
      Q R
      (toRightSelectedConditionalPhysicalityTailInput Q R G)
      r k

/-- Final receiver after removing projective selected-marginal geometry from
the raw conditional residual. -/
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
    PhysicalYangMillsSU2AdjacentRightSelectedConditionalPhysicalityTailInput.orbitMismatch_summable
      Q R
      (toRightSelectedConditionalPhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentBoundaryHaarConditionalPhysicalityTailInput

end BoundaryHaarConditionalTransport

end

end MathlibAnalytic
end MGAP4D
