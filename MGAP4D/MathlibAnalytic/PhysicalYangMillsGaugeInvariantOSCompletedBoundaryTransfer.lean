import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance completedBoundaryTransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedBoundaryTransferSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedBoundaryTransferSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedBoundaryTransferSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedBoundaryTransferSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedBoundaryTransferSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The already-completed finite Wilson OS transfer operator agrees with
carrier translation on every represented physical state, not only on the
positive-time-subalgebra presentation used by the public semigroup API. -/
theorem finiteOperator_on_carrierPhysicalState
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    C.finiteOperator n t
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState F) =
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation t F) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  change Tn.toPhysicalSemigroup.operator t (Pn.physicalState F) =
    Pn.physicalState (Tn.carrierTranslation t F)
  exact Tn.toCarrierSemigroup.physicalOperator_on_physicalState t F

/-- Canonical boundary-Hilbert transfer at physical time `t`.

The complete OS transfer `T_n(t/2)` is conjugated through the isometric
boundary realization `Ĵ_n`.  Since `Ĵ_n` need not be onto all of boundary
`L²`, the inverse is preceded by orthogonal projection to its closed range:

`K_{n,t} = Ĵ_n ∘ T_n(t/2) ∘ Ĵ_n⁻¹ ∘ P_{ran Ĵ_n}`.

This is a genuine continuous linear map on the whole boundary Haar `L²` and
requires no new physical, decay, or coercivity hypothesis. -/
noncomputable def completedBoundaryTransfer
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  realLinearIsometryProjectedCompression
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
    (C.finiteOperator n (t / 2))

/-- On the physical OS Hilbert range, the completed boundary transfer is
exactly conjugation of the completed OS semigroup. -/
@[simp] theorem completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) :
    Q.completedBoundaryTransfer hInvariant C n t
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi) =
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (C.finiteOperator n (t / 2) psi) := by
  exact realLinearIsometryProjectedCompression_apply_map
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
    (C.finiteOperator n (t / 2)) psi

/-- The global boundary transfer is contractive because orthogonal projection,
`Ĵ_n`, and `Ĵ_n⁻¹` are contractive/isometric and the physical OS transfer is
a contraction. -/
theorem completedBoundaryTransfer_opNorm_le_one
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) :
    ‖Q.completedBoundaryTransfer hInvariant C n t‖ ≤ 1 := by
  calc
    ‖Q.completedBoundaryTransfer hInvariant C n t‖ ≤
        ‖C.finiteOperator n (t / 2)‖ :=
      realLinearIsometryProjectedCompression_opNorm_le
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
        (C.finiteOperator n (t / 2))
    _ ≤ 1 := C.finiteOperator_opNorm_le n (t / 2)

/-- On every dense canonical boundary moment, the completed boundary operator
is exactly half-time observable translation.  This is the Hilbert-level form
of the carrier intertwining proved before completion. -/
theorem completedBoundaryTransfer_apply_canonicalBoundaryMoment
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.completedBoundaryTransfer hInvariant C n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2) F) := by
  calc
    Q.completedBoundaryTransfer hInvariant C n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) =
      Q.completedBoundaryTransfer hInvariant C n t
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState F)) := by
      rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
    _ = Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (C.finiteOperator n (t / 2)
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState F)) := by
      rw [Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment]
    _ = Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
          ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
            (t / 2) F)) := by
      rw [Q.finiteOperator_on_carrierPhysicalState]
    _ = physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2) F) := by
      rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]

/-- The completed boundary operator has the actual adjoint-synthesis
factorization on every dense canonical boundary moment:

`K_{n,t} m_F = A_φ† U_{n,t} F`.

Thus completion itself introduces no factorization defect.  What remains for a
full factorized certificate is a bounded global lift of the dense analysis
`m_F ↦ U_{n,t} F` from boundary `L²` into open-half `L²`. -/
theorem completedBoundaryTransfer_apply_canonicalBoundaryMoment_eq_actualSynthesis
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.completedBoundaryTransfer hInvariant C n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) =
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
        (Q.translatedPositiveHalfL2LinearMap hInvariant C n t F) := by
  rw [Q.completedBoundaryTransfer_apply_canonicalBoundaryMoment]
  symm
  simpa only [Q.boundaryMomentLinearIsometry_apply] using
    Q.actualSynthesis_translatedPositiveHalfL2LinearMap_apply
      hInvariant C n t F

/-- In particular, the exact completed boundary intertwining required by the
vacuum-centered gap route is already theorem-generated; no additional
intertwining field is needed at Hilbert level. -/
theorem completedBoundaryTransfer_vacuumCentered_intertwining
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.completedBoundaryTransfer hInvariant C n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F)) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2)
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F)) := by
  exact Q.completedBoundaryTransfer_apply_canonicalBoundaryMoment
    hInvariant C n t
    ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D

end
