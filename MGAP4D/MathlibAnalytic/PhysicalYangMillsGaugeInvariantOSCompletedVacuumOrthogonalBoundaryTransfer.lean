import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingQuadraticGapCertificate
import MGAP4D.MathlibAnalytic.RealLinearIsometrySubspaceProjectedCompression

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance completedVacuumOrthogonalBoundaryTransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedVacuumOrthogonalBoundaryTransferSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedVacuumOrthogonalBoundaryTransferSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedVacuumOrthogonalBoundaryTransferSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedVacuumOrthogonalBoundaryTransferSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedVacuumOrthogonalBoundaryTransferSpecialUnitaryBorelSpace (N : ℕ) :
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

/-- A represented vacuum-centered carrier vector lies in the complete physical
vacuum-orthogonal sector. -/
theorem physicalState_vacuumCenteredCarrier_mem_vacuumOrthogonal
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.physicalState (Pn.vacuumCenteredCarrier F) ∈ Pn.vacuumOrthogonal := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [Pn.mem_vacuumOrthogonal_iff, Pn.physicalState_vacuumCenteredCarrier]
  unfold finiteVacuumCentered
  have hinner : inner ℝ Pn.vacuum Pn.vacuum = 1 := by
    calc
      inner ℝ Pn.vacuum Pn.vacuum = ‖Pn.vacuum‖ ^ 2 :=
        real_inner_self_eq_norm_sq Pn.vacuum
      _ = 1 := by rw [Pn.norm_vacuum hPn]; norm_num
  simp [hinner]

/-- Whole-boundary realization of the completed OS transfer restricted to the
physical excitation sector:

`Ĵ_n ∘ T_n(t/2) ∘ P_{Ω⊥} ∘ Ĵ_n⁻¹ ∘ P_{ran Ĵ_n}`.

Unlike the uncentered compression from #1474, this operator kills the vacuum
and the nonphysical ambient complement.  Therefore strict vacuum-sector decay
can hold globally on the ambient boundary `L²` space. -/
noncomputable def completedVacuumOrthogonalBoundaryTransfer
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
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  realLinearIsometrySubspaceProjectedCompression
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
    Pn.vacuumOrthogonal
    (C.finiteOperator n (t / 2))

/-- On every vacuum-centered canonical Wilson boundary moment, the centered
ambient compression is exactly half-time OS translation. -/
theorem completedVacuumOrthogonalBoundaryTransfer_vacuumCentered_intertwining
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
    Q.completedVacuumOrthogonalBoundaryTransfer hInvariant C n t
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
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Fc := Pn.vacuumCenteredCarrier F
  have hFc : Pn.physicalState Fc ∈ Pn.vacuumOrthogonal :=
    Q.physicalState_vacuumCenteredCarrier_mem_vacuumOrthogonal hInvariant n F
  calc
    Q.completedVacuumOrthogonalBoundaryTransfer hInvariant C n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc) =
      Q.completedVacuumOrthogonalBoundaryTransfer hInvariant C n t
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState Fc)) := by
      rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
    _ = Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (C.finiteOperator n (t / 2) (Pn.physicalState Fc)) := by
      exact realLinearIsometrySubspaceProjectedCompression_apply_map_mem
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
        Pn.vacuumOrthogonal
        (C.finiteOperator n (t / 2))
        (Pn.physicalState Fc) hFc
    _ = Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState
          ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
            (t / 2) Fc)) := by
      rw [Q.finiteOperator_on_carrierPhysicalState]
    _ = physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2) Fc) := by
      rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]

/-- A completed OS quadratic-gap certificate transfers without loss to the
actual centered boundary realization.  This is the direct boundary route: no
actual-adjoint synthesis factorization or bounded open-half analysis lift is
needed. -/
theorem completedVacuumOrthogonalBoundaryTransfer_opNorm_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C)
    (n : ℕ) (t : NNReal) :
    ‖Q.completedVacuumOrthogonalBoundaryTransfer hInvariant C n t‖ ≤
      Real.sqrt (R.quadraticDecayFactor t) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hhalf : t / 2 + t / 2 = t := by
    ext
    norm_num <;> ring
  apply realLinearIsometrySubspaceProjectedCompression_opNorm_le
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
    Pn.vacuumOrthogonal
    (C.finiteOperator n (t / 2))
    (Real.sqrt (R.quadraticDecayFactor t))
    (Real.sqrt_nonneg _)
  intro x hx
  have hxinner : inner ℝ x Pn.vacuum = 0 := by
    have h := (Pn.mem_vacuumOrthogonal_iff x).mp hx
    simpa [real_inner_comm] using h
  have hdecay := R.finite_decay n (t / 2) x hxinner
  rw [hhalf] at hdecay
  exact hdecay

/-- Pointwise quadratic version of the same strict boundary contraction. -/
theorem completedVacuumOrthogonalBoundaryTransfer_quadratic_bound
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    ‖Q.completedVacuumOrthogonalBoundaryTransfer hInvariant C n t v‖ ^ 2 ≤
      R.quadraticDecayFactor t * ‖v‖ ^ 2 := by
  have hop := Q.completedVacuumOrthogonalBoundaryTransfer_opNorm_le
    hInvariant C R n t
  have happ :=
    (Q.completedVacuumOrthogonalBoundaryTransfer hInvariant C n t).le_opNorm v
  have hq := R.quadraticDecayFactor_nonneg t
  have hsqrt := Real.sqrt_nonneg (R.quadraticDecayFactor t)
  have hsqrt_sq := Real.sq_sqrt hq
  have hv := norm_nonneg v
  have hout := norm_nonneg
    (Q.completedVacuumOrthogonalBoundaryTransfer hInvariant C n t v)
  nlinarith

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D

end
