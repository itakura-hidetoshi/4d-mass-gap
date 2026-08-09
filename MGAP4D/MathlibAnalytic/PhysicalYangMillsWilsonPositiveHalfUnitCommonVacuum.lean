import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonInteractingBoundaryScaleCommonVacuumCarrier
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Canonical sign/unit normalization for the coherent positive-half Wilson
pullback.

The quadratic reflected observable fixes a positive-half square root only up to
sign.  This field chooses the canonical branch on the OS unit observable:
`1 ↦ 1`.  It adds no mass, decay, coercivity, integrability, or continuum
identification hypothesis. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfUnitCompatibility
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta) : Prop where
  map_one :
    ∀ n,
      Q.positiveHalfPullback n
          (⟨(1 : physicalYangMillsGaugeInvariantObservableSubalgebra S),
            D.positiveTimeSubalgebra.one_mem⟩ :
            D.positiveTimeSubalgebra.toSubmodule) = 1

namespace PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfUnitCompatibility

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}

/-- Unit normalization identifies the actual finite positive-half observable of
the OS vacuum with the constant-one observable. -/
theorem finitePositiveHalfObservable_vacuum_eq_one
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfUnitCompatibility Q)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        Pn.vacuumObservable = 1 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [Q.finitePositiveHalfObservable_eq_positiveHalfPullback]
  change Q.positiveHalfPullback n
      (⟨(1 : physicalYangMillsGaugeInvariantObservableSubalgebra S),
        D.positiveTimeSubalgebra.one_mem⟩ :
        D.positiveTimeSubalgebra.toSubmodule) = 1
  exact U.map_one n

/-- The boundary moment of the finite OS vacuum is exactly the canonical
strictly-positive Wilson boundary-vacuum moment `m₀`. -/
theorem boundaryMoment_vacuum_eq_boundaryVacuumMoment
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfUnitCompatibility Q)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        Pn.vacuumObservable b =
      periodicHypercubicEvenBoundaryVacuumMoment
        (halfExtent n) N hN (beta n) (hbeta n) b := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
  rw [U.finitePositiveHalfObservable_vacuum_eq_one hInvariant n]
  unfold periodicHypercubicEvenBoundaryObservableMoment
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  unfold periodicHypercubicEvenBoundaryVacuumMoment
  simp

/-- The completed boundary-Haar realization of the finite OS vacuum has `m₀`
as its almost-everywhere representative. -/
theorem canonicalBoundaryMomentL2_vacuum_coeFn
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfUnitCompatibility Q)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    (fun b =>
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        Pn.vacuumObservable b) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N]
      (fun b => periodicHypercubicEvenBoundaryVacuumMoment
        (halfExtent n) N hN (beta n) (hbeta n) b) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hmem :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      Pn.vacuumObservable
  have hcoe :
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          Pn.vacuumObservable b) =ᵐ[
        periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N]
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            Pn.vacuumObservable b) := by
    simpa [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2,
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2, hmem] using
      hmem.coeFn_toLp
  filter_upwards [hcoe] with b hb
  rw [hb]
  exact U.boundaryMoment_vacuum_eq_boundaryVacuumMoment hInvariant n b

/-- The upstream unit/sign choice generates the finite interacting-boundary
vacuum normalization isolated in the previous common-carrier package.

After the boundary-Haar realization gives `m₀`, reciprocal-vacuum transport is
pointwise `m₀⁻¹ m₀ = 1`; strict positivity of `m₀` supplies the only
nonvanishing fact. -/
noncomputable def toBoundaryMarginalVacuumCompatibility
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfUnitCompatibility Q)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalVacuumCompatibility
      Q hInvariant where
  finite_vacuum_eq_one := by
    intro n
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    change
      periodicHypercubicEvenBoundaryHaarToMarginalL2
          (halfExtent n) N hN (beta n) (hbeta n)
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
            Pn.vacuum) =
        Lp.const 2
          (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
            halfExtent N hN beta hbeta n)
          (1 : ℝ)
    change
      periodicHypercubicEvenBoundaryHaarToMarginalL2
          (halfExtent n) N hN (beta n) (hbeta n)
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
            (Pn.physicalState Pn.vacuumObservable)) =
        Lp.const 2
          (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
            halfExtent N hN beta hbeta n)
          (1 : ℝ)
    rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
    apply Lp.ext
    have hvacHaar :=
      U.canonicalBoundaryMomentL2_vacuum_coeFn hInvariant n
    have hvacMarginal :=
      periodicHypercubicEven_ae_boundaryHaar_to_marginal
        (halfExtent n) N hN (beta n) (hbeta n) hvacHaar
    have htransport :=
      periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          Pn.vacuumObservable)
    have hconst :
        (Lp.const 2
          (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
            halfExtent N hN beta hbeta n)
          (1 : ℝ)) =ᵐ[
            physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
              halfExtent N hN beta hbeta n]
          (fun _ => (1 : ℝ)) := by
      exact Lp.coeFn_const
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
          halfExtent N hN beta hbeta n)
        (2 : ENNReal) (1 : ℝ)
    filter_upwards [htransport, hvacMarginal, hconst] with b ht hv hc
    rw [ht, hv, hc]
    unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Function
    unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
    field_simp [ne_of_gt
      (periodicHypercubicEvenBoundaryVacuumMoment_pos
        (halfExtent n) N hN (beta n) (hbeta n) b)]

/-- Therefore unit-normalized coherent finite Wilson pullbacks send every
finite OS vacuum to the same constant-one vector in the actual interacting
common product carrier. -/
theorem commonEmbedding_vacuum
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfUnitCompatibility Q)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Q.physicalHilbertInteractingBoundaryCommonLinearIsometry hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) =
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta :=
  (U.toBoundaryMarginalVacuumCompatibility hInvariant).commonEmbedding_vacuum n

end PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfUnitCompatibility

end

end MathlibAnalytic
end MGAP4D
