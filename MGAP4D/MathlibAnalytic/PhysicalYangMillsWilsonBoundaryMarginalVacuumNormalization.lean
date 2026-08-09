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

/-- Minimal upstream normalization needed for the coherent finite-Wilson
positive-half pullback to carry the OS vacuum observable to the finite
constant-one observable.

This is deliberately stated before any boundary moment, density change, common
carrier, mass, gap, decay, or coercivity input.  The coherent pullback is only
real-linear, so preservation of the multiplicative unit is the one additional
kinematic compatibility which cannot be inferred from linearity alone. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) : Prop where
  positiveHalfPullback_vacuum_eq_one :
    ∀ n,
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      Q.positiveHalfPullback n (Pn.toPositiveTime Pn.vacuumObservable) = 1

namespace PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility

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
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Unit preservation at the coherent pullback is exactly unit preservation for
the finite positive-half observable attached to the OS vacuum carrier. -/
@[simp] theorem finitePositiveHalfObservable_vacuum_eq_one
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        Pn.vacuumObservable = 1 := by
  dsimp only
  rw [Q.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n]
  exact U.positiveHalfPullback_vacuum_eq_one n

/-- Consequently the actual finite Wilson shared-boundary moment of the OS
vacuum is the canonical Wilson boundary-vacuum wavefunction pointwise. -/
theorem boundaryMoment_vacuum_eq_vacuumMoment
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
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
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
  unfold periodicHypercubicEvenBoundaryObservableMoment
  unfold periodicHypercubicEvenBoundaryVacuumMoment
  apply integral_congr_ae
  filter_upwards with x
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  rw [U.finitePositiveHalfObservable_vacuum_eq_one n]
  simp

/-- The canonical boundary-Haar `L²` image of the finite OS vacuum has the
Wilson boundary-vacuum moment as its representative. -/
theorem canonicalBoundaryMomentL2_vacuum_coeFn
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    (fun b =>
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        Pn.vacuumObservable b) =ᵐ[
          periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N]
      periodicHypercubicEvenBoundaryVacuumMoment
        (halfExtent n) N hN (beta n) (hbeta n) := by
  dsimp only
  unfold physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
  refine
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumObservable)).coeFn_toLp.trans ?_
  filter_upwards with b
  exact U.boundaryMoment_vacuum_eq_vacuumMoment n b

/-- Reciprocal-vacuum density transport sends the boundary-Haar realization of
the OS vacuum to the canonical constant-one vector in the interacting boundary
marginal `L²`.

Pointwise this is only `m₀⁻¹ * m₀ = 1`; strict positivity of the already
constructed Wilson boundary-vacuum moment supplies the nonzero denominator. -/
theorem boundaryMarginal_vacuum_eq_one
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          Pn.vacuumObservable) =
      Lp.const 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
          halfExtent N hN beta hbeta n)
        (1 : ℝ) := by
  dsimp only
  change
    periodicHypercubicEvenBoundaryHaarToMarginalL2
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumObservable)) =
      Lp.const 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
          halfExtent N hN beta hbeta n)
        (1 : ℝ)
  apply Lp.ext
  let f :=
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumObservable)
  have htransport :=
    periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      (halfExtent n) N hN (beta n) (hbeta n) f
  have hvacHaar :
      (fun b => f b) =ᵐ[
        periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N]
        periodicHypercubicEvenBoundaryVacuumMoment
          (halfExtent n) N hN (beta n) (hbeta n) := by
    simpa [f] using U.canonicalBoundaryMomentL2_vacuum_coeFn n
  have hvacMarginal :=
    periodicHypercubicEven_ae_boundaryHaar_to_marginal
      (halfExtent n) N hN (beta n) (hbeta n) hvacHaar
  have hconst :=
    Lp.coeFn_const
      (μ := physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
        halfExtent N hN beta hbeta n)
      (p := (2 : ENNReal)) (c := (1 : ℝ))
  filter_upwards [htransport, hvacMarginal, hconst] with b htransport_b hvac_b hconst_b
  rw [htransport_b, hconst_b]
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Function
  rw [hvac_b]
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
  simp only [Function.const_apply]
  exact inv_mul_cancel₀
    (ne_of_gt
      (periodicHypercubicEvenBoundaryVacuumMoment_pos
        (halfExtent n) N hN (beta n) (hbeta n) b))

/-- The downstream finite-vacuum compatibility used by the interacting common
carrier is theorem-generated from the strictly upstream unit-preservation law. -/
noncomputable def toBoundaryMarginalVacuumCompatibility
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalVacuumCompatibility
      Q hInvariant where
  finite_vacuum_eq_one := by
    intro n
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    change
      periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
          (halfExtent n) N hN (beta n) (hbeta n)
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n Pn.vacuum) =
        Lp.const 2
          (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
            halfExtent N hN beta hbeta n)
          (1 : ℝ)
    change
      periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
          (halfExtent n) N hN (beta n) (hbeta n)
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
            (Pn.physicalState Pn.vacuumObservable)) =
        Lp.const 2
          (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
            halfExtent N hN beta hbeta n)
          (1 : ℝ)
    rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
    exact U.boundaryMarginal_vacuum_eq_one n

/-- Hence all finite Wilson OS vacua land on the same distinguished
constant-one vector in the theorem-generated interacting infinite-product
common carrier. -/
theorem commonEmbedding_vacuum
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    Q.physicalHilbertInteractingBoundaryCommonLinearIsometry hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) =
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta :=
  U.toBoundaryMarginalVacuumCompatibility.commonEmbedding_vacuum n

end PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility

end

end MathlibAnalytic
end MGAP4D
