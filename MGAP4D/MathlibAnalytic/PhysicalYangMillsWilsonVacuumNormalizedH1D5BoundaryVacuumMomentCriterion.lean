import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5LiteralWilsonIntegralCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePair
import Mathlib.Tactic

/-!
# Boundary-vacuum-moment form of the vacuum-normalized H1-D5 seam

The preceding literal-integral criterion still used the quotient-level `Lp`
representative of the finite OS vacuum.  The canonical-sign construction
already identifies the boundary-Haar realization of that vacuum with the
literal finite Wilson boundary vacuum moment.

This file transports that representative through the exact
boundary-to-spatial-slice-pair measure-preserving equivalence and substitutes it
into both sides of the H1-D5 matrix criterion.

No transfer compatibility, Perron--Frobenius alignment, or new model assumption
is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5VacMomentTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5VacMomentCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5VacMomentSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5VacMomentMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5VacMomentBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5VacMomentSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5VacMomentPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- The literal finite Wilson boundary vacuum moment written in ordered
spatial-slice-pair coordinates. -/
def periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (q :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ℝ :=
  periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta
    ((periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm q)

/-- A normalized physical pair-transfer coefficient can be evaluated against
any chosen a.e. representative of its source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_inner_physicalPairDecomposable_eq_literalWilsonIntegral_of_representative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hf :
      f =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N] phi) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N x y) =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2)⁻¹ *
        ∫ q, ∫ p,
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
              H N beta (p, q))
            (phi p *
              (((x :
                  Lp ℝ 2
                    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                      H N)) q.1) *
                ((y :
                  Lp ℝ 2
                    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                      H N)) q.2)))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let muPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
      H N hN beta hbeta
  let g :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
      H N x y
  have hK :
      K =ᵐ[muPair.prod muPair]
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta := by
    simpa [K, muPair] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
        H N hN beta hbeta
  have hg :
      g =ᵐ[muPair]
        fun q =>
          ((x : Lp ℝ 2 mu) q.1) *
            ((y : Lp ℝ 2 mu) q.2) := by
    simpa [
      g, mu, muPair,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2,
      realL2ExternalTensorFunction] using
      (realL2ExternalTensor_coeFn
        (μ := mu) (ν := mu)
        (x : Lp ℝ 2 mu) (y : Lp ℝ 2 mu))
  have hPairing :
      realL2HilbertSchmidtKernelPairing K f g =
        ∫ q, ∫ p,
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
              H N beta (p, q))
            (phi p *
              (((x : Lp ℝ 2 mu) q.1) *
                ((y : Lp ℝ 2 mu) q.2)))
          ∂muPair ∂muPair := by
    exact
      realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives
        K f g
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta)
        phi
        (fun q =>
          ((x : Lp ℝ 2 mu) q.1) *
            ((y : Lp ℝ 2 mu) q.2))
        hK
        (by simpa [muPair] using hf)
        hg
  change
    inner ℝ
        ((‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖ ^ 2)⁻¹ •
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta f)
        g = _
  rw [real_inner_smul_left]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner]
  rw [hPairing]

/-- The ordinary pair-Haar inner product can likewise be evaluated against any
chosen a.e. source representative. -/
theorem
    periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral_of_representative
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hf :
      f =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N] phi) :
    inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N x y) =
      ∫ q,
        inner ℝ (phi q)
          (((x :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  H N)) q.1) *
            ((y :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  H N)) q.2))
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let muPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let g :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
      H N x y
  have hg :
      g =ᵐ[muPair]
        fun q =>
          ((x : Lp ℝ 2 mu) q.1) *
            ((y : Lp ℝ 2 mu) q.2) := by
    simpa [
      g, mu, muPair,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2,
      realL2ExternalTensorFunction] using
      (realL2ExternalTensor_coeFn
        (μ := mu) (ν := mu)
        (x : Lp ℝ 2 mu) (y : Lp ℝ 2 mu))
  change inner ℝ f g = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(by simpa [muPair] using hf), hg] with q hphi hq
  rw [hphi, hq]

section VacuumMomentRepresentative

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- The pair-coordinate image of the canonical-sign finite OS vacuum is
represented a.e. by the literal finite Wilson boundary vacuum moment composed
with the inverse boundary-coordinate equivalence. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_coeFn_eq_boundaryVacuumMomentPairCoordinate
    (n : ℕ) :
    (fun q =>
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n q) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
        (halfExtent n) N]
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
        (halfExtent n) N hN (beta n) (hbeta n) := by
  let H := halfExtent n
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant n
  let J :=
    Q.vacuumNormalized.physicalHilbertBoundaryMomentLinearIsometry
      hInvariant n
  let E :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      H N
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let muB := periodicHypercubicEvenBoundaryHaarMeasure H N
  let muPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  have hJ :
      J Pn.vacuum =
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta
          Q.vacuumNormalized.toWeakStarBridge hInvariant n
          Pn.vacuumObservable := by
    change
      J (Pn.physicalState Pn.vacuumObservable) =
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta
          Q.vacuumNormalized.toWeakStarBridge hInvariant n
          Pn.vacuumObservable
    exact
      Q.vacuumNormalized.physicalHilbertBoundaryMomentLinearIsometry_physicalState
        hInvariant n Pn.vacuumObservable
  have hBoundary :
      (fun b => J Pn.vacuum b) =ᵐ[muB]
        periodicHypercubicEvenBoundaryVacuumMoment
          H N hN (beta n) (hbeta n) := by
    rw [hJ]
    simpa [H, muB, Pn] using
      (Q.vacuumNormalizedUnitCompatibility hInvariant).canonicalBoundaryMomentL2_vacuum_coeFn n
  have he :
      MeasurePreserving e muB muPair := by
    simpa [e, muB, muPair, H] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  have hForward :
      (fun q => E (J Pn.vacuum) q) =ᵐ[muPair]
        fun q => J Pn.vacuum (e.symm q) := by
    simpa [E, e, muPair, Function.comp_def] using
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry_coeFn
        H N (J Pn.vacuum)
  have hPull :
      (fun q => J Pn.vacuum (e.symm q)) =ᵐ[muPair]
        fun q =>
          periodicHypercubicEvenBoundaryVacuumMoment
            H N hN (beta n) (hbeta n) (e.symm q) := by
    simpa [Function.comp_def] using
      (MeasurePreserving.symm e he).quasiMeasurePreserving.ae_eq hBoundary
  change
    (fun q => E (J Pn.vacuum) q) =ᵐ[muPair]
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
        H N hN (beta n) (hbeta n)
  filter_upwards [hForward, hPull] with q hF hV
  rw [hF, hV]
  rfl

end VacuumMomentRepresentative

section VacuumNormalizedH1D5BoundaryMoment

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- H1-D5 with the finite OS vacuum replaced everywhere by its literal Wilson
boundary-vacuum-moment representative in pair coordinates. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_boundaryVacuumMomentWilsonIntegral :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        ∀ x y :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N,
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)‖ ^ 2)⁻¹ *
              ∫ q, ∫ p,
                inner ℝ
                  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                    (halfExtent n) N (beta n) (p, q))
                  (periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
                      (halfExtent n) N hN (beta n) (hbeta n) p *
                    (((x :
                        Lp ℝ 2
                          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                            (halfExtent n) N)) q.1) *
                      ((y :
                        Lp ℝ 2
                          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                            (halfExtent n) N)) q.2)))
                ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                  (halfExtent n) N)
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                (halfExtent n) N) =
            ∫ q,
              inner ℝ
                (periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
                  (halfExtent n) N hN (beta n) (hbeta n) q)
                (((x :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        (halfExtent n) N)) q.1) *
                  ((y :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        (halfExtent n) N)) q.2))
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                (halfExtent n) N) := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_normalizedTransfer_pairing_fixed
      Q hInvariant C]
  constructor
  · intro h n x y
    let vac :=
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
    let phi :=
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
        (halfExtent n) N hN (beta n) (hbeta n)
    have hvac :
        vac =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
            (halfExtent n) N] phi := by
      simpa [vac, phi] using
        physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_coeFn_eq_boundaryVacuumMomentPairCoordinate
          Q hInvariant n
    have hLeft :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_inner_physicalPairDecomposable_eq_literalWilsonIntegral_of_representative
        (halfExtent n) N hN (beta n) (hbeta n) vac x y phi hvac
    have hRight :=
      periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral_of_representative
        (halfExtent n) N vac x y phi hvac
    exact hLeft.symm.trans ((h n x y).trans hRight)
  · intro h n x y
    let vac :=
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
    let phi :=
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
        (halfExtent n) N hN (beta n) (hbeta n)
    have hvac :
        vac =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
            (halfExtent n) N] phi := by
      simpa [vac, phi] using
        physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_coeFn_eq_boundaryVacuumMomentPairCoordinate
          Q hInvariant n
    have hLeft :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_inner_physicalPairDecomposable_eq_literalWilsonIntegral_of_representative
        (halfExtent n) N hN (beta n) (hbeta n) vac x y phi hvac
    have hRight :=
      periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral_of_representative
        (halfExtent n) N vac x y phi hvac
    exact hLeft.trans ((h n x y).trans hRight.symm)

end VacuumNormalizedH1D5BoundaryMoment

end

end MathlibAnalytic
end MGAP4D
