import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualFiniteIntegralDefectBoundaryIntegral

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The canonical shared-boundary moment `L²` vector has squared norm exactly
equal to the finite Wilson OS quadratic value of the same positive-time
carrier observable.

This uses only theorem-generated identities: OS quadratic value equals the
actual finite reflected Wilson integral, and that integral equals the boundary
Haar integral of the squared canonical boundary moment. -/
theorem physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm_sq_eq_osQuadraticValue
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 =
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).osQuadraticValue F := by
  have hgram : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) :=
    fun b =>
      PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate.gram_integrable
        (S := S) (D := D) (halfExtent := halfExtent) (N := N)
        (hN := hN) (beta := beta) (hbeta := hbeta) (B := B)
        (hInvariant := hInvariant) n F b
  calc
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
      unfold physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      exact
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
          S D halfExtent N hN beta hbeta B hInvariant n F
          (physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
            S D halfExtent N hN beta hbeta B hInvariant n F)
    _ = physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F := by
      symm
      exact
        physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
          S D halfExtent N hN beta hbeta B hInvariant n F hgram
    _ = (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).osQuadraticValue F := by
      symm
      exact
        physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n F

/-- On the dense actual finite Wilson OS state family, the physical Hilbert norm
is exactly the norm of the canonical shared-boundary moment `L²` vector.

This is the unconditional isometric shadow needed before any attempt to
identify the OS transfer with a concrete transfer-matrix realization. -/
theorem physicalYangMillsEvenPeriodicWilsonOSPhysicalState_norm_eq_canonicalBoundaryMomentL2_norm
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖(physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).physicalState F‖ =
      ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let m :=
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent N hN beta hbeta B hInvariant n F
  have hphysical : ‖Pn.physicalState F‖ ^ 2 = Pn.osQuadraticValue F := by
    calc
      ‖Pn.physicalState F‖ ^ 2 = ‖F‖ ^ 2 := by rw [Pn.norm_physicalState]
      _ = Pn.osQuadraticValue F := (Pn.osQuadraticValue_eq_norm_sq F).symm
  have hboundary : ‖m‖ ^ 2 = Pn.osQuadraticValue F := by
    simpa [Pn, m] using
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm_sq_eq_osQuadraticValue
        S D halfExtent N hN beta hbeta B hInvariant n F
  nlinarith [norm_nonneg (Pn.physicalState F), norm_nonneg m]

/-- An actual finite Wilson OS dense state is null exactly when its canonical
shared-boundary moment vanishes in boundary Haar `L²`.

Thus the boundary moment detects precisely the OS null relation on the dense
carrier; no extra transfer-gap or compactness assumption is used. -/
theorem physicalYangMillsEvenPeriodicWilsonOSPhysicalState_eq_zero_iff_canonicalBoundaryMomentL2_eq_zero
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).physicalState F = 0 ↔
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F = 0 := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let m :=
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent N hN beta hbeta B hInvariant n F
  have hnorm : ‖Pn.physicalState F‖ = ‖m‖ := by
    simpa [Pn, m] using
      physicalYangMillsEvenPeriodicWilsonOSPhysicalState_norm_eq_canonicalBoundaryMomentL2_norm
        S D halfExtent N hN beta hbeta B hInvariant n F
  constructor
  · intro hzero
    apply norm_eq_zero.mp
    rw [← hnorm, hzero, norm_zero]
  · intro hzero
    apply norm_eq_zero.mp
    rw [hnorm]
    simpa [m] using (norm_eq_zero.mpr hzero)

end

end MathlibAnalytic
end MGAP4D