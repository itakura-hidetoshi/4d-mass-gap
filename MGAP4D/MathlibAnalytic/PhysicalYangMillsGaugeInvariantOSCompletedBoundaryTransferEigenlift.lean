import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransfer

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance completedBoundaryEigenliftSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedBoundaryEigenliftSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedBoundaryEigenliftSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedBoundaryEigenliftSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedBoundaryEigenliftSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedBoundaryEigenliftSpecialUnitaryBorelSpace (N : ℕ) :
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

/-- A boundary `L²` vector is an eigenvector of the completed Wilson boundary
transfer as soon as it is the Hilbert limit of canonical boundary moments whose
translated moments converge to the corresponding scalar multiple.

This is the completion-compatible replacement for requiring one exact
positive-time observable to realize the target vector and its translate. -/
theorem completedBoundaryTransfer_eigen_of_canonicalBoundaryMoment_tendsto
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) (mu : ℝ)
    (x : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
    (F : ℕ →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (hMoment : Tendsto
      (fun k =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n (F k))
      atTop (𝓝 x))
    (hTranslated : Tendsto
      (fun k =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
            (t / 2) (F k)))
      atTop (𝓝 (mu • x))) :
    Q.completedBoundaryTransfer hInvariant C n t x = mu • x := by
  have hMapped : Tendsto
      (fun k =>
        Q.completedBoundaryTransfer hInvariant C n t
          (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n (F k)))
      atTop
      (𝓝 (Q.completedBoundaryTransfer hInvariant C n t x)) :=
    (Q.completedBoundaryTransfer hInvariant C n t).continuous.continuousAt.tendsto.comp hMoment
  have hMapped' : Tendsto
      (fun k =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
            (t / 2) (F k)))
      atTop
      (𝓝 (Q.completedBoundaryTransfer hInvariant C n t x)) := by
    simpa only [Q.completedBoundaryTransfer_apply_canonicalBoundaryMoment] using hMapped
  exact tendsto_nhds_unique hMapped' hTranslated

/-- Every eigenvector of the completed boundary transfer that lies in the
closed physical OS boundary image lifts uniquely enough to a finite OS Hilbert
space eigenvector with the same eigenvalue.

No ambient Hilbert equivalence or surjectivity of the boundary realization is
used: only membership in the actual closed range and injectivity of the
Mathlib linear isometry `Ĵ_n`. -/
theorem exists_finiteOSEigenvector_of_completedBoundaryTransfer_eigen
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) (mu : ℝ)
    (x : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
    (hx : x ∈ Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n))
    (heigen : Q.completedBoundaryTransfer hInvariant C n t x = mu • x) :
    ∃ psi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi = x ∧
      C.finiteOperator n (t / 2) psi = mu • psi := by
  rcases hx with ⟨psi, rfl⟩
  refine ⟨psi, rfl, ?_⟩
  apply (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n).injective
  simpa only [map_smul,
    Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment] using heigen

/-- Dense canonical moment approximation plus closed-range membership is
therefore sufficient to produce a genuine finite OS Hilbert eigenvector. -/
theorem exists_finiteOSEigenvector_of_canonicalBoundaryMoment_tendsto
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) (mu : ℝ)
    (x : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
    (F : ℕ →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (hx : x ∈ Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n))
    (hMoment : Tendsto
      (fun k =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n (F k))
      atTop (𝓝 x))
    (hTranslated : Tendsto
      (fun k =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
            (t / 2) (F k)))
      atTop (𝓝 (mu • x))) :
    ∃ psi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi = x ∧
      C.finiteOperator n (t / 2) psi = mu • psi := by
  apply Q.exists_finiteOSEigenvector_of_completedBoundaryTransfer_eigen
    hInvariant C n t mu x hx
  exact Q.completedBoundaryTransfer_eigen_of_canonicalBoundaryMoment_tendsto
    hInvariant C n t mu x F hMoment hTranslated

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D

end
