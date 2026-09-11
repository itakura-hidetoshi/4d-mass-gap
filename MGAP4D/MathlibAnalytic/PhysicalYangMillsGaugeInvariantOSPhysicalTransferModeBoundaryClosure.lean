import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalTransferModeObservableImage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransferEigenlift
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryImageClosure
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance physicalTransferModeBoundaryClosureSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalTransferModeBoundaryClosureSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalTransferModeBoundaryClosureSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalTransferModeBoundaryClosureSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalTransferModeBoundaryClosureSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalTransferModeBoundaryClosureSpecialUnitaryBorelSpace (N : ℕ) :
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

/-- A norm limit of actual canonical Wilson boundary moments automatically lies
in the completed physical OS boundary image.

The separate range hypothesis in the first completion eigenlift is therefore
redundant whenever the target vector is supplied by an explicit approximating
sequence of canonical moments. -/
theorem mem_range_physicalHilbertBoundaryMomentLinearIsometry_of_canonicalBoundaryMoment_tendsto
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
    (F : ℕ →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (hMoment : Tendsto
      (fun k =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n (F k))
      atTop (𝓝 x)) :
    x ∈ Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) := by
  rw [Q.range_physicalHilbertBoundaryMomentLinearIsometry_eq_closure_canonicalBoundaryMoment]
  exact isClosed_closure.mem_of_tendsto hMoment
    (Filter.Eventually.of_forall (fun k => subset_closure ⟨F k, rfl⟩))

/-- Sequence realization alone is enough to lift a completed boundary
eigenmode to a genuine finite OS Hilbert eigenvector; no independent closed
range membership assumption is needed. -/
theorem exists_finiteOSEigenvector_of_canonicalBoundaryMoment_tendsto_autoRange
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
    ∃ psi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi = x ∧
      C.finiteOperator n (t / 2) psi = mu • psi := by
  apply Q.exists_finiteOSEigenvector_of_canonicalBoundaryMoment_tendsto
    hInvariant C n t mu x F
  · exact Q.mem_range_physicalHilbertBoundaryMomentLinearIsometry_of_canonicalBoundaryMoment_tendsto
      hInvariant n x F hMoment
  · exact hMoment
  · exact hTranslated

/-- Completion-compatible one-sided boundary realization.

Instead of requiring one positive-time observable whose boundary moments are
*exactly* the chosen endpoint vector and its unit translate, this structure
only asks for a sequence of actual OS carrier observables whose canonical
Wilson boundary moments converge to those two endpoint vectors.

The translated sequence uses one unit of observable time.  In the completed
boundary-transfer convention this is boundary time `t = 2`, since the exact
intertwining acts by `t / 2` on the finite OS Hilbert space. -/
structure OneSidedBoundaryClosureAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) N)) where
  approximants : ℕ →
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier
  momentZero : Tendsto
    (fun k =>
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (approximants k))
    atTop
    (𝓝 (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
      (halfExtent n) N f omega))
  momentOne : Tendsto
    (fun k =>
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          1 (approximants k)))
    atTop
    (𝓝 (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
      (halfExtent n) N fOne omegaOne))

/-- A one-sided endpoint mode realized only in Wilson boundary-moment closure
already produces a genuine finite OS Hilbert eigenvector.

This is the closure analogue of
`finiteOperator_one_eigen_of_oneSidedBoundaryObservableImage`: exact
observable realization is replaced by Hilbert convergence, while the physical
eigenvalue remains unchanged. -/
theorem exists_finiteOperator_one_eigen_of_oneSidedBoundaryClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) N))
    (mu : ℝ)
    (hf : fOne = mu • f)
    (homega : omegaOne = omega)
    (W : OneSidedBoundaryClosureAt Q hInvariant C n f omega fOne omegaOne) :
    ∃ psi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
          periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) N f omega ∧
      C.finiteOperator n 1 psi = mu • psi := by
  have hOne := W.momentOne
  rw [periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2_eq_smul
    (halfExtent n) N f omega fOne omegaOne mu hf homega] at hOne
  have hLift :=
    Q.exists_finiteOSEigenvector_of_canonicalBoundaryMoment_tendsto_autoRange
      hInvariant C n (2 : NNReal) mu
      (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
        (halfExtent n) N f omega)
      W.approximants W.momentZero (by simpa using hOne)
  simpa using hLift

/-- Closure realization specialized to the actual normalized physical one-slice
transfer mode and its fixed top/vacuum companion. -/
abbrev PhysicalTransferModeBoundaryClosureAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N) :=
  OneSidedBoundaryClosureAt Q hInvariant C n
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
      (halfExtent n) N f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      (halfExtent n) N hN (beta n) (hbeta n))
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
      (halfExtent n) N hN (beta n) (hbeta n) f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
      (halfExtent n) N hN (beta n) (hbeta n))

/-- A genuine eigenmode of the actual normalized physical one-slice transfer
lifts to a genuine finite Wilson OS Hilbert eigenvector as soon as its
one-particle boundary mode is realized in canonical Wilson moment closure.

Compared with the earlier observable-image theorem, no single exact
positive-time observable is required. -/
theorem exists_finiteOperator_one_eigen_of_normalizedPhysicalTransferModeBoundaryClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n) f = mu • f)
    (W : PhysicalTransferModeBoundaryClosureAt Q hInvariant C n f) :
    ∃ psi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
          periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) N hN (beta n) (hbeta n)) ∧
      C.finiteOperator n 1 psi = mu • psi := by
  apply Q.exists_finiteOperator_one_eigen_of_oneSidedBoundaryClosure
    hInvariant C n
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
      (halfExtent n) N f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      (halfExtent n) N hN (beta n) (hbeta n))
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
      (halfExtent n) N hN (beta n) (hbeta n) f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
      (halfExtent n) N hN (beta n) (hbeta n))
    mu
  · exact periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_eq_smul
      (halfExtent n) N hN (beta n) (hbeta n) f mu hf
  · exact periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp_eq
      (halfExtent n) N hN (beta n) (hbeta n)
  · exact W

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D

end
