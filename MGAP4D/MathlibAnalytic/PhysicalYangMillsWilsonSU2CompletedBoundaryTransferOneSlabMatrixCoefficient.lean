import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CompletedBoundaryTransferOneSlabIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance completedBoundaryOneSlabMatrixCoefficientSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedBoundaryOneSlabMatrixCoefficientTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedBoundaryOneSlabMatrixCoefficientCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedBoundaryOneSlabMatrixCoefficientSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedBoundaryOneSlabMatrixCoefficientMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedBoundaryOneSlabMatrixCoefficientBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance completedBoundaryOneSlabMatrixCoefficientSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

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

/-- Weak matrix-coefficient form of the completed-boundary/one-slab
intertwining at one cutoff.

Instead of asking for a vector equality in the pair Haar `L²` carrier, this
asks only that every matrix coefficient against an arbitrary pair-Haar test
vector agree.  This is the form naturally produced by the literal Wilson
kernel, Fubini, and Hilbert--Schmidt pairing identities. -/
def CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) : Prop :=
  ∀ f omega :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N,
    ∀ z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) N,
      inner ℝ
          (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
            (halfExtent n) N
            (Q.completedBoundaryTransfer hInvariant C n 2)
            (periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
              (halfExtent n) N
              (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
                (halfExtent n) N f)
              (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
                (halfExtent n) N omega))) z =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
              (halfExtent n) N hN (beta n) (hbeta n) f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
              (halfExtent n) N hN (beta n) (hbeta n) omega)) z

/-- Weak equality of all real pair-Haar matrix coefficients already implies the
strong vector-valued pair intertwining used by the exact-gap lane.

The proof is pure Hilbert-space separation: test the coefficient identity on
the difference of the two candidate vectors.  No finite OS eigen-equation,
continuum equation, Hamiltonian equation, or model-specific integral identity
is used here. -/
theorem completedBoundaryTransferOneSlabPairIntertwiningAt_of_weak
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (hWeak : CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt
      Q hInvariant C n) :
    CompletedBoundaryTransferOneSlabPairIntertwiningAt Q hInvariant C n := by
  intro f omega
  let x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
    periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
      (halfExtent n) N
      (Q.completedBoundaryTransfer hInvariant C n 2)
      (periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
        (halfExtent n) N
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
          (halfExtent n) N f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
          (halfExtent n) N omega))
  let y : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
    periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
      (halfExtent n) N
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        (halfExtent n) N hN (beta n) (hbeta n) f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        (halfExtent n) N hN (beta n) (hbeta n) omega)
  have hxy : ∀ z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N, inner ℝ x z = inner ℝ y z := by
    intro z
    simpa [CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt, x, y] using
      hWeak f omega z
  have htest := hxy (x - y)
  have hself : inner ℝ (x - y) (x - y) = 0 := by
    calc
      inner ℝ (x - y) (x - y) =
          inner ℝ x (x - y) - inner ℝ y (x - y) := by
        rw [inner_sub_left]
      _ = 0 := by rw [htest]; ring
  have hnormsq : ‖x - y‖ ^ 2 = 0 := by
    simpa using hself
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  have hzero : x - y = 0 := norm_eq_zero.mp hnorm
  exact sub_eq_zero.mp hzero

/-- All-cutoff weak matrix-coefficient compatibility is enough for the strong
structural one-slab compatibility family consumed by the downstream exact-gap
chain. -/
theorem completedBoundaryTransferOneSlabPairIntertwining_of_weak
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (hWeak : ∀ n,
      CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt
        Q hInvariant C n) :
    ∀ n, CompletedBoundaryTransferOneSlabPairIntertwiningAt
      Q hInvariant C n := by
  intro n
  exact Q.completedBoundaryTransferOneSlabPairIntertwiningAt_of_weak
    hInvariant C n (hWeak n)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
