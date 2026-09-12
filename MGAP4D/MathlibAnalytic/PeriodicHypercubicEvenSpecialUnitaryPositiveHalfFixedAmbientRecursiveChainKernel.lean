import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance positiveHalfFixedAmbientRecursiveChainKernelIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientRecursiveChainKernelCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientRecursiveChainKernelSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientRecursiveChainKernelMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientRecursiveChainKernelBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientRecursiveChainKernelSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Fixed-ambient inward Wilson chain kernel.

For a boundary pair `(A,B)` and `R` remaining interior slices, this recursively
peels the two endpoint slices of the remaining chain without changing the
ambient spatial extent `H`.

* `R = 0`: the two boundary slices are joined by one literal one-slab kernel;
* `R = 1`: the unique central slice is represented by the diagonal pair
  `(C,C)` in the pair kernel;
* `R = R' + 2`: the next distinct inward endpoint pair is peeled by the
  fixed-ambient measurable equivalence, contributing exactly one pair kernel,
  and recursion continues on the shorter chain.

The second component of the pair kernel is deliberately oriented from the
right boundary inward.  Its later identification with the literal path order
uses the already-proved symmetry of the one-slab Wilson kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
    (H N : ℕ)
    (beta : ℝ) :
    (R : ℕ) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N →
      ℝ
  | 0, boundary, _ =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta boundary.1 boundary.2
  | Nat.succ 0, boundary, path =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N beta (boundary, (path 0, path 0))
  | Nat.succ (Nat.succ R), boundary, path =>
      let peeled :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
          H R N path
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta (boundary, peeled.1) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
          H N beta R peeled.1 peeled.2

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_zero
    (H N : ℕ)
    (beta : ℝ)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (path :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H 0 N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
        H N beta 0 boundary path =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta boundary.1 boundary.2 := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_one
    (H N : ℕ)
    (beta : ℝ)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (path :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H 1 N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
        H N beta 1 boundary path =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N beta (boundary, (path 0, path 0)) := by
  rfl

/-- Exact fixed-ambient two-sided Markov recursion at the integrand level.
Peeling two remaining slices contributes the ambient pair one-step kernel and
leaves the same recursive chain kernel on `R` deeper slices. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_add_two
    (H R N : ℕ)
    (beta : ℝ)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (path :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
        H (R + 2) N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
        H N beta (R + 2) boundary path =
      let peeled :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
          H R N path
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta (boundary, peeled.1) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
          H N beta R peeled.1 peeled.2 := by
  rfl

/-- At positive rank and nonnegative coupling every fixed-ambient recursive
chain kernel has absolute value at most one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_abs_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ (R : ℕ)
      (boundary :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (path :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N),
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
          H N beta R boundary path| ≤ 1 := by
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      intro boundary path
      cases R with
      | zero =>
          simpa using
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
              H N hN beta hbeta boundary.1 boundary.2)
      | succ R =>
          cases R with
          | zero =>
              simpa using
                (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
                  H N hN beta hbeta (boundary, (path 0, path 0)))
          | succ R =>
              let peeled :=
                periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
                  H R N path
              rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_add_two]
              rw [abs_mul]
              have hPair :
                  |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                      H N beta (boundary, peeled.1)| ≤ 1 :=
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
                  H N hN beta hbeta (boundary, peeled.1)
              have hRest :
                  |periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
                      H N beta R peeled.1 peeled.2| ≤ 1 := by
                exact ih R (by omega) peeled.1 peeled.2
              calc
                |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                    H N beta (boundary, peeled.1)| *
                    |periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
                      H N beta R peeled.1 peeled.2| ≤ 1 * 1 := by
                  exact mul_le_mul hPair hRest (abs_nonneg _) (by norm_num)
                _ = 1 := by norm_num

end

end MathlibAnalytic
end MGAP4D
