import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairSwapEquivariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# Endpoint-swap symmetry of the ground-state joint law

The carrier-level pair swap constructed for the adjacent Krylov orbit preserves
product Haar measure.  Here we lift that symmetry through the actual
ground-state Wilson density.

The key point is exact and pointwise: the vacuum factors occur symmetrically at
the two endpoints and the one-slab Wilson kernel is symmetric.  Consequently
both the raw and normalized ground-state joint weights are invariant under
`(A,B) ↦ (B,A)`.  Combining that density symmetry with product-Haar swap
invariance gives a genuine measure-preserving endpoint swap for the
ground-state joint probability law, and hence a lossless real-L2 pullback on
that law.

No posterior disintegration, support statement, or identification of left and
right conditional expectations is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance p3GroundStateSwapTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3GroundStateSwapCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3GroundStateSwapSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3GroundStateSwapMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3GroundStateSwapBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3GroundStateSwapSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The raw ground-state joint weight is exactly invariant under exchanging the
two spatial endpoints. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z.swap =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z := by
  rcases z with ⟨A, B⟩
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
  simp only [Prod.swap_prod_mk]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H N hN beta hbeta B A]
  ring

/-
The normalized-weight swap theorem and the resulting measure-preserving swap
are already available in the imported ground-state joint-measure development:

* `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_swap`
* `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving`

We reuse those authoritative facts rather than redeclaring them here.
-/

/-- Lossless real-L2 pullback by endpoint swap on the ground-state joint law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointPairSwapLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) →ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.swap
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta)

/-- The ground-state joint-L2 swap is represented a.e. by literal endpoint
exchange. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointPairSwapLinearIsometry_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointPairSwapLinearIsometry
        H N hN beta hbeta f =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta]
      fun z => f z.swap := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let hswap :
      MeasurePreserving Prod.swap ν ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  change Lp.compMeasurePreserving Prod.swap hswap f =ᵐ[ν] fun z => f z.swap
  simpa [Function.comp_def] using
    (Lp.coeFn_compMeasurePreserving f hswap)

end

end MathlibAnalytic
end MGAP4D
