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
  simp only [Prod.swap_prod_mk, Prod.fst, Prod.snd]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H N hN beta hbeta B A]
  ring

/-- The normalized Doob/ground-state density inherits the same exact endpoint
swap symmetry. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z.swap =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_swap]

/-- Endpoint swap preserves the genuine ground-state joint probability law.
This is the exact measure-level bridge needed before conjugating right-boundary
conditional-expectation constructions to the left boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MeasurePreserving Prod.swap
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z)
  refine ⟨measurable_swap, ?_⟩
  change Measure.map Prod.swap ((μ.prod μ).withDensity w) = (μ.prod μ).withDensity w
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_swap hs,
    withDensity_apply _ (measurable_swap hs),
    withDensity_apply _ hs]
  calc
    (∫⁻ z in Prod.swap ⁻¹' s, w z ∂μ.prod μ) =
        ∫⁻ z in Prod.swap ⁻¹' s, w z.swap ∂μ.prod μ := by
      apply setLIntegral_congr_fun (measurable_swap hs)
      intro z hz
      dsimp [w]
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_swap
      ]
    _ = ∫⁻ z in s, w z ∂μ.prod μ := by
      exact
        (Measure.measurePreserving_swap :
          MeasurePreserving Prod.swap (μ.prod μ) (μ.prod μ)).setLIntegral_comp_preimage_emb
            MeasurableEquiv.prodComm.measurableEmbedding w s

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
