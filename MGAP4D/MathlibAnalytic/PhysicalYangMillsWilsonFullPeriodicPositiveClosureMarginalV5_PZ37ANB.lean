import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveMeasurePushforward
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentPositivity
import MGAP4D.MathlibAnalytic.MeasureMapFstProdWithDensity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANB — genuine full-periodic Wilson positive-closure marginal

ADDITIVE candidate after independently certified ANB fiber theorem.
Formal base `afaec9844528395877a8936ad75066251c2a369c`.

This file does NOT assume that the full-periodic Gibbs restriction is ANA's
normalized temporal-gauge half-path law. It constructs the exact pushforward to
shared reflection-fixed boundary plus the positive open half by integrating
only the negative open-half coordinate of the *original normalized* Gibbs
density. The resulting normalization is still the true full-periodic partition
function, already contained in the certified boundary-fibered Gibbs density.

This source requires a new exact-source Lean run, axiom audits, and independent
receipt before any merge. It does not alter the certified ANB fiber result.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Transport an arbitrary measurable density through a measurable equivalence.
This is a change-of-variables lemma, not an assumption about Wilson measures. -/
theorem p4Q2PZ37ANB_map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (d : β → ℝ≥0∞)
    (hd : Measurable d) :
    Measure.map e (μ.withDensity (d ∘ e)) =
      (Measure.map e μ).withDensity d := by
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  rw [withDensity_apply _ (hs.preimage e.measurable)]
  rw [withDensity_apply _ hs]
  rw [MeasureTheory.setLIntegral_map hs hd e.measurable]
  rfl

/-- The true marginal of a density on `α × (β × γ)` after forgetting only
`γ`, with the original product-bracketing and normalization preserved.

Unlike a `Prod.fst` projection from the original bracketing, the map retains
BOTH `α` and `β`. The factor is a fiberwise `lintegral`, not a constant. -/
theorem p4Q2PZ37ANB_map_positiveClosure_prod_withDensity
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ξ]
    (d : α × (β × γ) → ℝ≥0∞)
    (hd : Measurable d) :
    Measure.map (fun z : α × (β × γ) => (z.1, z.2.1))
        ((μ.prod (ν.prod ξ)).withDensity d) =
      (μ.prod ν).withDensity
        (fun z : α × β => ∫⁻ y, d (z.1, (z.2, y)) ∂ξ) := by
  let e : ((α × β) × γ) ≃ᵐ α × (β × γ) := MeasurableEquiv.prodAssoc
  let proj : α × (β × γ) → α × β := fun z => (z.1, z.2.1)
  have hproj : Measurable proj :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hAssoc :
      Measure.map e ((μ.prod ν).prod ξ) = μ.prod (ν.prod ξ) := by
    simpa [e] using (Measure.prodAssoc_prod (μ := μ) (ν := ν) (τ := ξ))
  have hSource :
      Measure.map e (((μ.prod ν).prod ξ).withDensity (d ∘ e)) =
        (μ.prod (ν.prod ξ)).withDensity d := by
    rw [p4Q2PZ37ANB_map_withDensity_measurableEquiv e _ d hd]
    rw [hAssoc]
  have hcomp :
      proj ∘ e = (Prod.fst : ((α × β) × γ) → α × β) := by
    funext z
    cases z with
    | mk ab c =>
      cases ab with
      | mk a b => rfl
  change Measure.map proj ((μ.prod (ν.prod ξ)).withDensity d) = _
  calc
    Measure.map proj ((μ.prod (ν.prod ξ)).withDensity d) =
        Measure.map proj
          (Measure.map e (((μ.prod ν).prod ξ).withDensity (d ∘ e))) := by
      rw [hSource]
    _ = Measure.map (proj ∘ e)
          (((μ.prod ν).prod ξ).withDensity (d ∘ e)) :=
      Measure.map_map hproj e.measurable
    _ = Measure.map Prod.fst
          (((μ.prod ν).prod ξ).withDensity (d ∘ e)) := by rw [hcomp]
    _ = (μ.prod ν).withDensity
          (fun z : α × β => ∫⁻ y, (d ∘ e) (z, y) ∂ξ) := by
      exact measure_map_fst_prod_withDensity (μ.prod ν) ξ (d ∘ e)
        (hd.comp e.measurable)
    _ = (μ.prod ν).withDensity
          (fun z : α × β => ∫⁻ y, d (z.1, (z.2, y)) ∂ξ) := by
      rfl

local instance p4Q2PZ37ANB_marginal_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance p4Q2PZ37ANB_marginal_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37ANB_marginal_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37ANB_marginal_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37ANB_marginal_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37ANB_marginal_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual full-periodic `SU(N)` Wilson Gibbs law, restricted to the shared
reflection-fixed boundary together with the complete positive open half, is
the corresponding product-Haar law weighted by the fiberwise integral of the
EXACT ORIGINAL full-periodic Gibbs density over the negative open half.

This is a typed marginal law on `(boundary, positive open-half)`, NOT yet the
normalized temporal-gauge spatial-path law used by AMZ/ANA. -/
theorem p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
            (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)).withDensity
        (fun z =>
          ∫⁻ y,
            periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
              H N hN beta hbeta (z.1, (z.2, y))
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let μb := periodicHypercubicEvenBoundaryHaarMeasure H N
  let μh := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let d := periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
    H N hN beta hbeta
  letI : SFinite μb := by
    dsimp [μb, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : SFinite μh := by
    dsimp [μh, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hd : Measurable d := by
    exact periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hcoords :
      Measure.map (P.boundaryFiberedCoordinates Gauge) C.gibbsMeasure =
        (μb.prod (μh.prod μh)).withDensity d := by
    simpa [P, C, μb, μh, d] using
      periodicHypercubicEvenSpecialUnitary_map_boundaryFiberedCoordinates_gibbsMeasure
        H N hN beta hbeta
  let proj : P.BoundaryConfiguration Gauge ×
      (P.OpenHalfConfiguration Gauge × P.OpenHalfConfiguration Gauge) →
        P.BoundaryConfiguration Gauge × P.OpenHalfConfiguration Gauge :=
    fun z => (z.1, z.2.1)
  have hproj : Measurable proj :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hcomp :
      proj ∘ P.boundaryFiberedCoordinates Gauge =
        (fun A => (P.boundaryRestriction A, P.positiveRestriction A)) := by
    rfl
  change Measure.map
      (fun A => (P.boundaryRestriction A, P.positiveRestriction A)) C.gibbsMeasure =
        (μb.prod μh).withDensity
          (fun z => ∫⁻ y, d (z.1, (z.2, y)) ∂μh)
  calc
    Measure.map
        (fun A => (P.boundaryRestriction A, P.positiveRestriction A)) C.gibbsMeasure =
        Measure.map (proj ∘ P.boundaryFiberedCoordinates Gauge) C.gibbsMeasure := by
      rw [hcomp]
      rfl
    _ = Measure.map proj
          (Measure.map (P.boundaryFiberedCoordinates Gauge) C.gibbsMeasure) := by
      exact (Measure.map_map hproj
        (P.boundaryFiberedCoordinates_measurable Gauge)).symm
    _ = Measure.map proj ((μb.prod (μh.prod μh)).withDensity d) := by
      rw [hcoords]
    _ = (μb.prod μh).withDensity
          (fun z => ∫⁻ y, d (z.1, (z.2, y)) ∂μh) := by
      exact p4Q2PZ37ANB_map_positiveClosure_prod_withDensity
        μb μh μh d hd

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_map_withDensity_measurableEquiv
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_map_positiveClosure_prod_withDensity
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal