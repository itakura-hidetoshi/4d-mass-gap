import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedBoundaryGaugeFixed
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundarySpatialHalfWeightFactorization
import Mathlib.Tactic

/-!
# Independent endpoint gauge action on the ordered boundary pair

The reflection-fixed boundary is exactly the disjoint union of the primary and
antipodal spatial slices.  Consequently two arbitrary one-slice gauge
transformations extend to one full finite-lattice gauge transformation by using
the first transformation on the primary fixed plane, the second (after the
canonical half-period reindexing) on the antipodal fixed plane, and identity
away from both fixed planes.

This file proves that the exact boundary/two-slice measurable equivalence
intertwines that full boundary action with the independent product action on
the ordered endpoint pair.

As a consequence, the canonical-sign finite OS vacuum pair from #5017 is fixed
by arbitrary and independent gauge transformations at its two endpoints.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance vacuumPairIndependentGaugeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumPairIndependentGaugeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumPairIndependentGaugeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumPairIndependentGaugeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumPairIndependentGaugeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumPairIndependentGaugeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance vacuumPairIndependentGaugeSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Extend two independently chosen endpoint gauge transformations to the full
four-dimensional periodic vertex set. -/
noncomputable def periodicHypercubicEvenIndependentEndpointGaugeExtension
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ := by
  classical
  exact fun v =>
    if hp : periodicHypercubicEvenOnPrimaryReflectionPlane H v then
      gammaPrimary ⟨v, hp⟩
    else if ha : periodicHypercubicEvenOnAntipodalReflectionPlane H v then
      gammaAntipodal
        ((periodicHypercubicEvenPrimaryAntipodalSpatialSliceVertexEquiv H).symm
          ⟨v, ha⟩)
    else 1

@[simp] theorem periodicHypercubicEvenIndependentEndpointGaugeExtension_primary
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenIndependentEndpointGaugeExtension
        H N gammaPrimary gammaAntipodal v.1 =
      gammaPrimary v := by
  classical
  simp [periodicHypercubicEvenIndependentEndpointGaugeExtension, v.2]

@[simp] theorem periodicHypercubicEvenIndependentEndpointGaugeExtension_antipodal
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenIndependentEndpointGaugeExtension
        H N gammaPrimary gammaAntipodal
        (periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex H v).1 =
      gammaAntipodal v := by
  classical
  have hnot :
      ¬ periodicHypercubicEvenOnPrimaryReflectionPlane H
        (periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex H v).1 := by
    intro hp
    exact periodicHypercubicEven_primary_antipodal_disjoint H
      (periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex H v).1
      hp
      (periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex H v).2
  rw [periodicHypercubicEvenIndependentEndpointGaugeExtension]
  rw [dif_neg hnot]
  rw [dif_pos
    (periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex H v).2]
  exact congrArg gammaAntipodal
    ((periodicHypercubicEvenPrimaryAntipodalSpatialSliceVertexEquiv H).left_inv v)

/-- Exact inverse pair-coordinate evaluation on a primary-slice fixed edge. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_apply_primary
    (H : ℕ) {Value : Type*} [MeasurableSpace Value]
    (A B : PeriodicHypercubicEvenSpatialSliceLink H → Value)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value).symm
        (A, B)
        (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e) =
      A e := by
  have hidx :
      periodicHypercubicEvenFixedEdgeToSpatialSliceSum H
          (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e) =
        Sum.inl e :=
    (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).right_inv
      (Sum.inl e)
  change
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H => Value)).symm (A, B))
        (periodicHypercubicEvenFixedEdgeToSpatialSliceSum H
          (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e)) =
      A e
  rw [hidx]
  rfl

/-- Exact inverse pair-coordinate evaluation on an antipodal fixed edge,
canonically reindexed by a primary-slice link. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_apply_antipodal
    (H : ℕ) {Value : Type*} [MeasurableSpace Value]
    (A B : PeriodicHypercubicEvenSpatialSliceLink H → Value)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value).symm
        (A, B)
        (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
          (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)) =
      B e := by
  have hidx :
      periodicHypercubicEvenFixedEdgeToSpatialSliceSum H
          (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
            (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)) =
        Sum.inr e :=
    (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).right_inv
      (Sum.inr e)
  change
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H => Value)).symm (A, B))
        (periodicHypercubicEvenFixedEdgeToSpatialSliceSum H
          (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
            (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e))) =
      B e
  rw [hidx]
  rfl

/-- Exact forward pair-coordinate evaluation on a primary fixed edge. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_apply_primary
    (H : ℕ) {Value : Type*} [MeasurableSpace Value]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value b).1 e =
      b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e) := by
  have h :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_apply_primary
      H
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value b).1
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value b).2
      e
  simpa using h.symm

/-- Exact forward pair-coordinate evaluation on an antipodal fixed edge. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_apply_antipodal
    (H : ℕ) {Value : Type*} [MeasurableSpace Value]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value b).2 e =
      b
        (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
          (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)) := by
  have h :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_apply_antipodal
      H
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value b).1
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value b).2
      e
  simpa using h.symm

/-- Independent product gauge action on the ordered primary/antipodal pair. -/
def periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
      H N gammaPrimary z.1,
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
      H N gammaAntipodal z.2)

/-- The full boundary gauge action for the endpoint extension becomes exactly
the independent product gauge action after the exact two-slice coordinate
equivalence. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_gaugeTransform
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ)
        (periodicHypercubicEvenBoundaryGaugeTransform H N
          (periodicHypercubicEvenIndependentEndpointGaugeExtension
            H N gammaPrimary gammaAntipodal) b) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform
        H N gammaPrimary gammaAntipodal
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) b) := by
  classical
  let E :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let z := E b
  apply Prod.ext
  · funext e
    rw [
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_apply_primary]
    change
      periodicHypercubicEvenIndependentEndpointGaugeExtension
          H N gammaPrimary gammaAntipodal e.1.1 *
        b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e) *
        (periodicHypercubicEvenIndependentEndpointGaugeExtension
          H N gammaPrimary gammaAntipodal
          (periodicHypercubicEvenSpatialSliceShift H e.1 e.2).1)⁻¹ =
      gammaPrimary e.1 * z.1 e *
        (gammaPrimary
          (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹
    rw [
      periodicHypercubicEvenIndependentEndpointGaugeExtension_primary,
      periodicHypercubicEvenIndependentEndpointGaugeExtension_primary]
    have hb :
        b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e) =
          z.1 e := by
      simpa [z, E] using
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_apply_primary
          H b e).symm
    rw [hb]
  · funext e
    rw [
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_apply_antipodal]
    let ea :=
      periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e
    have hb :
        b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H ea) =
          z.2 e := by
      simpa [ea, z, E] using
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_apply_antipodal
          H b e).symm
    have hsrc :
        ea.1.1 =
          (periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex H e.1).1 := by
      rfl
    have htgt :
        periodicHypercubicEdgeTarget
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H ea).1 =
          (periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex H
            (periodicHypercubicEvenSpatialSliceShift H e.1 e.2)).1 := by
      dsimp [ea, periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv,
        periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge]
      exact
        (periodicHypercubicEvenHalfPeriodTimeShift_shift_spatial
          H e.1.1 e.2.1 e.2.2).symm
    change
      periodicHypercubicEvenIndependentEndpointGaugeExtension
          H N gammaPrimary gammaAntipodal ea.1.1 *
        b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H ea) *
        (periodicHypercubicEvenIndependentEndpointGaugeExtension
          H N gammaPrimary gammaAntipodal
          (periodicHypercubicEdgeTarget
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H ea).1))⁻¹ =
      gammaAntipodal e.1 * z.2 e *
        (gammaAntipodal
          (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹
    rw [hsrc, htgt, hb]
    rw [
      periodicHypercubicEvenIndependentEndpointGaugeExtension_antipodal,
      periodicHypercubicEvenIndependentEndpointGaugeExtension_antipodal]

/-- The independent endpoint action preserves product Haar probability. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform_measurePreserving
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform
        H N gammaPrimary gammaAntipodal)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  exact MeasurePreserving.prod
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H N gammaPrimary)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H N gammaAntipodal)

/-- L2 pullback for independent gauge transformations on the two endpoints. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform
      H N gammaPrimary gammaAntipodal)
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform_measurePreserving
      H N gammaPrimary gammaAntipodal)

/-- The independent pair gauge pullback has the expected almost-everywhere
representative.  Naming this coercion boundary avoids relying downstream on
unfolding `Lp.compMeasurePreserving` through the linear-isometry wrapper. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry_coeFn
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
        H N gammaPrimary gammaAntipodal f =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      fun z =>
        f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform
          H N gammaPrimary gammaAntipodal z) := by
  simpa [
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry,
    Function.comp_def] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform_measurePreserving
        H N gammaPrimary gammaAntipodal))

/-- Exact L2 conjugacy between the full boundary gauge pullback and the
independent endpoint pair pullback. -/
theorem periodicHypercubicEvenBoundaryGaugePullback_to_pair
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
        (periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N
          (periodicHypercubicEvenIndependentEndpointGaugeExtension
            H N gammaPrimary gammaAntipodal) f) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
        H N gammaPrimary gammaAntipodal
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          H N f) := by
  apply Lp.ext
  let E :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let G :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform
      H N gammaPrimary gammaAntipodal
  let gamma :=
    periodicHypercubicEvenIndependentEndpointGaugeExtension
      H N gammaPrimary gammaAntipodal
  have hleft :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry_coeFn
      H N
      (periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N gamma f)
  have hboundary :=
    periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry_coeFn
      H N gamma f
  have hpull :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry_coeFn
      H N gammaPrimary gammaAntipodal
      (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f)
  have hforward :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry_coeFn
      H N f
  have hESymm :
      MeasurePreserving E.symm
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
    exact MeasurePreserving.symm E
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_haar
        H N)
  have hboundaryPair :=
    hESymm.quasiMeasurePreserving.ae_eq hboundary
  have hforwardGauge :=
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform_measurePreserving
      H N gammaPrimary gammaAntipodal).quasiMeasurePreserving.ae_eq hforward
  filter_upwards [hleft, hboundaryPair, hpull, hforwardGauge]
      with z hL hB hP hF
  have hL' :
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
          (periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N gamma f) z =
        periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N gamma f
          (E.symm z) := by
    simpa [E, Function.comp_def] using hL
  have hB' :
      periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N gamma f
          (E.symm z) =
        f (periodicHypercubicEvenBoundaryGaugeTransform H N gamma (E.symm z)) := by
    simpa [E, Function.comp_def] using hB
  have hP' :
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
          H N gammaPrimary gammaAntipodal
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f) z =
        periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f
          (G z) := by
    simpa [G] using hP
  have hF' :
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f
          (G z) =
        f (E.symm (G z)) := by
    simpa [E, G, Function.comp_def] using hF
  have hcoord :
      periodicHypercubicEvenBoundaryGaugeTransform H N gamma (E.symm z) =
        E.symm (G z) := by
    apply E.injective
    rw [E.apply_symm_apply]
    simpa [E, G, gamma] using
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_gaugeTransform
        H N gammaPrimary gammaAntipodal (E.symm z))
  calc
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
        (periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N gamma f) z =
      periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N gamma f
        (E.symm z) := hL'
    _ = f (periodicHypercubicEvenBoundaryGaugeTransform H N gamma (E.symm z)) := hB'
    _ = f (E.symm (G z)) := by rw [hcoord]
    _ = periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f
        (G z) := hF'.symm
    _ = periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
        H N gammaPrimary gammaAntipodal
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f) z := hP'.symm

/-- The concrete boundary vacuum in pair coordinates is fixed by arbitrary
independent endpoint gauge transformations. -/
theorem periodicHypercubicEvenBoundaryVacuumPairL2_independentGaugeFixed
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
        H N gammaPrimary gammaAntipodal
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
          (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta)) =
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) := by
  rw [← periodicHypercubicEvenBoundaryGaugePullback_to_pair]
  rw [periodicHypercubicEvenBoundaryVacuumL2_gaugeFixed]

section VacuumNormalizedPair

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

/-- Canonical-sign explicit OS vacuum pairs are fixed by arbitrary and
independent primary/antipodal endpoint gauge transformations. -/
theorem physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_independentGaugeFixed
    (n : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation
        (halfExtent n) N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
        (halfExtent n) N gammaPrimary gammaAntipodal
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n) =
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_eq_boundaryVacuumPair
      Q hInvariant n]
  exact
    periodicHypercubicEvenBoundaryVacuumPairL2_independentGaugeFixed
      (halfExtent n) N hN (beta n) (hbeta n)
      gammaPrimary gammaAntipodal

end VacuumNormalizedPair

end

end MathlibAnalytic
end MGAP4D
