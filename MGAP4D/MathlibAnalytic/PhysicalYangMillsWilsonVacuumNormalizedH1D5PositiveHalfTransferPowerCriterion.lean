import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5PureUnfixedPathKernelCriterion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSNormalizedGramEndpointPhysicalTransfer
import Mathlib.Tactic

/-!
# Positive-half transfer-power form of the vacuum-normalized H1-D5 seam

The pure H1-D5 path criterion uses the unnormalized complete positive-half
path-kernel moment as a function of the ordered reflection-boundary pair.

This file identifies its ordinary physical test coefficient with the already
constructed positive-half physical transfer power.  The proof is a finite
Wilson Fubini/change-of-coordinates argument:

* the shared fixed boundary is reindexed into the ordered primary/antipodal
  spatial pair by an exact measure-preserving equivalence;
* the two endpoint evaluations in the positive-half transfer coordinates are
  exactly those two pair coordinates;
* the boundary vacuum moment is the open-half integral of the completed
  positive Gram feature;
* the existing normalized Gram endpoint theorem identifies the resulting
  closure integral with the physical positive-half transfer matrix element;
* the common finite partition normalization cancels.

No completed OS transfer or extra compatibility is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5PowerTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5PowerCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5PowerSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5PowerMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5PowerBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5PowerSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5PowerPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- The first coordinate of the canonical shared-boundary reindexing is
literally the primary reflection-fixed spatial slice. -/
@[simp] theorem
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_fst_apply
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ) b).1 e =
      b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e) := by
  rfl

/-- The second coordinate of the canonical shared-boundary reindexing is the
antipodal reflection-fixed slice, reindexed back to the primary link carrier by
the half-period equivalence. -/
@[simp] theorem
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_snd_apply
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ) b).2 e =
      b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
        (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)) := by
  rfl

/-- In positive-half transfer coordinates the primary endpoint is exactly the
first ordered shared-boundary slice. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_eq_boundaryPair_fst
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (u : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H N (b, u)).1 0 =
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) b).1 := by
  funext e
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_apply]
  rfl

/-- In positive-half transfer coordinates the terminal endpoint is exactly the
second ordered shared-boundary slice. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_eq_boundaryPair_snd
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (u : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H N (b, u)).1
        (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) =
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) b).2 := by
  have hlast :
      Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =
        (Fin.last H).succ := by
    apply Fin.ext
    simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
  rw [hlast]
  funext e
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_apply]
  rfl

/-- Pair-Haar testing of the literal finite Wilson boundary vacuum moment is
exactly the normalized positive-half Gram endpoint integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient_boundaryVacuumMoment_eq_gramEndpointClosureIntegral
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
        H N
        (periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN beta hbeta)
        x y =
      ∫ z,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2 *
          ((x : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
            (y : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1
                (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let eB :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Gauge
  let muB := periodicHypercubicEvenBoundaryHaarMeasure H N
  let muO := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let muP := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let X :=
    fun q :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      ((x : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.1) *
      ((y : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.2)
  let F :=
    fun z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2 *
        X (eB z.1)
  have he :
      MeasurePreserving eB muB muP := by
    simpa [eB, muB, muP, Gauge] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  have hExisting :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaussEndpoints_integrable
      H N hN beta hbeta x y
  have hInt :
      Integrable F (muB.prod muO) := by
    have hEq :
        (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            ((x : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
                ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                  H N z).1 0) *
              (y : Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
                ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                  H N z).1
                  (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))) =ᵐ[
            muB.prod muO] F := by
      filter_upwards with z
      rw [
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_eq_boundaryPair_fst,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_eq_boundaryPair_snd]
      rfl
    have hExisting' :
        Integrable
          (fun z :
            PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                H N hN beta hbeta z.1 z.2 *
              ((x : Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
                  ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                    H N z).1 0) *
                (y : Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
                  ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                    H N z).1
                    (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))))
          (muB.prod muO) := by
      simpa [
        muB, muO,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure,
        periodicHypercubicEvenPositiveHalfClosurePiMeasure,
        periodicHypercubicEvenBoundaryHaarMeasure,
        periodicHypercubicEvenOpenHalfHaarMeasure] using hExisting
    exact hExisting'.congr hEq
  unfold periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
  change
    (∫ q,
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN beta hbeta q)
        (X q) ∂muP) = _
  rw [show
    (∫ q,
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN beta hbeta q)
        (X q) ∂muP) =
      ∫ q,
        periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
            H N hN beta hbeta q * X q ∂muP by
          apply integral_congr_ae
          filter_upwards with q
          rw [realScalarInner_eq_mul]]
  let G :=
    fun q :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN beta hbeta q * X q
  have hChange := he.integral_comp' G
  calc
    (∫ q,
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN beta hbeta q * X q ∂muP) =
        ∫ b, G (eB b) ∂muB := by
      exact hChange.symm
    _ = ∫ b,
        (∫ u,
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b u ∂muO) * X (eB b) ∂muB := by
      apply integral_congr_ae
      filter_upwards with b
      simp only [G, periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate,
        periodicHypercubicEvenBoundaryVacuumMoment, eB, muO]
      rw [MeasurableEquiv.symm_apply_apply]
    _ = ∫ b, ∫ u,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b u * X (eB b)
        ∂muO ∂muB := by
      apply integral_congr_ae
      filter_upwards with b
      rw [integral_mul_const]
    _ = ∫ z, F z ∂(muB.prod muO) := by
      exact (MeasureTheory.integral_prod F hInt).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_eq_boundaryPair_fst,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_eq_boundaryPair_snd]
      rfl

/-- The unnormalized complete positive-half path-kernel vacuum message has
ordinary physical matrix coefficients equal to the full positive-half physical
transfer power. -/
theorem
    periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient_vacuumUnfixedPathKernelMoment_eq_physicalPositiveHalfTransfer
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
        H N
        (periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
          H N beta)
        x y =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta x) y := by
  let Z :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction
  let c := (Real.sqrt Z)⁻¹
  have hZ : 0 < Z := by
    exact
      compact_oriented_partitionFunction_pos
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base
        (continuous_compact_oriented_boltzmannIntegrable
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
  have hsqrt : Real.sqrt Z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hZ)
  have hc : c ≠ 0 := inv_ne_zero hsqrt
  have hVac :=
    periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient_boundaryVacuumMoment_eq_gramEndpointClosureIntegral
      H N hN beta hbeta x y
  have hTransfer :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_closureIntegral_eq_invSqrtPartition_mul_physicalTransfer
      H N hN beta hbeta x y
  have hVacTransfer :
      periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
          H N
          (periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
            H N hN beta hbeta)
          x y =
        c *
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN beta hbeta x) y := by
    exact hVac.trans (by simpa [c, Z] using hTransfer)
  have hScale :=
    periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient_scale_source
      H N c
      (periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
        H N beta)
      x y
  have hVacPoint :
      (fun q =>
        periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN beta hbeta q) =
      (fun q =>
        c *
          periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
            H N beta q) := by
    funext q
    simpa [c, Z] using
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_eq_invSqrtPartition_mul_unfixedPathKernelMomentPairCoordinate
        H N hN beta hbeta q
  rw [hVacPoint, hScale] at hVacTransfer
  exact mul_left_cancel₀ hc hVacTransfer

end

end MathlibAnalytic
end MGAP4D
