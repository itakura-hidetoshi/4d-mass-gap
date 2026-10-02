import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5PathMessageFixedVector
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSNormalizedGramEndpointPhysicalTransfer
import Mathlib.Tactic

/-!
# The finite Wilson path message is the kernel vector of the positive-half transfer power

After #5036 the remaining H1-D5 seam is a raw pair-transfer eigen-equation for
the unnormalized complete positive-half Wilson path message.

This file identifies the matrix coefficients of that path message.  Against
every decomposable pair of one-slice Gauss-law states, its pair-Haar coefficient
is exactly the matrix coefficient of the physical transfer across the complete
positive half-cylinder, i.e. the `H+1`-fold power of the physical one-slab
transfer.

The proof is only finite-volume Haar/Fubini geometry:

* transport pair-Haar back to the shared Wilson boundary;
* expand the boundary vacuum moment as its open-half Gram integral;
* use the exact boundary/open-half product Haar law;
* identify the primary and antipodal boundary coordinates with the two path
  endpoints;
* apply the existing Gauss-endpoint positive-half transfer theorem;
* finally cancel the already-exposed positive partition normalization.

No completed OS transfer, continuum input, or additional compatibility
assumption occurs here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5PathCoeffTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5PathCoeffCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5PathCoeffSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5PathCoeffMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5PathCoeffBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5PathCoeffSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5PathCoeffPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance h1d5PathCoeffBoundaryHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance h1d5PathCoeffOpenHalfHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The first component of the canonical boundary-to-pair coordinate map is
literally the primary fixed spatial slice. -/
@[simp] theorem
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_fst_apply
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (a : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) b).1 a =
      b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H a) := by
  classical
  let X :
      (PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H) → Type :=
    fun _ => Matrix.specialUnitaryGroup (Fin N) ℂ
  let E := periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H
  let reindex := MeasurableEquiv.piCongrLeft X E
  let split := MeasurableEquiv.sumPiEquivProdPi X
  change (split (reindex b)).1 a =
    b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H a)
  change reindex b (Sum.inl a) =
    b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H a)
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := X) E b (E.symm (Sum.inl a))
  rw [E.apply_symm_apply] at h
  simpa [reindex, E,
    periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices,
    periodicHypercubicEvenSpatialSliceSumToFixedEdge] using h

/-- The second component of the canonical boundary-to-pair coordinate map is
the antipodal fixed slice, canonically reindexed by half-period translation. -/
@[simp] theorem
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_snd_apply
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (a : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) b).2 a =
      b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
        (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H a)) := by
  classical
  let X :
      (PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H) → Type :=
    fun _ => Matrix.specialUnitaryGroup (Fin N) ℂ
  let E := periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H
  let reindex := MeasurableEquiv.piCongrLeft X E
  let split := MeasurableEquiv.sumPiEquivProdPi X
  change (split (reindex b)).2 a =
    b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
      (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H a))
  change reindex b (Sum.inr a) =
    b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
      (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H a))
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := X) E b (E.symm (Sum.inr a))
  rw [E.apply_symm_apply] at h
  simpa [reindex, E,
    periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices,
    periodicHypercubicEvenSpatialSliceSumToFixedEdge] using h

/-- The last positive-half slab endpoint is the antipodal fixed spatial layer. -/
theorem periodicHypercubicEvenPositiveHalfCylinder_finLast_eq_finLast_succ
    (H : ℕ) :
    Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =
      (Fin.last H).succ := by
  apply Fin.ext
  simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]

/-- Pair-Haar coefficient of the normalized finite Wilson boundary vacuum is the
positive-half physical transfer coefficient with exactly the reciprocal
square-root partition normalization. -/
theorem
    periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_pairCoefficient_eq_invSqrtPartition_mul_physicalPositiveHalfTransfer
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
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN beta hbeta x)
          y := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let muPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let muB :=
    periodicHypercubicEvenBoundaryHaarMeasure H N
  let muO :=
    periodicHypercubicEvenOpenHalfHaarMeasure H N
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let phi :=
    periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
      H N hN beta hbeta
  let test := fun q :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    ((x : Lp ℝ 2 mu) q.1) * ((y : Lp ℝ 2 mu) q.2)
  let raw := fun z :
      PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta z.1 z.2 *
      ((x : Lp ℝ 2 mu)
          ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1 0) *
        (y : Lp ℝ 2 mu)
          ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1
            (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
  have he : MeasurePreserving e muB muPair := by
    simpa [e, muB, muPair] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  have hchange :=
    he.integral_comp'
      (fun q =>
        inner ℝ (phi q) (test q))
  have hRaw :
      Integrable raw
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) := by
    simpa only [raw, mu, mul_assoc] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaussEndpoints_integrable
        H N hN beta hbeta x y
  have hEndpoint :
      ∀ z :
          PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
            (Matrix.specialUnitaryGroup (Fin N) ℂ),
        test (e z.1) =
          ((x : Lp ℝ 2 mu)
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
            (y : Lp ℝ 2 mu)
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1
                (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) := by
    intro z
    have hPrimary :
        (e z.1).1 =
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1 0 := by
      funext a
      dsimp [e]
      rw [
        periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_fst_apply,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_apply
      ]
    have hAntipodal :
        (e z.1).2 =
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1
            (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) := by
      funext a
      have hLast :
          (Fin.last (H + 1) : Fin (H + 2)) = (Fin.last H).succ := by
        apply Fin.ext
        rfl
      rw [hLast]
      dsimp [e]
      rw [
        periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_snd_apply,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_apply
      ]
    dsimp [test]
    rw [hPrimary, hAntipodal]
  have hRawProd :
      Integrable raw (muB.prod muO) := by
    simpa only [
      muB, muO,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure,
      periodicHypercubicEvenPositiveHalfClosurePiMeasure
    ] using hRaw
  have hProd :
      Integrable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            test (e z.1))
        (muB.prod muO) := by
    apply hRawProd.congr
    filter_upwards with z
    dsimp [raw]
    exact
      congrArg
        (fun t : ℝ =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 * t)
        (hEndpoint z).symm
  unfold periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
  calc
    (∫ q,
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN beta hbeta q)
        (((x : Lp ℝ 2 mu) q.1) * ((y : Lp ℝ 2 mu) q.2))
      ∂muPair) =
        ∫ b,
          inner ℝ (phi (e b)) (test (e b)) ∂muB := by
      symm
      simpa [phi, test, e, mu, muPair, muB] using hchange
    _ =
        ∫ b,
          periodicHypercubicEvenBoundaryVacuumMoment
              H N hN beta hbeta b *
            test (e b)
          ∂muB := by
      apply integral_congr_ae
      filter_upwards with b
      rw [realScalarInner_eq_mul]
      simp [phi, periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate, e]
    _ =
        ∫ b,
          (∫ u,
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                H N hN beta hbeta b u *
              test (e b)
            ∂muO)
          ∂muB := by
      apply integral_congr_ae
      filter_upwards with b
      unfold periodicHypercubicEvenBoundaryVacuumMoment
      rw [← integral_mul_const]
    _ =
        ∫ z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            test (e z.1)
          ∂(muB.prod muO) := by
      symm
      exact MeasureTheory.integral_prod _ hProd
    _ =
        ∫ z :
          PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
            (Matrix.specialUnitaryGroup (Fin N) ℂ),
          raw z
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [raw]
      exact
        congrArg
          (fun t : ℝ =>
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                H N hN beta hbeta z.1 z.2 * t)
          (hEndpoint z)
    _ =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN beta hbeta x)
          y := by
      simpa [raw, mu] using
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_closureIntegral_eq_invSqrtPartition_mul_physicalTransfer
          H N hN beta hbeta x y

/-- After cancelling the strictly positive finite partition normalization, the
literal unnormalized path message is exactly the Hilbert--Schmidt kernel vector
of the physical transfer across the complete positive half-cylinder. -/
theorem
    periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate_pairCoefficient_eq_physicalPositiveHalfTransfer
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
          H N hN beta hbeta x)
        y := by
  let z :=
    Real.sqrt
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction
  let c := z⁻¹
  let phi :=
    periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
      H N beta
  have hZ :
      0 <
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction :=
    compact_oriented_partitionFunction_pos
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base
      (continuous_compact_oriented_boltzmannIntegrable
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
  have hz : z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hZ)
  have hc : c ≠ 0 := inv_ne_zero hz
  have hVac :=
    periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_pairCoefficient_eq_invSqrtPartition_mul_physicalPositiveHalfTransfer
      H N hN beta hbeta x y
  have hScale :=
    periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient_scale_source
      H N c phi x y
  have hPoint :
      (fun q => c * phi q) =
        periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN beta hbeta := by
    funext q
    symm
    exact
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_eq_invSqrtPartition_mul_unfixedPathKernelMomentPairCoordinate
        H N hN beta hbeta q
  rw [hPoint] at hScale
  have hmul :
      c *
          periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
            H N phi x y =
        c *
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN beta hbeta x)
            y := by
    calc
      c *
          periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
            H N phi x y =
        periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
          H N
          (periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
            H N hN beta hbeta)
          x y := hScale.symm
      _ =
        c *
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN beta hbeta x)
            y := by
        simpa [c, z] using hVac
  exact mul_left_cancel₀ hc hmul

section PhysicalPathMessage

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

/-- The concrete finite Wilson path-message `L²` vector from #5036 has exactly
the matrix coefficients of the physical `H+1`-slab transfer operator. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_inner_decomposable_eq_physicalPositiveHalfTransfer
    (n : ℕ)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N) :
    inner ℝ
        (physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
          Q hInvariant n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          (halfExtent n) N x y) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) x)
        y := by
  let H := halfExtent n
  let msg :=
    physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
      Q hInvariant n
  let phi :=
    periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
      H N (beta n)
  have hrep :
      msg =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
        phi := by
    simpa [msg, phi, H] using
      physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_coeFn
        Q hInvariant n
  have hinner :=
    periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral_of_representative
      H N msg x y phi hrep
  calc
    inner ℝ msg
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N x y) =
      periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
        H N phi x y := by
          simpa [
            periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient] using hinner
    _ =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN (beta n) (hbeta n) x)
        y := by
          exact
            periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate_pairCoefficient_eq_physicalPositiveHalfTransfer
              H N hN (beta n) (hbeta n) x y

end PhysicalPathMessage

end

end MathlibAnalytic
end MGAP4D
