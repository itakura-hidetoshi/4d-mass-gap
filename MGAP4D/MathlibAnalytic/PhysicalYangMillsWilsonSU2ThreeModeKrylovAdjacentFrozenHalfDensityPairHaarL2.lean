import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFrozenPosteriorMeanResamplingL2Budget
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarL2Equiv
import Mathlib.Tactic

/-!
# Exact pair-Haar L2 carrier of the frozen joint half-density receiver

The previous stages control M_f(B), the normalized physical frozen
posterior mean, in the actual joint L2 measure.  The original signed
right receiver is nevertheless W(C,B)*M_f(B) with
  W(C,B) = lambda^(-1) Omega(B)/sqrt(rho_joint(C,B)).

Instead of estimating W by an inverse-vacuum supremum, apply the
already-constructed inverse half-density change of measure from the
genuine joint law to pair Haar.  Exact cancellation gives

  U_joint^(-1)(W*M_f)
    = lambda^(-1) (S f) o snd

as pair-Haar L2 vectors, where S is the physical normalized one-slab
operator.  Since the two spatial Haar marginals are probability
measures, the right-coordinate pullback is isometric, hence

  ||W*M_f||_L2(joint)
    = lambda^(-1) ||S f||_L2(Haar).

The normalization lambda^(-1) is intentionally retained; no
volume-uniform bound on it is claimed.  The original joint law, source
sign, output half-density and distinct beta(n)/beta(n+1) structure
remain unchanged.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3HalfDensityPairHaarTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3HalfDensityPairHaarCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3HalfDensityPairHaarSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3HalfDensityPairHaarMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3HalfDensityPairHaarBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3HalfDensityPairHaarSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3HalfDensityPairHaarSliceHaarProbability (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance p3HalfDensityPairHaarJointProbability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- Projection onto the right coordinate preserves the actual normalized
slice-Haar measure from its original pair-Haar product carrier. -/
theorem spatialSlicePairHaar_snd_measurePreserving
    (H N : ℕ) :
    MeasurePreserving Prod.snd
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change MeasurePreserving Prod.snd (mu.prod mu) mu
  refine ⟨measurable_snd, ?_⟩
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The full joint receiver returns to the actual normalized physical
transfer by exact inverse-half-density transport, not an unproven
vacuum-denominator estimate.  The returned pair-Haar vector is a
right-coordinate pullback of the physical Haar-L2 transfer output. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_halfDensityHaarRight
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖⁻¹ •
          Lp.compMeasurePreserving Prod.snd
            (spatialSlicePairHaar_snd_measurePreserving H N)
            ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
                H N hN beta hbeta f :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
              Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let muP := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let muJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let g : Lp ℝ 2 mu := (S f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  let hSnd := spatialSlicePairHaar_snd_measurePreserving H N
  let pull : Lp ℝ 2 muP := Lp.compMeasurePreserving Prod.snd hSnd g
  let v : Lp ℝ 2 muP := lambda⁻¹ • pull
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    H N hN beta hbeta
  let F := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  have hJtoP : muJ ≪ muP := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
      H N hN beta hbeta
  have hGmu :
      g =ᵐ[mu] fun B =>
        lambda⁻¹ * decomposableOneSliceTransferIntegral H N beta
          (f : Lp ℝ 2 mu) B := by
    simpa [g, S, mu, lambda] using
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_ae_eq_inv_mul_decomposableOneSliceTransferIntegral
        H N hN beta hbeta f)
  have hGmuP :
      (fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => g z.2) =ᵐ[muP]
        fun z => lambda⁻¹ * decomposableOneSliceTransferIntegral H N beta
          (f : Lp ℝ 2 mu) z.2 := by
    simpa [muP, mu, Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := mu)).ae_eq hGmu
  have hGmuJ := hJtoP.ae_eq hGmuP
  have hPullP :
      pull =ᵐ[muP] fun z => g z.2 := by
    simpa [pull, Function.comp_def] using
      (Lp.coeFn_compMeasurePreserving g hSnd)
  have hSmulP := Lp.coeFn_smul lambda⁻¹ pull
  have hVmuP :
      v =ᵐ[muP] fun z => lambda⁻¹ * g z.2 := by
    filter_upwards [hSmulP, hPullP] with z hs hp
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul, hp]
  have hVmuJ := hJtoP.ae_eq hVmuP
  have hDensity :=
    hJtoP.ae_eq (continuousJointSqrtDensity_ae_eq H N hN beta hbeta)
  have hFrep := BoundedContinuousFunction.coeFn_toLp 2 muJ ℝ F
  have hUrep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
      H N hN beta hbeta v
  change BoundedContinuousFunction.toLp 2 muJ ℝ F =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
      H N hN beta hbeta v
  apply Lp.ext
  filter_upwards [hFrep, hUrep, hVmuJ, hDensity, hGmuJ]
      with z hF hU hV hD hG
  rw [hF, hU]
  change
    ((lambda⁻¹ * omega z.2) /
        continuousJointSqrtDensity H N hN beta hbeta z) *
      (lambda⁻¹ * decomposableOneSliceTransferIntegral H N beta
        (f : Lp ℝ 2 mu) z.2 / omega z.2) =
    v z /
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
        H N hN beta hbeta z
  rw [hV, ← hD, hG]
  have hOmega :
      omega z.2 ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.2).ne'
  have hSqrt :
      continuousJointSqrtDensity H N hN beta hbeta z ≠ 0 :=
    (continuousJointSqrtDensity_pos H N hN beta hbeta z).ne'
  field_simp [hOmega, hSqrt]

/-- The joint half-density receiver norm reduces exactly to one scalar
normalization times the original physical normalized-transfer image norm,
with no volume-dependent inverse-vacuum supremum. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_norm_eq_inv_transferNorm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f)‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f‖ := by
  rw [normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_halfDensityHaarRight
    H N hN beta hbeta f]
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let muP := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let g : Lp ℝ 2 mu :=
    ((S f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 mu)
  let hSnd := spatialSlicePairHaar_snd_measurePreserving H N
  let pull : Lp ℝ 2 muP := Lp.compMeasurePreserving Prod.snd hSnd g
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    H N hN beta hbeta
  have hpull : ‖pull‖ = ‖g‖ := by
    exact
      (Lp.compMeasurePreservingₗᵢ ℝ Prod.snd hSnd).norm_map g
  have hlam : 0 ≤ lambda⁻¹ := by
    exact
      (inv_pos.mpr
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
          H N hN beta hbeta)).le
  change ‖U (lambda⁻¹ • pull)‖ = lambda⁻¹ * ‖S f‖
  calc
    ‖U (lambda⁻¹ • pull)‖ = ‖lambda⁻¹ • pull‖ := U.norm_map _
    _ = ‖lambda⁻¹‖ * ‖pull‖ := norm_smul _ _
    _ = lambda⁻¹ * ‖g‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hlam, hpull]
    _ = lambda⁻¹ * ‖S f‖ := rfl

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
