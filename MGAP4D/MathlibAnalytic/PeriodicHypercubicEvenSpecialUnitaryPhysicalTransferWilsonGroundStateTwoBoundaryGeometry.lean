import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateMarginalGeometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The raw ground-state joint weight restricted on the left boundary has
mass `λ` times the corresponding vacuum mass.  The proof is the left-boundary
counterpart of the right marginal theorem, with the existing exact symmetry of
the Hilbert--Schmidt kernel pairing supplying the only exchange of boundary
coordinates. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_setIntegral_fst
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hs : MeasurableSet s) :
    ∫ z in Prod.fst ⁻¹' s,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        ∫ A in s,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
            H N hN beta hbeta A
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let f : Lp ℝ 2 μ := Ω.1
  let g := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2
    H N hN beta hbeta s hs
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let E := realL2ExternalTensor g f
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  have hKrep :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta
  have hErep := realL2ExternalTensor_coeFn g f
  have hgrep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2_coeFn
      H N hN beta hbeta s hs
  have hfstQMP :
      Measure.QuasiMeasurePreserving
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => z.1)
        (μ.prod μ) μ := by
    exact Measure.quasiMeasurePreserving_fst
  have hgrepProd :
      ∀ᵐ z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ∂(μ.prod μ),
        g z.1 =
          s.indicator (fun A =>
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 A) z.1 := by
    simpa [Function.comp_def] using hgrep.comp_tendsto hfstQMP.tendsto_ae
  have hpre : MeasurableSet
      ((fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => z.1) ⁻¹' s) :=
    measurable_fst hs
  have hcoreEq :
      (fun z => inner ℝ (K z) (E z)) =ᵐ[μ.prod μ]
        (Prod.fst ⁻¹' s).indicator
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
            H N hN beta hbeta) := by
    filter_upwards [hKrep, hErep, hgrepProd] with z hk hE hg
    rw [hk, hE]
    simp only [realL2ExternalTensorFunction]
    rw [hg]
    simp only [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
      RCLike.re_to_real, conj_trivial]
    by_cases hz : z.1 ∈ s
    · rw [Set.indicator_of_mem hz]
      have hzpre : z ∈ Prod.fst ⁻¹' s := hz
      rw [Set.indicator_of_mem hzpre]
      dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight,
        f, Ω]
      ring
    · rw [Set.indicator_of_notMem hz]
      have hzpre : z ∉ Prod.fst ⁻¹' s := hz
      rw [Set.indicator_of_notMem hzpre]
      ring
  have heigenP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H N hN beta hbeta
  have heigenAmbient : T f = lambda • f := by
    have hval := congrArg Subtype.val heigenP
    simpa [T, f, Ω, lambda] using hval
  have hsymm :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_symmetric
      H N hN beta hbeta
  change
    (∫ z in Prod.fst ⁻¹' s,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z ∂(μ.prod μ)) =
      lambda * ∫ A in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
          H N hN beta hbeta A ∂μ
  calc
    (∫ z in Prod.fst ⁻¹' s,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z ∂(μ.prod μ)) =
        ∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ) := by
      rw [← integral_indicator hpre]
      exact integral_congr_ae hcoreEq.symm
    _ = realL2HilbertSchmidtKernelPairing K g f := by
      change (∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ)) = inner ℝ K E
      exact (MeasureTheory.L2.inner_def K E).symm
    _ = realL2HilbertSchmidtKernelPairing K f g := hsymm g f
    _ = inner ℝ (T f) g := by
      symm
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]
    _ = lambda * inner ℝ f g := by
      rw [heigenAmbient, real_inner_smul_left]
    _ = lambda * ∫ A in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
          H N hN beta hbeta A ∂μ := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuum_inner_indicator]

/-- After division by the strictly positive top transfer norm, the left
boundary event mass equals its vacuum event mass. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_setIntegral_fst
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hs : MeasurableSet s) :
    ∫ z in Prod.fst ⁻¹' s,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =
      ∫ A in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
          H N hN beta hbeta A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  have hlambda : 0 < lambda := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
  rw [integral_const_mul,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_setIntegral_fst
      H N hN beta hbeta s hs]
  change lambda⁻¹ *
      (lambda * ∫ A in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
          H N hN beta hbeta A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = _
  rw [← mul_assoc, inv_mul_cancel₀ hlambda.ne', one_mul]

/-- The left-coordinate pushforward of the ground-state joint law is exactly
the vacuum boundary law. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_fst
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure.map Prod.fst
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_fst hs]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta (Prod.fst ⁻¹' s) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta s
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure,
    withDensity_apply _ (measurable_fst hs)]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure,
    withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
        H N hN beta hbeta).integrableOn
      (ae_restrict_of_ae
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
          H N hN beta hbeta).mono fun _ hz => hz.le)),
    ← ofReal_integral_eq_lintegral_ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight_integrable
        H N hN beta hbeta).integrableOn
      (ae_restrict_of_ae
        (ae_of_all _ fun A => sq_nonneg
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1 A))),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_setIntegral_fst
      H N hN beta hbeta s hs]

/-- The first boundary coordinate is measure preserving from the Wilson
one-slab ground-state joint law to the vacuum law. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_fst_measurePreserving
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MeasurePreserving Prod.fst
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) :=
  ⟨measurable_fst,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_fst
      H N hN beta hbeta⟩

/-- Pulling a vacuum `L²` vector back along the left boundary coordinate is a
canonical linear isometry into the ground-state one-slab joint `L²` space. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) →ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_fst_measurePreserving
      H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D