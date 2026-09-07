import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Basic
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

/-- Restrict the canonical physical top vacuum to a measurable boundary event,
without leaving the Haar `L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hs : MeasurableSet s) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let f : Lp ℝ 2 μ := Ω.1
  ((Lp.memLp f).indicator hs).toLp (s.indicator fun A => f A)

/-- The restricted-vacuum `L²` vector has the expected indicator
representative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hs : MeasurableSet s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2
        H N hN beta hbeta s hs =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      s.indicator (fun A =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let f : Lp ℝ 2 μ := Ω.1
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2,
    μ, Ω, f] using ((Lp.memLp f).indicator hs).coeFn_toLp

/-- Pairing the vacuum with its measurable restriction is exactly the vacuum
weight integrated over that event. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuum_inner_indicator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hs : MeasurableSet s) :
    inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2
          H N hN beta hbeta s hs) =
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
  have hg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2_coeFn
      H N hN beta hbeta s hs
  change inner ℝ f g = ∫ A in s,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
      H N hN beta hbeta A ∂μ
  rw [MeasureTheory.L2.inner_def]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [hg] with A hA
  rw [hA]
  by_cases hAs : A ∈ s
  · rw [Set.indicator_of_mem hAs, Set.indicator_of_mem hAs]
    simp only [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
      RCLike.re_to_real, conj_trivial]
    dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight, f, Ω]
    ring
  · rw [Set.indicator_of_notMem hAs, Set.indicator_of_notMem hAs]
    simp

/-- The raw ground-state joint weight restricted on the right boundary has
mass `λ` times the corresponding vacuum mass.  The proof is entirely through
the Hilbert--Schmidt matrix coefficient and the Hilbert-space eigen-equation. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_setIntegral_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hs : MeasurableSet s) :
    ∫ z in Prod.snd ⁻¹' s,
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
  let E := realL2ExternalTensor f g
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  have hKrep :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta
  have hErep := realL2ExternalTensor_coeFn f g
  have hgrep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumIndicatorL2_coeFn
      H N hN beta hbeta s hs
  have hsndQMP :
      Measure.QuasiMeasurePreserving
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => z.2)
        (μ.prod μ) μ := by
    exact Measure.quasiMeasurePreserving_snd
  have hgrepProd :
      ∀ᵐ z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ∂(μ.prod μ),
        g z.2 =
          s.indicator (fun A =>
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 A) z.2 := by
    simpa [Function.comp_def] using hgrep.comp_tendsto hsndQMP.tendsto_ae
  have hpre : MeasurableSet (Prod.snd ⁻¹' s) := measurable_snd hs
  have hcoreEq :
      (fun z => inner ℝ (K z) (E z)) =ᵐ[μ.prod μ]
        (Prod.snd ⁻¹' s).indicator
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
            H N hN beta hbeta) := by
    filter_upwards [hKrep, hErep, hgrepProd] with z hk hE hg
    rw [hk, hE, hg]
    simp only [realL2ExternalTensorFunction, real_inner_eq_re_inner (𝕜 := ℝ),
      RCLike.inner_apply, RCLike.re_to_real, conj_trivial]
    by_cases hz : z.2 ∈ s
    · rw [Set.indicator_of_mem hz]
      have hzpre : z ∈ Prod.snd ⁻¹' s := hz
      rw [Set.indicator_of_mem hzpre]
      dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight,
        f, Ω]
      ring
    · rw [Set.indicator_of_notMem hz]
      have hzpre : z ∉ Prod.snd ⁻¹' s := hz
      rw [Set.indicator_of_notMem hzpre]
      ring
  have heigenP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H N hN beta hbeta
  have heigenAmbient : T f = lambda • f := by
    have hval := congrArg Subtype.val heigenP
    simpa [T, f, Ω, lambda] using hval
  change
    (∫ z in Prod.snd ⁻¹' s,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z ∂(μ.prod μ)) =
      lambda * ∫ A in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
          H N hN beta hbeta A ∂μ
  calc
    (∫ z in Prod.snd ⁻¹' s,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z ∂(μ.prod μ)) =
        ∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ) := by
      rw [← integral_indicator hpre]
      exact integral_congr_ae hcoreEq.symm
    _ = inner ℝ (T f) g := by
      symm
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]
      change inner ℝ K E = ∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ)
      exact MeasureTheory.L2.inner_def K E
    _ = lambda * inner ℝ f g := by
      rw [heigenAmbient, real_inner_smul_left]
    _ = lambda * ∫ A in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
          H N hN beta hbeta A ∂μ := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuum_inner_indicator]

/-- After division by the strictly positive top transfer norm, the right
boundary event mass equals its vacuum event mass. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_setIntegral_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hs : MeasurableSet s) :
    ∫ z in Prod.snd ⁻¹' s,
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_setIntegral_snd
      H N hN beta hbeta s hs]
  change lambda⁻¹ *
      (lambda * ∫ A in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
          H N hN beta hbeta A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = _
  rw [← mul_assoc, inv_mul_cancel₀ hlambda.ne', one_mul]

/-- The right-coordinate pushforward of the ground-state joint law is exactly
the vacuum boundary law. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure.map Prod.snd
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_snd hs]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta (Prod.snd ⁻¹' s) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta s
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure,
    withDensity_apply _ (measurable_snd hs)]
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_setIntegral_snd
      H N hN beta hbeta s hs]

/-- The second boundary coordinate is measure preserving from the Wilson
one-slab ground-state joint law to the vacuum law. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_snd_measurePreserving
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MeasurePreserving Prod.snd
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) :=
  ⟨measurable_snd,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_snd
      H N hN beta hbeta⟩

/-- Pulling a vacuum `L²` vector back along the right boundary coordinate is a
canonical linear isometry into the ground-state one-slab joint `L²` space. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
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
  Lp.compMeasurePreservingₗᵢ ℝ Prod.snd
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_snd_measurePreserving
      H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D