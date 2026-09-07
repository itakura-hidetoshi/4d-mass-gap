import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector
import Mathlib.MeasureTheory.Measure.WithDensity
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

/-- The square of the canonical nonnegative physical top-vacuum representative.
This is the Radon--Nikodym weight of the ground-state boundary law with respect
to spatial Haar measure. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta).1 A) ^ 2

/-- The unnormalized ground-state Wilson one-slab weight on a pair of spatial
boundaries. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1 z.1 *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta z.1 z.2 *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1 z.2

/-- The normalized Doob/ground-state one-slab weight.  Its normalization uses
the actual physical transfer norm, whose strict positivity was proved from the
literal Wilson kernel. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
      H N hN beta hbeta z

/-- The vacuum boundary measure `Ω² dμ`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
    (fun A => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
        H N hN beta hbeta A))

/-- The genuine ground-state Wilson one-slab joint measure
`λ⁻¹ Ω(A) K(A,B) Ω(B) dμ(A)dμ(B)`, with `ofReal` only clipping a null set on
which an arbitrary `L²` representative need not be nonnegative. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).withDensity
    (fun z => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z))

/-- The vacuum weight is integrable because the canonical vacuum lies in real
`L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let f : Lp ℝ 2 μ := Ω.1
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight, f, Ω, μ] using
    (Lp.memLp f).integrable_sq

/-- The normalized physical vacuum makes `Ω² dμ` have total mass one. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
        H N hN beta hbeta A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) = 1 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let f : Lp ℝ 2 μ := Ω.1
  have hnorm : ‖f‖ = 1 := by
    change ‖Ω‖ = 1
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H N hN beta hbeta
  calc
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
        H N hN beta hbeta A ∂μ) =
        ∫ A, ‖f A‖ ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with A
          simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight,
            f, Ω, Real.norm_eq_abs, sq_abs]
    _ = ‖f‖ ^ 2 := by
      symm
      exact realL2_norm_sq_eq_integral_norm_sq f
    _ = 1 := by rw [hnorm]; norm_num

/-- The unnormalized ground-state joint weight is integrable without any
pointwise formula for the Fréchet--Riesz transfer output. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let f : Lp ℝ 2 μ := Ω.1
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let E := realL2ExternalTensor f f
  change Integrable
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
      H N hN beta hbeta) (μ.prod μ)
  have hcore : Integrable (fun z => inner ℝ (K z) (E z)) (μ.prod μ) :=
    MeasureTheory.L2.integrable_inner K E
  apply hcore.congr
  have hKrep :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta
  have hErep := realL2ExternalTensor_coeFn f f
  filter_upwards [hKrep, hErep] with z hk hE
  rw [hk, hE]
  simp only [realL2ExternalTensorFunction, real_inner_eq_re_inner (𝕜 := ℝ),
    RCLike.inner_apply, RCLike.re_to_real, conj_trivial]
  dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight,
    f, Ω]
  ring

/-- Hilbert--Schmidt pairing and the Hilbert-space top-eigenvector equation
normalize the raw ground-state joint weight to exactly the physical transfer
norm.  No pointwise eigen-equation is introduced. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∫ z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let f : Lp ℝ 2 μ := Ω.1
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let E := realL2ExternalTensor f f
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  have hKrep :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta
  have hErep := realL2ExternalTensor_coeFn f f
  have hcoreEq :
      (fun z => inner ℝ (K z) (E z)) =ᵐ[μ.prod μ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
          H N hN beta hbeta := by
    filter_upwards [hKrep, hErep] with z hk hE
    rw [hk, hE]
    simp only [realL2ExternalTensorFunction, real_inner_eq_re_inner (𝕜 := ℝ),
      RCLike.inner_apply, RCLike.re_to_real, conj_trivial]
    dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight,
      f, Ω]
    ring
  have heigenP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H N hN beta hbeta
  have heigenAmbient : T f = lambda • f := by
    have hval := congrArg Subtype.val heigenP
    simpa [T, f, Ω, lambda] using hval
  have hfnorm : ‖f‖ = 1 := by
    change ‖Ω‖ = 1
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H N hN beta hbeta
  change
    (∫ z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z ∂(μ.prod μ)) = lambda
  calc
    (∫ z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z ∂(μ.prod μ)) =
        ∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ) :=
      integral_congr_ae hcoreEq.symm
    _ = inner ℝ (T f) f := by
      symm
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]
      change inner ℝ K E = ∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ)
      exact MeasureTheory.L2.inner_def K E
    _ = lambda := by
      rw [heigenAmbient, real_inner_smul_left, real_inner_self_eq_norm_sq, hfnorm]
      ring

/-- The raw joint density is strictly positive almost everywhere on Haar pairs.
The only exceptional set comes from the chosen `L²` representative of the
vacuum; the literal Wilson kernel itself is positive everywhere. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_ae_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ᵐ z ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N),
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta z := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hΩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_pos
      H N hN beta hbeta
  have hfst :
      ∀ᵐ z ∂(μ.prod μ),
        0 < (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hΩ
  have hsnd :
      ∀ᵐ z ∂(μ.prod μ),
        0 < (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hΩ
  change ∀ᵐ z ∂(μ.prod μ),
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
      H N hN beta hbeta z
  filter_upwards [hfst, hsnd] with z h1 h2
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
  exact mul_pos
    (mul_pos h1
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta z.1 z.2)) h2

/-- The normalized ground-state joint weight is integrable. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_integrable
      H N hN beta hbeta).const_mul _

/-- The normalized joint weight has integral one. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∫ z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) = 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
  rw [integral_const_mul,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_integral]
  exact inv_mul_cancel₀
    (ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta))

/-- The normalized joint density is strictly positive almost everywhere. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ᵐ z ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N),
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H N hN beta hbeta z := by
  have hlambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight_ae_pos
      H N hN beta hbeta] with z hz
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
  exact mul_pos (inv_pos.mpr hlambda) hz

/-- The vacuum boundary law is a probability measure. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) where
  measure_univ := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight_integrable
        H N hN beta hbeta)
      (ae_of_all _ fun A => sq_nonneg
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A)),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight_integral]
    simp

/-- The ground-state Wilson one-slab joint law is a probability measure. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) where
  measure_univ := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
        H N hN beta hbeta)
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
        H N hN beta hbeta).mono fun _ hz => hz.le),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integral]
    simp

end

end MathlibAnalytic
end MGAP4D