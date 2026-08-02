import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalL2Density
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHaarGibbsL2Isometry

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct ENNReal NNReal

noncomputable section

universe u

local instance boundaryMarginalIsometryNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMarginalIsometryTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMarginalIsometryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMarginalIsometrySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMarginalIsometryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMarginalIsometryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The boundary marginal density is pointwise nonzero because the finite
Wilson OS boundary vacuum wavefunction is strictly positive. -/
theorem periodicHypercubicEvenBoundaryMarginalDensity_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryMarginalDensity
      H N hN beta hbeta b ≠ 0 := by
  unfold periodicHypercubicEvenBoundaryMarginalDensity
  rw [ENNReal.ofReal_ne_zero_iff]
  exact sq_pos_of_pos
    (periodicHypercubicEvenBoundaryVacuumMoment_pos
      H N hN beta hbeta b)

/-- Boundary Haar measure is absolutely continuous with respect to the
strictly positive interacting boundary marginal. -/
theorem periodicHypercubicEvenBoundaryHaarMeasure_absolutelyContinuous_marginalMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryHaarMeasure H N ≪
      periodicHypercubicEvenBoundaryMarginalMeasure
        H N hN beta hbeta := by
  unfold periodicHypercubicEvenBoundaryMarginalMeasure
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  have hset :=
    (withDensity_apply_eq_zero'
      (periodicHypercubicEvenBoundaryMarginalDensity_measurable
        H N hN beta hbeta).aemeasurable).1 hzero
  have hall :
      {b | periodicHypercubicEvenBoundaryMarginalDensity
        H N hN beta hbeta b ≠ 0} = Set.univ := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact periodicHypercubicEvenBoundaryMarginalDensity_ne_zero
      H N hN beta hbeta b
  simpa [hall] using hset

/-- Haar almost-everywhere identities remain valid under the interacting
boundary marginal. -/
theorem periodicHypercubicEven_ae_boundaryHaar_to_marginal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    {α : Type u}
    {f g : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N → α}
    (h : f =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H N] g) :
    f =ᵐ[periodicHypercubicEvenBoundaryMarginalMeasure
      H N hN beta hbeta] g :=
  h.filter_mono
    (Measure.ae_le_iff_absolutelyContinuous.mpr
      (withDensity_absolutelyContinuous _ _))

/-- Marginal almost-everywhere identities remain valid under boundary Haar
because the OS boundary marginal density is strictly positive. -/
theorem periodicHypercubicEven_ae_marginal_to_boundaryHaar
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    {α : Type u}
    {f g : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N → α}
    (h : f =ᵐ[periodicHypercubicEvenBoundaryMarginalMeasure
      H N hN beta hbeta] g) :
    f =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H N] g :=
  h.filter_mono
    (Measure.ae_le_iff_absolutelyContinuous.mpr
      (periodicHypercubicEvenBoundaryHaarMeasure_absolutelyContinuous_marginalMeasure
        H N hN beta hbeta))

/-- Reciprocal-vacuum density transport as an actual interacting boundary
marginal `L²` vector. -/
noncomputable def periodicHypercubicEvenBoundaryHaarToMarginalL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta :=
  (periodicHypercubicEvenBoundaryHaarToMarginalL2Function_memLp
    H N hN beta hbeta f).toLp
    (periodicHypercubicEvenBoundaryHaarToMarginalL2Function
      H N hN beta hbeta f)

/-- The marginal representative is pointwise reciprocal-vacuum transport. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2
      H N hN beta hbeta f =ᵐ[
        periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN beta hbeta]
      periodicHypercubicEvenBoundaryHaarToMarginalL2Function
        H N hN beta hbeta f :=
  MemLp.coeFn_toLp
    (periodicHypercubicEvenBoundaryHaarToMarginalL2Function_memLp
      H N hN beta hbeta f)

/-- Reciprocal-vacuum boundary transport preserves addition. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2_add
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2
        H N hN beta hbeta (f + g) =
      periodicHypercubicEvenBoundaryHaarToMarginalL2
          H N hN beta hbeta f +
        periodicHypercubicEvenBoundaryHaarToMarginalL2
          H N hN beta hbeta g := by
  apply Lp.ext
  have hsource := periodicHypercubicEven_ae_boundaryHaar_to_marginal
    H N hN beta hbeta (Lp.coeFn_add f g)
  filter_upwards
    [periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      H N hN beta hbeta (f + g),
      periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
        H N hN beta hbeta f,
      periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
        H N hN beta hbeta g,
      Lp.coeFn_add
        (periodicHypercubicEvenBoundaryHaarToMarginalL2
          H N hN beta hbeta f)
        (periodicHypercubicEvenBoundaryHaarToMarginalL2
          H N hN beta hbeta g),
      hsource] with b hsum hf hg htarget hsrc
  rw [hsum, htarget]
  simp only [Pi.add_apply]
  rw [hf, hg]
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Function
  rw [hsrc]
  simp only [Pi.add_apply]
  ring

/-- Reciprocal-vacuum boundary transport preserves real scalar
multiplication. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2_smul
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2
        H N hN beta hbeta (r • f) =
      r • periodicHypercubicEvenBoundaryHaarToMarginalL2
        H N hN beta hbeta f := by
  apply Lp.ext
  have hsource := periodicHypercubicEven_ae_boundaryHaar_to_marginal
    H N hN beta hbeta (Lp.coeFn_smul r f)
  filter_upwards
    [periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      H N hN beta hbeta (r • f),
      periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
        H N hN beta hbeta f,
      Lp.coeFn_smul r
        (periodicHypercubicEvenBoundaryHaarToMarginalL2
          H N hN beta hbeta f),
      hsource] with b hsmul hf htarget hsrc
  rw [hsmul, htarget]
  simp only [Pi.smul_apply]
  rw [hf]
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Function
  rw [hsrc]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Reciprocal-vacuum transport as a real linear map. -/
noncomputable def periodicHypercubicEvenBoundaryHaarToMarginalL2LinearMap
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗ[ℝ]
      PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta where
  toFun := periodicHypercubicEvenBoundaryHaarToMarginalL2
    H N hN beta hbeta
  map_add' := periodicHypercubicEvenBoundaryHaarToMarginalL2_add
    H N hN beta hbeta
  map_smul' := periodicHypercubicEvenBoundaryHaarToMarginalL2_smul
    H N hN beta hbeta

/-- Reciprocal-vacuum transport preserves the boundary real `L²` inner
product exactly. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
      (periodicHypercubicEvenBoundaryHaarToMarginalL2
        H N hN beta hbeta f)
      (periodicHypercubicEvenBoundaryHaarToMarginalL2
        H N hN beta hbeta g) =
      inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def]
  unfold periodicHypercubicEvenBoundaryMarginalMeasure
  rw [integral_withDensity_eq_integral_smul₀
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal_measurable
      H N hN beta hbeta).aemeasurable]
  have hf := periodicHypercubicEven_ae_marginal_to_boundaryHaar
    H N hN beta hbeta
    (periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      H N hN beta hbeta f)
  have hg := periodicHypercubicEven_ae_marginal_to_boundaryHaar
    H N hN beta hbeta
    (periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      H N hN beta hbeta g)
  apply integral_congr_ae
  filter_upwards [hf, hg] with b hfb hgb
  rw [hfb, hgb]
  simp only [periodicHypercubicEvenBoundaryHaarToMarginalL2Function,
    smul_eq_mul, continuous_compact_oriented_real_inner_eq_mul]
  calc
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal
        H N hN beta hbeta b : ℝ) *
      ((periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
          H N hN beta hbeta b * f b) *
        (periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
          H N hN beta hbeta b * g b)) =
      ((periodicHypercubicEvenBoundaryMarginalDensityNNReal
          H N hN beta hbeta b : ℝ) *
        periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
          H N hN beta hbeta b ^ 2) * (f b * g b) := by ring
    _ = f b * g b := by
      rw [periodicHypercubicEvenBoundaryMarginalDensityNNReal_mul_weight_sq]
      simp

/-- Reciprocal-vacuum transport preserves the boundary `L²` norm. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2_norm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    ‖periodicHypercubicEvenBoundaryHaarToMarginalL2
      H N hN beta hbeta f‖ = ‖f‖ := by
  have hinner := periodicHypercubicEvenBoundaryHaarToMarginalL2_inner
    H N hN beta hbeta f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg
    (periodicHypercubicEvenBoundaryHaarToMarginalL2
      H N hN beta hbeta f), norm_nonneg f]

/-- The OS-compatible reciprocal-vacuum density change is a real linear
isometric embedding from boundary Haar `L²` into the interacting Wilson
boundary marginal `L²`. -/
noncomputable def periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta :=
  LinearIsometry.mk
    (periodicHypercubicEvenBoundaryHaarToMarginalL2LinearMap
      H N hN beta hbeta)
    (periodicHypercubicEvenBoundaryHaarToMarginalL2_norm
      H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D
