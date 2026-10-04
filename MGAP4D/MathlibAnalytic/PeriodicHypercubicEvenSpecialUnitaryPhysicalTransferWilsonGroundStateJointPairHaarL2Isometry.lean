import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasureEquivalence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePair
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Pair-Haar to ground-state joint L² half-density isometry

The genuine finite-volume ground-state one-slab law is

  dπ(z) = w(z) d(μ ⊗ μ)(z),

where `w` is the normalized joint weight.  Existing results prove

* `w` is integrable,
* `w > 0` pair-Haar almost everywhere,
* `π` is exactly `withDensity (ofReal w)`.

Therefore no uniform upper or lower density bound is needed to compare the
Hilbert carriers.  The half-density transform

  f ↦ f / sqrt(w)

is an exact real-linear isometry from ordered pair-Haar `L²` into the genuine
ground-state joint `L²`; the cancellation is simply

  w * |f / sqrt(w)|² = |f|²

almost everywhere.

This is a Hilbert-space change of measure only.  It does not identify the
ground-state conditional expectation with the physical transfer operator and
does not introduce any H1-D5-style exact descent.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct ENNReal

noncomputable section

local instance groundStateJointPairHaarL2IsometryTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointPairHaarL2IsometryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointPairHaarL2IsometrySecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointPairHaarL2IsometryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointPairHaarL2IsometryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointPairHaarL2IsometrySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The pointwise square-root of the normalized ground-state joint density. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  Real.sqrt
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta z)

/-- The square-root joint density is strictly positive pair-Haar almost
everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity_ae_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ᵐ z ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N),
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
          H N hN beta hbeta z := by
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
      H N hN beta hbeta] with z hz
  exact Real.sqrt_pos.2 hz

/-- Representative-level inverse-half-density transform from pair Haar to the
genuine ground-state joint law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  f z /
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
      H N hN beta hbeta z

/-- The inverse-half-density representative belongs to ground-state joint
`L²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction_memLp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
        H N hN beta hbeta f)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta
  let sqrtw := fun z =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
      H N hN beta hbeta z
  let u := fun z => f z / sqrtw z
  let rho := fun z => ENNReal.ofReal (w z)
  have hwStrong : AEStronglyMeasurable w μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
      H N hN beta hbeta).aestronglyMeasurable
  have hsqrtStrong : AEStronglyMeasurable sqrtw μ := by
    dsimp [sqrtw,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hwStrong
  have huStrongμ : AEStronglyMeasurable u μ := by
    exact (Lp.aestronglyMeasurable f).div₀ hsqrtStrong
  have hrhoAE : AEMeasurable rho μ := by
    exact hwStrong.aemeasurable.ennreal_ofReal
  have hrhoTop : ∀ᵐ z ∂μ, rho z < (⊤ : ENNReal) := by
    filter_upwards with z
    simp [rho]
  have hνac : μ.withDensity rho ≪ μ :=
    withDensity_absolutelyContinuous _ _
  have huStrongν : AEStronglyMeasurable u (μ.withDensity rho) :=
    huStrongμ.mono_ac hνac
  have hwpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
      H N hN beta hbeta
  have huSqInt : Integrable (fun z => u z ^ 2) (μ.withDensity rho) := by
    rw [integrable_withDensity_iff_integrable_smul₀' hrhoAE hrhoTop]
    apply (Lp.memLp f).integrable_sq.congr
    filter_upwards [hwpos] with z hz
    have hsqrtpos : 0 < sqrtw z := by
      dsimp [sqrtw,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity]
      exact Real.sqrt_pos.2 hz
    have hsqrtne : sqrtw z ≠ 0 := ne_of_gt hsqrtpos
    simp only [smul_eq_mul]
    dsimp [rho, u]
    rw [ENNReal.toReal_ofReal hz.le]
    have hsqrt_sq :
        sqrtw z ^ 2 =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta z := by
      dsimp [sqrtw,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity]
      exact Real.sq_sqrt hz.le
    rw [← hsqrt_sq]
    field_simp [hsqrtne]
  change MemLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
      H N hN beta hbeta f) 2 (μ.withDensity rho)
  have huMem : MemLp u 2 (μ.withDensity rho) :=
    (memLp_two_iff_integrable_sq huStrongν).2 huSqInt
  simpa [u, sqrtw, w, rho,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure] using huMem

/-- Inverse-half-density transport as an actual joint `L²` vector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction_memLp
    H N hN beta hbeta f).toLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
      H N hN beta hbeta f)

/-- The transported `L²` vector has the expected representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta f =ᵐ[
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
        H N hN beta hbeta f :=
  MemLp.coeFn_toLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction_memLp
      H N hN beta hbeta f)

/-- The half-density transport preserves addition. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta (f + g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
          H N hN beta hbeta f +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
          H N hN beta hbeta g := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  have hνμ : ν ≪ μ := by
    simpa [ν, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
        H N hN beta hbeta
  apply Lp.ext
  have hfg : ⇑(f + g) =ᵐ[ν] f + g :=
    hνμ.ae_eq (Lp.coeFn_add f g)
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
      H N hN beta hbeta (f + g),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
        H N hN beta hbeta f,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
        H N hN beta hbeta g,
      Lp.coeFn_add
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
          H N hN beta hbeta g),
      hfg] with z hsum hf hg htarget hsrc
  rw [hsum, htarget]
  simp only [Pi.add_apply]
  rw [hf, hg]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
  simp only [Pi.add_apply] at hsrc
  rw [hsrc]
  ring

/-- The half-density transport preserves real scalar multiplication. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_smul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : ℝ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta (c • f) =
      c •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
          H N hN beta hbeta f := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  have hνμ : ν ≪ μ := by
    simpa [ν, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
        H N hN beta hbeta
  apply Lp.ext
  have hcf : ⇑(c • f) =ᵐ[ν] c • f :=
    hνμ.ae_eq (Lp.coeFn_smul c f)
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
      H N hN beta hbeta (c • f),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
        H N hN beta hbeta f,
      Lp.coeFn_smul c
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
          H N hN beta hbeta f),
      hcf] with z hsmul hf htarget hsrc
  rw [hsmul, htarget]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hf]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
  simp only [Pi.smul_apply, smul_eq_mul] at hsrc
  rw [hsrc]
  ring

/-- Inverse-half-density transport preserves the squared `L²` norm exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta f‖ ^ 2 = ‖f‖ ^ 2 := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta
  let sqrtw := fun z =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
      H N hN beta hbeta z
  let u := fun z => f z / sqrtw z
  let rho := fun z => ENNReal.ofReal (w z)
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
      H N hN beta hbeta f
  have hUrep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
      H N hN beta hbeta f
  have hwStrong : AEStronglyMeasurable w μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
      H N hN beta hbeta).aestronglyMeasurable
  have hrhoAE : AEMeasurable rho μ :=
    hwStrong.aemeasurable.ennreal_ofReal
  have hrhoTop : ∀ᵐ z ∂μ, rho z < (⊤ : ENNReal) := by
    filter_upwards with z
    simp [rho]
  have hwpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
      H N hN beta hbeta
  have hInt :
      (∫ z, ‖U z‖ ^ 2 ∂(μ.withDensity rho)) =
        ∫ z, ‖f z‖ ^ 2 ∂μ := by
    calc
      (∫ z, ‖U z‖ ^ 2 ∂(μ.withDensity rho)) =
          ∫ z, u z ^ 2 ∂(μ.withDensity rho) := by
        apply integral_congr_ae
        have hrep : U =ᵐ[μ.withDensity rho] u := by
          simpa [U, u, sqrtw, w, rho,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure] using hUrep
        filter_upwards [hrep] with z hz
        rw [hz]
        simp [Real.norm_eq_abs, sq_abs]
      _ = ∫ z, (rho z).toReal • (u z ^ 2) ∂μ := by
        exact integral_withDensity_eq_integral_toReal_smul₀ hrhoAE hrhoTop _
      _ = ∫ z, ‖f z‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hwpos] with z hz
        have hsqrtpos : 0 < sqrtw z := by
          dsimp [sqrtw,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity]
          exact Real.sqrt_pos.2 hz
        have hsqrtne : sqrtw z ≠ 0 := ne_of_gt hsqrtpos
        simp only [smul_eq_mul]
        dsimp [rho, u]
        rw [ENNReal.toReal_ofReal hz.le]
        have hsqrt_sq :
            sqrtw z ^ 2 =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
                H N hN beta hbeta z := by
          dsimp [sqrtw,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity]
          exact Real.sq_sqrt hz.le
        rw [← hsqrt_sq]
        field_simp [hsqrtne]
        simp [Real.norm_eq_abs, sq_abs]
  rw [realL2_norm_sq_eq_integral_norm_sq U,
    realL2_norm_sq_eq_integral_norm_sq f]
  change
    (∫ z, ‖U z‖ ^ 2 ∂(μ.withDensity rho)) =
      ∫ z, ‖f z‖ ^ 2 ∂μ
  exact hInt

/-- Inverse-half-density transport preserves the `L²` norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta f‖ = ‖f‖ := by
  have hsq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_norm_sq
      H N hN beta hbeta f
  nlinarith [
    norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta f),
    norm_nonneg f]

/-- The exact inverse-half-density Hilbert-space embedding from pair Haar to the
genuine ground-state joint `L²` carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2LinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) where
  toFun :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
      H N hN beta hbeta
  map_add' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_add
      H N hN beta hbeta
  map_smul' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_smul
      H N hN beta hbeta
  norm_map' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_norm
      H N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
