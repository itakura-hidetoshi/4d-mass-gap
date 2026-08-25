import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferRealSpectrumIsolation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryGaussLawProjection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Complex Haar-`L²` pullback by the same physical spatial lattice gauge
transformation used by the real finite Wilson carrier.  No new configuration
space, measure, or gauge action is introduced: only the scalar field of the
wavefunction is changed from `ℝ` to `ℂ`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗᵢ[ℂ]
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N γ)

/-- The complex gauge pullback has the same literal almost-everywhere
representative as the real one. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry_coeFn
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
        H N γ f =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun A => f (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) := by
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry,
    Function.comp_def] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N γ))

/-- The same physical gauge transformation acts unitarily on complex Haar
`L²`; in particular it preserves the norm exactly. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry_norm
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    ‖periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
        H N γ f‖ = ‖f‖ :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
    H N γ).norm_map f

/-- Complex Gauss-law sector on the exact same finite spatial lattice and Haar
probability space as the real physical carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule
    (H N : ℕ) :
    Submodule ℂ
      (Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) where
  carrier := {f | ∀ γ,
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
      H N γ f = f}
  zero_mem' := by
    intro γ
    exact map_zero _
  add_mem' := by
    intro f g hf hg γ
    rw [map_add, hf γ, hg γ]
  smul_mem' := by
    intro c f hf γ
    rw [map_smul, hf γ]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule_mem
    (H N : ℕ)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule H N ↔
      ∀ γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
          H N γ f = f :=
  Iff.rfl

/-- Closed complex Hilbert realization of the finite-volume Gauss-law sector.
It is the intersection of the kernels `U_γ - I`, exactly as for the real
carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule
    (H N : ℕ) :
    ClosedSubmodule ℂ
      (Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  ⨅ γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
    (⊥ : ClosedSubmodule ℂ
      (Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))).comap
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
          H N γ).toContinuousLinearMap -
        ContinuousLinearMap.id ℂ
          (Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))

/-- Membership in the closed complex carrier is literal invariance under every
physical spatial gauge pullback. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule_mem
    (H N : ℕ)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule
        H N ↔
      ∀ γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
          H N γ f = f := by
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule,
    sub_eq_zero]

/-- The closed complex carrier has exactly the underlying complex Gauss-law
submodule defined above. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule_toSubmodule_eq
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule
      H N).toSubmodule =
      periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule H N := by
  ext f
  simp

/-- Consequently the complex Gauss-law sector is closed in the complete
complex Haar Hilbert space. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule_isClosed
    (H N : ℕ) :
    IsClosed
      (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule H N :
        Set (Lp ℂ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) := by
  rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule_toSubmodule_eq]
  exact
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule
      H N).isClosed

/-- The genuine finite complex physical Hilbert carrier.  This is an
abbreviation of the closed gauge-invariant subspace of complex Haar `L²`, not
a prototype or an unrelated complex vector space. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert
    (H N : ℕ) : Type :=
  periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule H N

/-- Canonical orthogonal Gauss-law projection on the complex Haar Hilbert
space. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaussLawProjection
    (H N : ℕ) :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℂ]
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule
    H N).starProjection

/-- The complex Gauss-law projector fixes exactly the complex physical
vectors. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaussLawProjection_eq_self_iff
    (H N : ℕ)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaussLawProjection H N f = f ↔
      f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule
        H N := by
  change
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule
      H N).starProjection f = f ↔ _
  rw [Submodule.starProjection_eq_self_iff]
  simp

/-- The range of the complex orthogonal Gauss-law projection is exactly the
complex physical Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaussLawProjection_range
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaussLawProjection H N).range =
      periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule H N := by
  change
    ((periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule
      H N).starProjection).range = _
  rw [Submodule.range_starProjection]
  exact
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2ClosedSubmodule_toSubmodule_eq
      H N

local instance periodicHypercubicEvenSpecialUnitaryComplexGaussLawHaar_isProbability
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The constant-one complex Haar vector is fixed by every actual lattice
gauge transformation. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullback_const_one
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry H N γ
        (Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℂ)) =
      Lp.const 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℂ) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let oneL2 : Lp ℂ 2 μ := Lp.const 2 μ (1 : ℂ)
  apply Lp.ext
  have hPull :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry_coeFn
      H N γ oneL2
  have hConst : oneL2 =ᵐ[μ] fun _ => (1 : ℂ) := by
    simpa [oneL2] using
      (Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℂ)))
  have hConstPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H N γ).quasiMeasurePreserving.ae_eq hConst
  filter_upwards [hPull, hConstPull, hConst] with A hpull hpulled hone
  calc
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
        H N γ oneL2 A =
      oneL2 (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) := hpull
    _ = 1 := by simpa using hpulled
    _ = oneL2 A := by simpa using hone.symm

/-- Canonical complex physical unit vector, witnessing nontriviality without
introducing any extra state space. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalConstantUnitVector
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  ⟨Lp.const 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℂ), by
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule_mem]
    intro γ
    exact periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullback_const_one H N γ⟩

/-- The canonical complex Gauss-law vector has unit Haar-`L²` norm. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalConstantUnitVector_norm
    (H N : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalConstantUnitVector H N‖ = 1 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change ‖Lp.const 2 μ (1 : ℂ)‖ = 1
  simpa [measureReal_def] using
    (Lp.norm_const (μ := μ) (p := 2) (c := (1 : ℂ)) (by norm_num))

/-- The complex physical carrier is complete because it is a closed subspace
of complex Haar `L²`.  Kept as a named constructor so downstream spectral
files can install it locally without a global instance diamond. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- Audit-visible receipt that the complex Hilbert carrier is the genuine
complex-valued Gauss-law sector over the very same finite Wilson configuration
space and Haar probability measure. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexGaussLawHilbertPackage
    (H N : ℕ) : Prop where
  closed :
    IsClosed
      (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule H N :
        Set (Lp ℂ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  pullbackIsometric :
    ∀ (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
      (f : Lp ℂ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)),
      ‖periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
          H N γ f‖ = ‖f‖
  projectorRange :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaussLawProjection H N).range =
      periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule H N
  referenceUnit :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalConstantUnitVector H N‖ = 1

/-- Construct the complex finite Wilson Gauss-law Hilbert package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexGaussLawHilbertPackage
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryComplexGaussLawHilbertPackage H N :=
  { closed :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule_isClosed
        H N
    pullbackIsometric :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry_norm
        H N
    projectorRange :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaussLawProjection_range H N
    referenceUnit :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalConstantUnitVector_norm H N }

end
end MathlibAnalytic
end MGAP4D
