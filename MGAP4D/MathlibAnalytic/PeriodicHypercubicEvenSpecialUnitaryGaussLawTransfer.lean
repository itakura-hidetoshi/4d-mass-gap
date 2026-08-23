import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryGaussLawProjection
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

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

/-- Simultaneous gauge action on the two adjacent spatial boundaries. -/
def periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Prod.map
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ)

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform_apply
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform H N γ p =
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ p.1,
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ p.2) :=
  rfl

/-- Simultaneous boundary gauge transformation preserves the product Haar
probability measure. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_measurePreserving
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform H N γ)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  exact
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N γ).prod
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N γ)

/-- Haar-`L²` pullback on the pair of adjacent spatial boundaries. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) →ₗᵢ[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform H N γ)
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_measurePreserving H N γ)

/-- The one-slice pullback has the expected almost-everywhere representative. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ f =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun A => f (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) := by
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry,
    Function.comp_def] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N γ))

/-- The pair pullback has the expected almost-everywhere representative. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry_coeFn
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (F : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry H N γ F =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      fun p => F (periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform H N γ p) := by
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry,
    Function.comp_def] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving F
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_measurePreserving H N γ))

/-- The literal one-slab kernel, viewed as a product-Haar `L²` vector, is fixed
by simultaneous gauge pullback on its two boundary variables. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_gaugeFixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta := by
  apply Lp.ext
  let K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta
  have hPull :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry_coeFn
      H N γ K
  have hK :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta
  have hKPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_measurePreserving
      H N γ).quasiMeasurePreserving.ae_eq hK
  filter_upwards [hPull, hKPull, hK] with p hpull hkpull hkp
  rw [hpull, hkpull, hkp]
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_gaugeInvariant
    H N beta γ p.1 p.2

/-- External tensors intertwine one-slice gauge pullback with simultaneous
pair-space gauge pullback. -/
theorem periodicHypercubicEvenSpecialUnitaryRealL2ExternalTensor_gaugePullback
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ g) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry
        H N γ (realL2ExternalTensor f g) := by
  apply Lp.ext
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let U := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
  let G := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ
  let Upair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry H N γ
  have hLeft := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) (U f) (U g)
  have hf := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
    H N γ f
  have hg := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
    H N γ g
  have hfPair :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        U f p.1) =ᵐ[μ.prod μ] fun p => f (G p.1) := by
    simpa [μ, U, G, Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hf
  have hgPair :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        U g p.2) =ᵐ[μ.prod μ] fun p => g (G p.2) := by
    simpa [μ, U, G, Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hg
  have hRight :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry_coeFn
      H N γ (realL2ExternalTensor f g)
  have hTensor := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) f g
  have hTensorPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_measurePreserving
      H N γ).quasiMeasurePreserving.ae_eq hTensor
  filter_upwards [hLeft, hfPair, hgPair, hRight, hTensorPull] with p hleft hfp hgp hright htensor
  rw [hleft, hright, htensor]
  simp only [realL2ExternalTensorFunction]
  rw [hfp, hgp]
  rfl

/-- The complete actual one-slab Hilbert--Schmidt pairing is invariant when
both test vectors are pulled back by the same spatial lattice gauge
transformation. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_gaugeInvariant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ g) =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta) f g := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta
  let Upair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry H N γ
  rw [realL2HilbertSchmidtKernelPairing, realL2HilbertSchmidtKernelPairing]
  rw [periodicHypercubicEvenSpecialUnitaryRealL2ExternalTensor_gaugePullback H N γ f g]
  rw [← periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_gaugeFixed
    H N hN beta hbeta γ]
  exact Upair.inner_map_map K (realL2ExternalTensor f g)

/-- Pullback by the inverse gauge transformation is a left inverse on Haar
`L²`. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_inv_apply
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ⁻¹
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ f) =
      f := by
  apply Lp.ext
  have hOuter :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ⁻¹
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ f)
  have hInner :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ f
  have hInnerPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H N γ⁻¹).quasiMeasurePreserving.ae_eq hInner
  filter_upwards [hOuter, hInnerPull] with A houter hinner
  rw [houter, hinner]
  rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_mul]
  simp

/-- Pullback by a gauge transformation is also a left inverse to pullback by
its inverse. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_apply_inv
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ⁻¹ f) =
      f := by
  simpa using
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_inv_apply H N γ⁻¹ f

/-- The actual one-slab transfer commutes with every finite-volume spatial
lattice gauge pullback. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_gauge_commute_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ f) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) := by
  apply ext_inner_right ℝ
  intro g
  let U := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
  let Uinv := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ⁻¹
  have hg : U (Uinv g) = g := by
    exact periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_apply_inv H N γ g
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta (U f)) g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta (U f)) (U (Uinv g)) := by rw [hg]
    _ = realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta) (U f) (U (Uinv g)) :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
        H N hN beta hbeta (U f) (U (Uinv g))
    _ = realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta) f (Uinv g) :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_gaugeInvariant
        H N hN beta hbeta γ f (Uinv g)
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) (Uinv g) :=
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
        H N hN beta hbeta f (Uinv g)).symm
    _ = inner ℝ
        (U (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f)) (U (Uinv g)) := by
      symm
      exact U.inner_map_map
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) (Uinv g)
    _ = inner ℝ
        (U (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f)) g := by rw [hg]

/-- Operator-level commutation with every spatial gauge pullback. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_gauge_commute
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H N γ).toContinuousLinearMap =
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H N γ).toContinuousLinearMap.comp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta) := by
  apply ContinuousLinearMap.ext
  intro f
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_gauge_commute_apply
    H N hN beta hbeta γ f

/-- The actual one-slab transfer preserves the finite-volume Gauss-law physical
subspace. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLaw
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)}
    (hf : f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta f ∈
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem] at hf ⊢
  intro γ
  rw [← periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_gauge_commute_apply
    H N hN beta hbeta γ f]
  rw [hf γ]

/-- By symmetry, the transfer also preserves the orthogonal complement of the
Gauss-law sector. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLawOrthogonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)}
    (hf : f ∈
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)ᗮ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta f ∈
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro g hg
  rw [real_inner_comm]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isSymmetric
    H N hN beta hbeta f g]
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal f).1 hf
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta g)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLaw
      H N hN beta hbeta hg)

/-- The actual one-slab transfer commutes with the orthogonal Gauss-law
projection. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_GaussLawProjection_commute_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f) := by
  let K := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  let P := periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  have hTP : T (P f) ∈ K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLaw
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_mem H N f)
  have hrem : f - P f ∈ Kᗮ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlice_sub_GaussLawProjection_mem_orthogonal
      H N f
  have hTrem : T (f - P f) ∈ Kᗮ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLawOrthogonal
      H N hN beta hbeta hrem
  have hdiff : T f - T (P f) ∈ Kᗮ := by
    simpa using hTrem
  change
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
      H N).starProjection (T f) = T (P f)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · simpa [K] using hTP
  · simpa [K] using hdiff

/-- Operator-level commutation with the orthogonal Gauss-law projection. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_GaussLawProjection_commute
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N).comp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta) =
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N) := by
  apply ContinuousLinearMap.ext
  intro f
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_GaussLawProjection_commute_apply
      H N hN beta hbeta f

/-- The physical finite-volume one-slab transfer obtained by restricting the
actual Haar-`L²` transfer to the Gauss-law fixed Hilbert sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta).restrict
      (fun f hf =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLaw
          H N hN beta hbeta hf)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta f :=
  rfl

/-- The restricted physical transfer remains symmetric. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsSymmetric := by
  intro f g
  change inner ℝ
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta f) g =
    inner ℝ f
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta g)
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta f g

/-- The restricted physical transfer remains positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive := by
  rw [LinearMap.isPositive_iff]
  refine ⟨periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
    H N hN beta hbeta, ?_⟩
  intro f
  have hAmbient :=
    (LinearMap.isPositive_iff.mp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isPositive
        H N hN beta hbeta)).2 (f :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  exact hAmbient

/-- Audit-visible finite-volume physical transfer package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  gaugeCommutes :
    ∀ γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta).comp
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ).toContinuousLinearMap =
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ).toContinuousLinearMap.comp
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta)
  preservesPhysical :
    ∀ {f},
      f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f ∈
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  projectionCommutes :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N).comp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta) =
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N)
  physicalSymmetric :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsSymmetric
  physicalPositive :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive

/-- Construct the complete finite-volume physical one-slab transfer receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferPackage
      H N hN beta hbeta :=
  { gaugeCommutes :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_gauge_commute
        H N hN beta hbeta
    preservesPhysical :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLaw
        H N hN beta hbeta
    projectionCommutes :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_GaussLawProjection_commute
        H N hN beta hbeta
    physicalSymmetric :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta
    physicalPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
