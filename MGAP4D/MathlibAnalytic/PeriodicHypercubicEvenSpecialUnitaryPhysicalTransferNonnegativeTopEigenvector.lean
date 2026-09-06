import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenvector
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

/-- Canonical pointwise absolute value on a real `L²` class, assembled from
Mathlib's positive and negative parts. -/
noncomputable def realL2Abs
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  Lp.posPart f + Lp.negPart f

/-- The canonical `L²` absolute value has the expected almost-everywhere
representative. -/
theorem realL2Abs_coeFn
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) :
    realL2Abs f =ᵐ[μ] fun x => |f x| := by
  filter_upwards [Lp.coeFn_add (Lp.posPart f) (Lp.negPart f),
    Lp.coeFn_posPart f, Lp.coeFn_negPart_eq_max f] with x hadd hpos hneg
  change (Lp.posPart f + Lp.negPart f : Lp ℝ 2 μ) x = |f x|
  rw [hadd, hpos, hneg]
  by_cases hx : 0 ≤ f x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
    ring
  · have hx' : f x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), abs_of_nonpos hx']
    ring

/-- Taking pointwise absolute value preserves the real `L²` norm. -/
theorem realL2Abs_norm
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) :
    ‖realL2Abs f‖ = ‖f‖ := by
  have hsq : ‖realL2Abs f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [realL2_norm_sq_eq_integral_norm_sq,
      realL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [realL2Abs_coeFn f] with x hx
    rw [hx]
    simp [Real.norm_eq_abs]
  have hleft : 0 ≤ ‖realL2Abs f‖ := norm_nonneg _
  have hright : 0 ≤ ‖f‖ := norm_nonneg _
  nlinarith

/-- The canonical absolute-value representative is nonnegative almost
everywhere. -/
theorem realL2Abs_ae_nonnegative
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, 0 ≤ realL2Abs f x :=
  (realL2Abs_coeFn f).mono fun x hx => by
    rw [hx]
    exact abs_nonneg _

/-- A nonnegative real Hilbert--Schmidt kernel can only increase its diagonal
quadratic pairing after replacing a test vector by its pointwise absolute
value. -/
theorem realL2HilbertSchmidtKernelPairing_le_abs
    {α : Type u} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (hK : ∀ᵐ z ∂(μ.prod μ), 0 ≤ K z)
    (f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtKernelPairing K f f ≤
      realL2HilbertSchmidtKernelPairing K (realL2Abs f) (realL2Abs f) := by
  rw [realL2HilbertSchmidtKernelPairing,
    realL2HilbertSchmidtKernelPairing,
    MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def]
  apply integral_mono_ae
  · exact MeasureTheory.L2.integrable_inner K (realL2ExternalTensor f f)
  · exact MeasureTheory.L2.integrable_inner K
      (realL2ExternalTensor (realL2Abs f) (realL2Abs f))
  · have habsFst :
        (fun z : α × α => realL2Abs f z.1) =ᵐ[μ.prod μ]
          fun z => |f z.1| := by
      simpa [Function.comp_def] using
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq
          (realL2Abs_coeFn f)
    have habsSnd :
        (fun z : α × α => realL2Abs f z.2) =ᵐ[μ.prod μ]
          fun z => |f z.2| := by
      simpa [Function.comp_def] using
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq
          (realL2Abs_coeFn f)
    filter_upwards [hK,
      realL2ExternalTensor_coeFn f f,
      realL2ExternalTensor_coeFn (realL2Abs f) (realL2Abs f),
      habsFst, habsSnd] with z hk hff haa haf has
    rw [hff, haa]
    simp only [realL2ExternalTensorFunction]
    rw [haf, has]
    simp only [RCLike.inner_apply, conj_trivial]
    apply mul_le_mul_of_nonneg_right _ hk
    calc
      f z.1 * f z.2 ≤ |f z.1 * f z.2| := le_abs_self _
      _ = |f z.1| * |f z.2| := abs_mul _ _

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

/-- Spatial gauge pullback commutes with the canonical real `L²` absolute
value.  This is the key order-theoretic fact showing that the Gauss-law sector
is closed under `f ↦ |f|`. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_realL2Abs
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
        (realL2Abs f) =
      realL2Abs
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ f) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let G := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ
  let U := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
  apply Lp.ext
  have hLeft :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ (realL2Abs f)
  have hAbsPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H N γ).quasiMeasurePreserving.ae_eq (realL2Abs_coeFn f)
  have hUf :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ f
  have hRight := realL2Abs_coeFn (U f)
  filter_upwards [hLeft, hAbsPull, hUf, hRight] with A hleft habspull huf hright
  calc
    U (realL2Abs f) A = realL2Abs f (G A) := by simpa [μ, G, U] using hleft
    _ = |f (G A)| := by simpa [G] using habspull
    _ = |U f A| := by rw [huf]
    _ = realL2Abs (U f) A := hright.symm

/-- Absolute value as an endomorphism of the actual finite-volume Gauss-law
Hilbert carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ⟨realL2Abs
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)), by
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem]
    intro γ
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_realL2Abs]
    rw [f.property γ]⟩

/-- Physical absolute value preserves norm exactly. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_norm
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N f‖ = ‖f‖ := by
  change
    ‖realL2Abs
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ = ‖f‖
  exact realL2Abs_norm
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Physical absolute value has a nonnegative Haar-`L²` representative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_ae_nonnegative
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 ≤ (periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N f).1 A :=
  realL2Abs_ae_nonnegative
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- The actual Wilson one-slab kernel is strictly positive also at the level of
its product-Haar `L²` representative. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_ae_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ᵐ z ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N),
      0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta z :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
    H N hN beta hbeta).mono fun z hz => by
      change 0 <
        (fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta p) z
      rw [hz]
      exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta z.1 z.2

/-- The actual ambient one-slab Wilson transfer quadratic form increases under
pointwise absolute value. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_le_abs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) f ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta (realL2Abs f)) (realL2Abs f) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]
  exact realL2HilbertSchmidtKernelPairing_le_abs
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta)
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_ae_pos
      H N hN beta hbeta).mono fun _ hz => hz.le)
    f

/-- The same absolute-value domination holds on the actual Gauss-law physical
transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_le_abs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f) f ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N f))
        (periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N f) := by
  change inner ℝ
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≤
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (realL2Abs
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))))
      (realL2Abs
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_le_abs
    H N hN beta hbeta
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- A canonical normalized nonnegative vacuum candidate obtained by taking the
pointwise absolute value of the already constructed physical top eigenvector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta)

/-- The nonnegative vacuum candidate remains normalized. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta‖ = 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector,
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_norm,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm]

/-- The chosen absolute-value vacuum has a nonnegative representative almost
everywhere with respect to the actual spatial-slice Haar probability. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_ae_nonnegative H N
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta)

/-- The nonnegative vacuum candidate still attains the top physical Rayleigh
value and therefore is itself a top eigenvector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta
  let Ωa := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  have hΩnorm : ‖Ω‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H N hN beta hbeta
  have hΩanorm : ‖Ωa‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H N hN beta hbeta
  have hΩeig : T Ω = ‖T‖ • Ω := by
    simpa [T, Ω] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
        H N hN beta hbeta
  have hΩquad : inner ℝ (T Ω) Ω = ‖T‖ := by
    rw [hΩeig, real_inner_smul_left, real_inner_self_eq_norm_sq, hΩnorm]
    ring
  have hdom : inner ℝ (T Ω) Ω ≤ inner ℝ (T Ωa) Ωa := by
    simpa [T, Ω, Ωa] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_le_abs
        H N hN beta hbeta Ω
  have hinnerBound : inner ℝ (T Ωa) Ωa ≤ ‖T Ωa‖ * ‖Ωa‖ :=
    real_inner_le_norm _ _
  have hquadUpper : inner ℝ (T Ωa) Ωa ≤ ‖T‖ := by
    calc
      inner ℝ (T Ωa) Ωa ≤ ‖T Ωa‖ * ‖Ωa‖ := hinnerBound
      _ ≤ (‖T‖ * ‖Ωa‖) * ‖Ωa‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm Ωa) (norm_nonneg Ωa)
      _ = ‖T‖ := by rw [hΩanorm]; ring
  have hΩaquad : inner ℝ (T Ωa) Ωa = ‖T‖ := by
    apply le_antisymm hquadUpper
    rw [← hΩquad]
    exact hdom
  have hTΩa_le : ‖T Ωa‖ ≤ ‖T‖ := by
    calc
      ‖T Ωa‖ ≤ ‖T‖ * ‖Ωa‖ := T.le_opNorm Ωa
      _ = ‖T‖ := by rw [hΩanorm, mul_one]
  have hT_le : ‖T‖ ≤ ‖T Ωa‖ := by
    calc
      ‖T‖ = inner ℝ (T Ωa) Ωa := hΩaquad.symm
      _ ≤ ‖T Ωa‖ * ‖Ωa‖ := real_inner_le_norm _ _
      _ = ‖T Ωa‖ := by rw [hΩanorm, mul_one]
  have hTΩa_norm : ‖T Ωa‖ = ‖T‖ := le_antisymm hTΩa_le hT_le
  have hCS : inner ℝ (T Ωa) Ωa = ‖T Ωa‖ * ‖Ωa‖ := by
    rw [hΩaquad, hTΩa_norm, hΩanorm, mul_one]
  have halign := (inner_eq_norm_mul_iff_real).1 hCS
  rw [hΩanorm, hTΩa_norm, one_smul] at halign
  simpa [T, Ωa] using halign

/-- Audit-visible receipt: the actual physical one-slab Wilson transfer admits
a normalized top eigenvector with a nonnegative Haar-`L²` representative,
without assuming positivity of the previously chosen abstract eigenvector. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  unit :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta‖ = 1
  aeNonnegative :
    ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A
  topEigen :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta

/-- Construct the nonnegative physical top-eigenvector receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvectorPackage
      H N hN beta hbeta :=
  { unit :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
        H N hN beta hbeta
    aeNonnegative :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H N hN beta hbeta
    topEigen :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
