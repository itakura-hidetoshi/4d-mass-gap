import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2TransferFactorization
import MGAP4D.MathlibAnalytic.CompactGaugeWilsonGaugeInvariance
import Mathlib.MeasureTheory.Function.LpSpace.Basic
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

/-- Gauge transformations living on the actual vertices of one modern
spatial time slice. -/
abbrev PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation
    (H N : ℕ) : Type :=
  PeriodicHypercubicEvenSpatialSliceVertex H →
    Matrix.specialUnitaryGroup (Fin N) ℂ

/-- Actual lattice gauge action on a spatial-slice configuration. -/
def periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  fun e =>
    γ e.1 * A e *
      (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_apply
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A e =
      γ e.1 * A e *
        (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹ :=
  rfl

/-- Independent spatial unit translations commute inside the slice. -/
theorem periodicHypercubicEvenSpatialSliceShift_comm
    (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu nu : PeriodicHypercubicEvenSpatialDirection) :
    periodicHypercubicEvenSpatialSliceShift H
        (periodicHypercubicEvenSpatialSliceShift H v mu) nu =
      periodicHypercubicEvenSpatialSliceShift H
        (periodicHypercubicEvenSpatialSliceShift H v nu) mu := by
  apply Subtype.ext
  exact periodicHypercubicShift_comm
    (PeriodicHypercubicEvenSideLength H) v.1 mu.1 nu.1

/-- The identity gauge transformation acts trivially. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_one
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N
        (1 : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) A = A := by
  funext e
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform]

/-- Pointwise multiplication of vertex gauge transformations gives the
expected composition law. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_mul
    (H N : ℕ)
    (γ δ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N (γ * δ) A =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N δ A) := by
  funext e
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform]
  group

/-- A spatial plaquette holonomy transforms by conjugation at its base vertex. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_gaugeTransform
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) p =
      γ p.1 * periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p * (γ p.1)⁻¹ := by
  unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
  simp only [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_apply]
  rw [periodicHypercubicEvenSpatialSliceShift_comm H p.1 p.2.1.1 p.2.1.2]
  group

/-- The intrinsic spatial Wilson action is gauge invariant. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  simp_rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_gaugeTransform]
  simp_rw [specialUnitaryWilsonPlaquetteEnergy_conjInvariant]

/-- Spatial half-Boltzmann weights are gauge invariant. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_gaugeInvariant
    (H N : ℕ)
    (beta : ℝ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant]

/-- On every link, the relative boundary variable transforms by conjugation at
the target vertex. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_relative
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ((periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A e)⁻¹ *
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B e) =
      γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) *
        ((A e)⁻¹ * B e) *
        (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹ := by
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform]
  group

/-- The temporal-gauge crossing action is invariant under the same gauge
transformation on both adjacent boundaries. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_gaugeInvariant
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  simp_rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_relative]
  simp_rw [specialUnitaryWilsonPlaquetteEnergy_conjInvariant]

/-- The product crossing kernel is simultaneously gauge invariant. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_gaugeInvariant
    (H N : ℕ)
    (beta : ℝ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H N beta
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H N beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_gaugeInvariant]

/-- The complete symmetric one-slab action is simultaneously gauge invariant. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_gaugeInvariant
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_gaugeInvariant,
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant]

/-- The actual complete one-slab Wilson kernel is simultaneously gauge
invariant on its two spatial boundaries. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_gaugeInvariant
    (H N : ℕ)
    (beta : ℝ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_gaugeInvariant,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_gaugeInvariant,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_gaugeInvariant]

/-- Every individual link-coordinate gauge action preserves normalized compact
Haar probability. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeLink_measurePreserving
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    MeasurePreserving
      (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        γ e.1 * x *
          (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  normalizedCompactHaar_measurePreserving_mul_left_right
    (Matrix.specialUnitaryGroup (Fin N) ℂ)
    (γ e.1)
    (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹

/-- The full spatial-slice lattice gauge action preserves the actual product
Haar probability measure used by the one-slab transfer. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  refine ⟨?_, ?_⟩
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
    fun_prop
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    let f : PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ →
          Matrix.specialUnitaryGroup (Fin N) ℂ :=
      fun e x =>
        γ e.1 * x *
          (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹
    have hf : ∀ e, AEMeasurable (f e)
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
      fun e =>
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeLink_measurePreserving
          H N γ e).measurable.aemeasurable
    letI : ∀ e, SigmaFinite
        ((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).map (f e)) :=
      fun e => by
        rw [(periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeLink_measurePreserving
          H N γ e).map_eq]
        infer_instance
    rw [show periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ =
        (fun A e => f e (A e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeLink_measurePreserving
        H N γ e).map_eq

/-- Haar-`L²` pullback by a spatial lattice gauge transformation.  Because the
actual product Haar measure is preserved, this is an isometric linear action on
the complete one-slice Hilbert space. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗᵢ[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N γ)

/-- The pullback isometry preserves the complete Haar-`L²` norm exactly. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_norm
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    ‖periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ f‖ =
      ‖f‖ :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ).norm_map f

/-- Linear Gauss-law invariant sector: vectors fixed by every actual spatial
lattice gauge pullback.  Closedness/projection is deliberately left for the
next Hilbert-subspace unit. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
    (H N : ℕ) :
    Submodule ℝ
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) where
  carrier := {f | ∀ γ,
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
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

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem
    (H N : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N ↔
      ∀ γ,
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ f = f :=
  Iff.rfl

/-- Audit-visible receipt for the new finite-volume Gauss-law preparation
layer. -/
structure PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeActionPackage
    (H N : ℕ) : Prop where
  haarPreserving :
    ∀ γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
      MeasurePreserving
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
  oneSlabKernelInvariant :
    ∀ (beta : ℝ)
      (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
      (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B) =
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B
  pullbackIsometry :
    ∀ (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)),
      ‖periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ f‖ = ‖f‖

/-- Construct the finite-volume Gauss-law preparation receipt. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeActionPackage
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeActionPackage H N :=
  { haarPreserving :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N
    oneSlabKernelInvariant :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_gaugeInvariant H N
    pullbackIsometry :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_norm H N }

end

end MathlibAnalytic
end MGAP4D
