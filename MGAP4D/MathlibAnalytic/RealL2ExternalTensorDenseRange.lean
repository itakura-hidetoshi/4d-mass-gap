import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorCore
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Tactic

/-!
# Density of algebraic external tensors in real product-Haar L²

For finite measures `μ` and `ν`, the canonical algebraic external-tensor
realization

`L²(μ) ⊗ L²(ν) → L²(μ × ν)`

has dense range.

The proof is deliberately measure-theoretic and uses only native Mathlib:

1. product indicators are literal external tensors of one-factor indicators;
2. if `K` is orthogonal to the external-tensor range, its integral over every
   measurable rectangle vanishes;
3. measurable rectangles form a π-system generating the product σ-algebra;
4. `MeasurableSpace.induction_on_inter` propagates the vanishing set integral
   to every measurable set;
5. `Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero` gives `K = 0` a.e.;
6. the Hilbert-space orthogonal-complement criterion gives density.

This is the analytic completion ingredient needed after the algebraic
tensorwise Gauss-projection range theorem of #5023.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- The indicator of a measurable rectangle is exactly the real `L²`
external tensor of the two one-factor indicator vectors. -/
theorem realL2ExternalTensor_indicatorConstLp_one
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s)
    {t : Set β} (ht : MeasurableSet t) :
    realL2ExternalTensor
        (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ))
        (indicatorConstLp 2 ht (measure_ne_top ν t) (1 : ℝ)) =
      indicatorConstLp 2 (hs.prod ht)
        (measure_ne_top (μ.prod ν) (s ×ˢ t)) (1 : ℝ) := by
  apply Lp.ext
  let f : Lp ℝ 2 μ :=
    indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)
  let g : Lp ℝ 2 ν :=
    indicatorConstLp 2 ht (measure_ne_top ν t) (1 : ℝ)
  let r : Lp ℝ 2 (μ.prod ν) :=
    indicatorConstLp 2 (hs.prod ht)
      (measure_ne_top (μ.prod ν) (s ×ˢ t)) (1 : ℝ)
  have hTensor :=
    realL2ExternalTensor_coeFn (μ := μ) (ν := ν) f g
  have hf :
      f =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) := by
    simpa [f] using
      (indicatorConstLp_coeFn
        (p := (2 : ENNReal)) (μ := μ)
        (s := s) (hs := hs) (hμs := measure_ne_top μ s) (c := (1 : ℝ)))
  have hg :
      g =ᵐ[ν] t.indicator (fun _ => (1 : ℝ)) := by
    simpa [g] using
      (indicatorConstLp_coeFn
        (p := (2 : ENNReal)) (μ := ν)
        (s := t) (hs := ht) (hμs := measure_ne_top ν t) (c := (1 : ℝ)))
  have hfPair :
      (fun z : α × β => f z.1) =ᵐ[μ.prod ν]
        fun z => s.indicator (fun _ => (1 : ℝ)) z.1 := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq hf
  have hgPair :
      (fun z : α × β => g z.2) =ᵐ[μ.prod ν]
        fun z => t.indicator (fun _ => (1 : ℝ)) z.2 := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq hg
  have hr :
      r =ᵐ[μ.prod ν] (s ×ˢ t).indicator (fun _ => (1 : ℝ)) := by
    simpa [r] using
      (indicatorConstLp_coeFn
        (p := (2 : ENNReal)) (μ := μ.prod ν)
        (s := s ×ˢ t) (hs := hs.prod ht)
        (hμs := measure_ne_top (μ.prod ν) (s ×ˢ t)) (c := (1 : ℝ)))
  filter_upwards [hTensor, hfPair, hgPair, hr] with z hTensorZ hfZ hgZ hrZ
  rw [hTensorZ, hrZ]
  simp only [realL2ExternalTensorFunction]
  rw [hfZ, hgZ]
  by_cases hsZ : z.1 ∈ s <;> by_cases htZ : z.2 ∈ t
  · simp [Set.indicator_of_mem, hsZ, htZ]
  · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hsZ, htZ]
  · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hsZ, htZ]
  · simp [Set.indicator_of_notMem, hsZ, htZ]

/-- The algebraic external-tensor range is dense in the full real
`L²(μ × ν)` product space whenever both factor measures are finite. -/
theorem realL2ExternalTensorLift_range_topologicalClosure_eq_top
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (LinearMap.range
      (realL2ExternalTensorLift (μ := μ) (ν := ν))).topologicalClosure =
      (⊤ : Submodule ℝ (Lp ℝ 2 (μ.prod ν))) := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro K hK
  have hKint : Integrable (fun z => K z) (μ.prod ν) :=
    (Lp.memLp K).integrable one_le_two
  have hRect :
      ∀ {s : Set α}, MeasurableSet s →
        ∀ {t : Set β}, MeasurableSet t →
          (∫ z in s ×ˢ t, K z ∂(μ.prod ν)) = 0 := by
    intro s hs t ht
    let f : Lp ℝ 2 μ :=
      indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)
    let g : Lp ℝ 2 ν :=
      indicatorConstLp 2 ht (measure_ne_top ν t) (1 : ℝ)
    let r : Lp ℝ 2 (μ.prod ν) :=
      indicatorConstLp 2 (hs.prod ht)
        (measure_ne_top (μ.prod ν) (s ×ˢ t)) (1 : ℝ)
    have hrange :
        r ∈ LinearMap.range
          (realL2ExternalTensorLift (μ := μ) (ν := ν)) := by
      refine ⟨f ⊗ₜ[ℝ] g, ?_⟩
      change realL2ExternalTensor f g = r
      simpa [f, g, r] using
        (realL2ExternalTensor_indicatorConstLp_one
          (μ := μ) (ν := ν) hs ht)
    have horth :
        inner ℝ r K = 0 :=
      (Submodule.mem_orthogonal
        (LinearMap.range
          (realL2ExternalTensorLift (μ := μ) (ν := ν))) K).1
        hK r hrange
    change
      inner ℝ
        (indicatorConstLp 2 (hs.prod ht)
          (measure_ne_top (μ.prod ν) (s ×ˢ t)) (1 : ℝ))
        K = 0 at horth
    calc
      (∫ z in s ×ˢ t, K z ∂(μ.prod ν)) =
          inner ℝ
            (indicatorConstLp 2 (hs.prod ht)
              (measure_ne_top (μ.prod ν) (s ×ˢ t)) (1 : ℝ))
            K := by
        symm
        exact
          L2.inner_indicatorConstLp_one
            (μ := μ.prod ν) (s := s ×ˢ t)
            (hs.prod ht)
            (measure_ne_top (μ.prod ν) (s ×ˢ t)) K
      _ = 0 := horth
  have hAll :
      ∀ u : Set (α × β), MeasurableSet u →
        (∫ z in u, K z ∂(μ.prod ν)) = 0 := by
    intro u hu
    induction u, hu
      using MeasurableSpace.induction_on_inter
        generateFrom_prod.symm isPiSystem_prod with
    | empty =>
        simp
    | basic u hu =>
        rcases hu with ⟨s, hs, t, ht, rfl⟩
        exact hRect hs ht
    | compl u hu hzero =>
        have hUniv :
            (∫ z, K z ∂(μ.prod ν)) = 0 := by
          have h := hRect
            (s := Set.univ) MeasurableSet.univ
            (t := Set.univ) MeasurableSet.univ
          simpa only [Set.univ_prod_univ, setIntegral_univ] using h
        have hadd := integral_add_compl hu hKint
        rw [hzero, hUniv] at hadd
        simpa using hadd
    | iUnion f hdisj hmeas hzero =>
        rw [integral_iUnion hmeas hdisj hKint.integrableOn]
        simp [hzero]
  have hAE :
      (fun z => K z) =ᵐ[μ.prod ν] 0 :=
    hKint.ae_eq_zero_of_forall_setIntegral_eq_zero
      (fun u hu _ => hAll u hu)
  apply Lp.ext
  exact hAE.trans (Lp.coeFn_zero ℝ 2 (μ.prod ν)).symm

/-- Equivalent dense-range formulation for the universal algebraic external
tensor lift. -/
theorem realL2ExternalTensorLift_denseRange
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    DenseRange
      (realL2ExternalTensorLift (μ := μ) (ν := ν)) := by
  rw [denseRange_iff_closure_range]
  change
    closure
        (LinearMap.range
          (realL2ExternalTensorLift (μ := μ) (ν := ν)) :
          Set (Lp ℝ 2 (μ.prod ν))) =
      Set.univ
  rw [← Submodule.topologicalClosure_coe,
    realL2ExternalTensorLift_range_topologicalClosure_eq_top]
  rfl

/-- Audit-visible density package for the real product-`L²` external tensor. -/
structure RealL2ExternalTensorDenseRangePackage
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : Prop where
  rectangleIndicator :
    ∀ {s : Set α} (hs : MeasurableSet s)
      {t : Set β} (ht : MeasurableSet t),
      realL2ExternalTensor
          (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ))
          (indicatorConstLp 2 ht (measure_ne_top ν t) (1 : ℝ)) =
        indicatorConstLp 2 (hs.prod ht)
          (measure_ne_top (μ.prod ν) (s ×ˢ t)) (1 : ℝ)
  dense :
    DenseRange
      (realL2ExternalTensorLift (μ := μ) (ν := ν))

/-- Construct the dense-range receipt. -/
theorem realL2ExternalTensorDenseRangePackage
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    RealL2ExternalTensorDenseRangePackage
      (μ := μ) (ν := ν) :=
  { rectangleIndicator :=
      realL2ExternalTensor_indicatorConstLp_one
        (μ := μ) (ν := ν)
    dense :=
      realL2ExternalTensorLift_denseRange
        (μ := μ) (ν := ν) }

end

end MathlibAnalytic
end MGAP4D
