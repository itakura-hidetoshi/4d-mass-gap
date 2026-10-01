import MGAP4D.MathlibAnalytic.RealHilbertPairwiseOrthogonalStrongLimit
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# Centered coordinate directions in an infinite product probability L² space

The scale-common carrier used for the finite Wilson boundary marginals is an
independent infinite product.  This file records the exact Hilbert geometry of
that construction.

A vector pulled back from coordinate `i` and a vector pulled back from a
different coordinate `j` have inner product equal to the product of their
means.  Hence centered coordinate vectors at distinct scales are orthogonal.
Consequently, a sequence which places one centered excitation in a fresh
independent coordinate at every scale can have a strong limit only at zero.

This is a kinematic statement about independent products.  It does not identify
any finite one-slab top sector with an OS vacuum-orthogonal sector.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory ProbabilityTheory Topology
open scoped InnerProductSpace

noncomputable section

universe u v

/-- Pull one coordinate real `L²` space isometrically into an infinite product
of probability spaces. -/
noncomputable def infiniteProductProbabilityCoordinateL2Pullback
    {ι : Type u}
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) :
    Lp ℝ 2 (μ i) →ₗᵢ[ℝ] Lp ℝ 2 (Measure.infinitePi μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (Function.eval i)
    (measurePreserving_eval_infinitePi μ i)

/-- In a probability `L²` space, pairing with the constant-one vector is
integration. -/
theorem realL2_inner_constOne_eq_integral
    {α : Type u}
    [MeasurableSpace α]
    {μ : Measure α}
    [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) :
    inner ℝ (Lp.const 2 μ (1 : ℝ)) f = ∫ x, f x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))] with x hx
  rw [hx]
  simp [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
    RCLike.re_to_real, Function.const_apply]

/-- Pullbacks from distinct independent product coordinates have inner product
equal to the product of their scalar means. -/
theorem infiniteProductProbabilityCoordinateL2Pullback_inner_eq_mul_integrals
    {ι : Type u}
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    {i j : ι}
    (hij : i ≠ j)
    (f : Lp ℝ 2 (μ i))
    (g : Lp ℝ 2 (μ j)) :
    inner ℝ
        (infiniteProductProbabilityCoordinateL2Pullback μ i f)
        (infiniteProductProbabilityCoordinateL2Pullback μ j g) =
      (∫ x, f x ∂μ i) * ∫ y, g y ∂μ j := by
  let hf : AEStronglyMeasurable f (μ i) := Lp.aestronglyMeasurable f
  let hg : AEStronglyMeasurable g (μ j) := Lp.aestronglyMeasurable g
  let F : α i → ℝ := hf.mk f
  let G : α j → ℝ := hg.mk g
  have hFstrong : StronglyMeasurable F := by
    simpa [F, hf] using hf.stronglyMeasurable_mk
  have hGstrong : StronglyMeasurable G := by
    simpa [G, hg] using hg.stronglyMeasurable_mk
  have hFae : f =ᵐ[μ i] F := by
    simpa [F, hf] using hf.ae_eq_mk
  have hGae : g =ᵐ[μ j] G := by
    simpa [G, hg] using hg.ae_eq_mk
  have hPullF :
      infiniteProductProbabilityCoordinateL2Pullback μ i f =ᵐ[Measure.infinitePi μ]
        fun ω => F (ω i) := by
    have hcomp :=
      Lp.coeFn_compMeasurePreserving f (measurePreserving_eval_infinitePi μ i)
    have hrep :=
      (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae_eq hFae
    exact hcomp.trans hrep
  have hPullG :
      infiniteProductProbabilityCoordinateL2Pullback μ j g =ᵐ[Measure.infinitePi μ]
        fun ω => G (ω j) := by
    have hcomp :=
      Lp.coeFn_compMeasurePreserving g (measurePreserving_eval_infinitePi μ j)
    have hrep :=
      (measurePreserving_eval_infinitePi μ j).quasiMeasurePreserving.ae_eq hGae
    exact hcomp.trans hrep
  have hEvalIndependent :
      (fun ω : ∀ k, α k => ω i) ⟂ᵢ[Measure.infinitePi μ]
        (fun ω : ∀ k, α k => ω j) := by
    exact
      (iIndepFun_infinitePi
        (P := μ)
        (X := fun _ x => x)
        (fun _ => measurable_id)).indepFun hij
  have hFGIndependent :
      (fun ω : ∀ k, α k => F (ω i)) ⟂ᵢ[Measure.infinitePi μ]
        (fun ω : ∀ k, α k => G (ω j)) := by
    simpa [Function.comp_def] using
      hEvalIndependent.comp hFstrong.measurable hGstrong.measurable
  have hfactor :
      (∫ ω, F (ω i) * G (ω j) ∂Measure.infinitePi μ) =
        (∫ ω, F (ω i) ∂Measure.infinitePi μ) *
          ∫ ω, G (ω j) ∂Measure.infinitePi μ := by
    exact hFGIndependent.integral_fun_mul_eq_mul_integral
      (hFstrong.comp_measurable (by fun_prop)).aestronglyMeasurable
      (hGstrong.comp_measurable (by fun_prop)).aestronglyMeasurable
  have hFcoord :
      (∫ ω, F (ω i) ∂Measure.infinitePi μ) = ∫ x, F x ∂μ i := by
    calc
      (∫ ω, F (ω i) ∂Measure.infinitePi μ) =
          ∫ x, F x ∂(Measure.infinitePi μ).map (Function.eval i) := by
            symm
            exact integral_map_of_stronglyMeasurable
              (by fun_prop) hFstrong
      _ = ∫ x, F x ∂μ i := by
        rw [Measure.infinitePi_map_eval]
  have hGcoord :
      (∫ ω, G (ω j) ∂Measure.infinitePi μ) = ∫ x, G x ∂μ j := by
    calc
      (∫ ω, G (ω j) ∂Measure.infinitePi μ) =
          ∫ x, G x ∂(Measure.infinitePi μ).map (Function.eval j) := by
            symm
            exact integral_map_of_stronglyMeasurable
              (by fun_prop) hGstrong
      _ = ∫ x, G x ∂μ j := by
        rw [Measure.infinitePi_map_eval]
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ ω,
        inner ℝ
          (infiniteProductProbabilityCoordinateL2Pullback μ i f ω)
          (infiniteProductProbabilityCoordinateL2Pullback μ j g ω)
        ∂Measure.infinitePi μ) =
        ∫ ω, F (ω i) * G (ω j) ∂Measure.infinitePi μ := by
      apply integral_congr_ae
      filter_upwards [hPullF, hPullG] with ω hfi hgj
      rw [hfi, hgj]
      simp [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
        RCLike.re_to_real, mul_comm]
    _ =
        (∫ ω, F (ω i) ∂Measure.infinitePi μ) *
          ∫ ω, G (ω j) ∂Measure.infinitePi μ := hfactor
    _ = (∫ x, F x ∂μ i) * ∫ y, G y ∂μ j := by
      rw [hFcoord, hGcoord]
    _ = (∫ x, f x ∂μ i) * ∫ y, g y ∂μ j := by
      rw [integral_congr_ae hFae.symm, integral_congr_ae hGae.symm]

/-- Distinct coordinate pullbacks are orthogonal as soon as one of the two
coordinate vectors is centered. -/
theorem infiniteProductProbabilityCoordinateL2Pullback_inner_eq_zero_of_left_centered
    {ι : Type u}
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    {i j : ι}
    (hij : i ≠ j)
    (f : Lp ℝ 2 (μ i))
    (g : Lp ℝ 2 (μ j))
    (hf :
      inner ℝ (Lp.const 2 (μ i) (1 : ℝ)) f = 0) :
    inner ℝ
        (infiniteProductProbabilityCoordinateL2Pullback μ i f)
        (infiniteProductProbabilityCoordinateL2Pullback μ j g) = 0 := by
  rw [infiniteProductProbabilityCoordinateL2Pullback_inner_eq_mul_integrals μ hij f g]
  rw [← realL2_inner_constOne_eq_integral f, hf, zero_mul]

/-- A sequence of centered vectors, one in each independent product coordinate,
is pairwise orthogonal. -/
theorem infiniteProductProbabilityCoordinateL2Pullback_pairwise_inner_eq_zero
    {α : ℕ → Type v}
    [∀ n, MeasurableSpace (α n)]
    (μ : ∀ n, Measure (α n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (f : (n : ℕ) → Lp ℝ 2 (μ n))
    (hcenter :
      ∀ n, inner ℝ (Lp.const 2 (μ n) (1 : ℝ)) (f n) = 0) :
    ∀ {m n : ℕ}, m ≠ n →
      inner ℝ
        (infiniteProductProbabilityCoordinateL2Pullback μ m (f m))
        (infiniteProductProbabilityCoordinateL2Pullback μ n (f n)) = 0 := by
  intro m n hmn
  exact
    infiniteProductProbabilityCoordinateL2Pullback_inner_eq_zero_of_left_centered
      μ hmn (f m) (f n) (hcenter m)

/-- Therefore the independent product scale carrier admits no nonzero strong
limit obtained by moving a centered excitation through fresh scale
coordinates. -/
theorem infiniteProductProbabilityCoordinateL2Pullback_tendsto_zero_of_centered
    {α : ℕ → Type v}
    [∀ n, MeasurableSpace (α n)]
    (μ : ∀ n, Measure (α n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (f : (n : ℕ) → Lp ℝ 2 (μ n))
    (hcenter :
      ∀ n, inner ℝ (Lp.const 2 (μ n) (1 : ℝ)) (f n) = 0)
    (x : Lp ℝ 2 (Measure.infinitePi μ))
    (hlim :
      Tendsto
        (fun n => infiniteProductProbabilityCoordinateL2Pullback μ n (f n))
        atTop
        (𝓝 x)) :
    x = 0 := by
  exact realHilbert_tendsto_zero_of_pairwise_inner_eq_zero
    (fun n => infiniteProductProbabilityCoordinateL2Pullback μ n (f n))
    x
    (infiniteProductProbabilityCoordinateL2Pullback_pairwise_inner_eq_zero μ f hcenter)
    hlim

end

end MathlibAnalytic
end MGAP4D
