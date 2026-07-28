import MGAP4D.MathlibAnalytic.RealTensorComplexificationComplexInnerProductSpace
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

namespace RealTensorComplexification

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The real-imaginary `L²` product model of the algebraic complexification. -/
abbrev RealImagProduct (H : Type u) [NormedAddCommGroup H] :=
  WithLp 2 (H × H)

/-- Real-part evaluation on the scalar tensor factor. -/
def realPartBilinear : ℂ →ₗ[ℝ] H →ₗ[ℝ] H :=
  (LinearMap.lsmul ℝ H).comp Complex.reLm

/-- Imaginary-part evaluation on the scalar tensor factor. -/
def imagPartBilinear : ℂ →ₗ[ℝ] H →ₗ[ℝ] H :=
  (LinearMap.lsmul ℝ H).comp Complex.imLm

/-- Real component of an algebraic complexification vector. -/
def realPart : Space H →ₗ[ℝ] H :=
  TensorProduct.lift realPartBilinear

/-- Imaginary component of an algebraic complexification vector. -/
def imagPart : Space H →ₗ[ℝ] H :=
  TensorProduct.lift imagPartBilinear

@[simp] theorem realPart_tmul (z : ℂ) (x : H) :
    realPart (z ⊗ₜ[ℝ] x : Space H) = z.re • x := by
  rfl

@[simp] theorem imagPart_tmul (z : ℂ) (x : H) :
    imagPart (z ⊗ₜ[ℝ] x : Space H) = z.im • x := by
  rfl

/-- Additivity of the explicitly named real tensor inner product in its second
argument. -/
theorem realInner_add_right (x y z : Space H) :
    realInner x (y + z) = realInner x y + realInner x z := by
  calc
    realInner x (y + z) = realInner (y + z) x := realInner_comm x (y + z)
    _ = realInner y x + realInner z x := realInner_add_left y z x
    _ = realInner x y + realInner x z := by
      rw [realInner_comm y x, realInner_comm z x]

/-- The two coordinate maps before applying the `L²` type synonym. -/
def toRealImagProdLinear : Space H →ₗ[ℝ] H × H :=
  LinearMap.prod realPart imagPart

/-- Real-imaginary coordinate map into the `L²` product. -/
def toRealImagLinear : Space H →ₗ[ℝ] RealImagProduct H :=
  (WithLp.linearEquiv 2 ℝ (H × H)).symm.toLinearMap.comp
    toRealImagProdLinear

@[simp] theorem toRealImagLinear_tmul (z : ℂ) (x : H) :
    toRealImagLinear (z ⊗ₜ[ℝ] x : Space H) =
      WithLp.toLp 2 (z.re • x, z.im • x) := by
  rfl

/-- The imaginary-axis embedding `x ↦ i ⊗ x`. -/
def ofImagLinear : H →ₗ[ℝ] Space H :=
  imaginaryUnitLinearIsometry.toLinearMap.comp
    ofRealLinearIsometry.toLinearMap

@[simp] theorem ofImagLinear_apply (x : H) :
    ofImagLinear x = (Complex.I : ℂ) ⊗ₜ[ℝ] x := by
  simp [ofImagLinear]

/-- Reconstruct an algebraic complexification vector from its real and imaginary
components. -/
def fromRealImagProdLinear : H × H →ₗ[ℝ] Space H :=
  LinearMap.coprod ofRealLinearIsometry.toLinearMap ofImagLinear

/-- Reconstruction from the `L²` real-imaginary product. -/
def fromRealImagLinear : RealImagProduct H →ₗ[ℝ] Space H :=
  fromRealImagProdLinear.comp
    (WithLp.linearEquiv 2 ℝ (H × H)).toLinearMap

@[simp] theorem fromRealImagLinear_toLp (x y : H) :
    fromRealImagLinear (WithLp.toLp 2 (x, y)) =
      (1 : ℂ) ⊗ₜ[ℝ] x + (Complex.I : ℂ) ⊗ₜ[ℝ] y := by
  simp [fromRealImagLinear, fromRealImagProdLinear]

/-- Reconstruction after taking real and imaginary coordinates is the identity. -/
theorem fromRealImagLinear_toRealImagLinear (x : Space H) :
    fromRealImagLinear (toRealImagLinear x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z y
    rw [toRealImagLinear_tmul, fromRealImagLinear_toLp]
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
    rw [← TensorProduct.add_tmul]
    congr 1
    apply Complex.ext <;> simp
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

/-- Taking coordinates after reconstruction is the identity. -/
theorem toRealImagLinear_fromRealImagLinear (p : RealImagProduct H) :
    toRealImagLinear (fromRealImagLinear p) = p := by
  change WithLp.toLp 2
      (realPart (fromRealImagLinear p), imagPart (fromRealImagLinear p)) = p
  rw [show fromRealImagLinear p =
      (1 : ℂ) ⊗ₜ[ℝ] p.fst + (Complex.I : ℂ) ⊗ₜ[ℝ] p.snd by
    simpa [fromRealImagLinear, fromRealImagProdLinear] using
      fromRealImagLinear_toLp (H := H) p.fst p.snd]
  simp only [map_add, realPart_tmul, imagPart_tmul, Complex.one_re,
    one_smul, Complex.I_re, zero_smul, add_zero, Complex.one_im,
    Complex.I_im, zero_add]
  change WithLp.toLp 2 (WithLp.ofLp p) = p
  exact WithLp.toLp_ofLp (p := 2) p

/-- Linear equivalence between the algebraic complexification and its real and
imaginary `L²` coordinates. -/
def realImagLinearEquiv : Space H ≃ₗ[ℝ] RealImagProduct H :=
  LinearEquiv.ofLinear toRealImagLinear fromRealImagLinear
    (LinearMap.ext fun p => toRealImagLinear_fromRealImagLinear p)
    (LinearMap.ext fun x => fromRealImagLinear_toRealImagLinear x)

@[simp] theorem realImagLinearEquiv_apply (x : Space H) :
    realImagLinearEquiv x = toRealImagLinear x :=
  rfl

@[simp] theorem realImagLinearEquiv_symm_apply (p : RealImagProduct H) :
    realImagLinearEquiv.symm p = fromRealImagLinear p :=
  rfl

/-- The real-imaginary coordinate equivalence preserves the canonical real inner
product. -/
theorem realImagLinearEquiv_inner_map_map (x y : Space H) :
    inner ℝ (realImagLinearEquiv x) (realImagLinearEquiv y) =
      realInner x y := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [realInner]
  · intro z u
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [realInner]
    · intro w v
      simp only [realImagLinearEquiv_apply, toRealImagLinear_tmul,
        WithLp.prod_inner_apply, inner_smul_left, inner_smul_right]
      unfold realInner
      rw [TensorProduct.inner_tmul, Complex.inner]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
        starRingEnd_apply, star_trivial]
      ring
    · intro y₁ y₂ hy₁ hy₂
      rw [map_add, inner_add_right, realInner_add_right, hy₁, hy₂]
  · intro x₁ x₂ hx₁ hx₂
    rw [map_add, inner_add_left, realInner_add_left, hx₁, hx₂]

/-- Canonical real-linear isometric equivalence with the real-imaginary `L²`
product. -/
def realImagLinearIsometryEquiv :
    Space H ≃ₗᵢ[ℝ] RealImagProduct H :=
  realImagLinearEquiv.isometryOfInner fun x y => by
    simpa [realInner] using realImagLinearEquiv_inner_map_map x y

@[simp] theorem realImagLinearIsometryEquiv_apply (x : Space H) :
    realImagLinearIsometryEquiv x = toRealImagLinear x := by
  rfl

@[simp] theorem realImagLinearIsometryEquiv_symm_apply
    (p : RealImagProduct H) :
    realImagLinearIsometryEquiv.symm p = fromRealImagLinear p := by
  rfl

/-- The algebraic complexification is already complete when the original real
inner-product space is complete. Because the scalar factor is the
two-dimensional real Hilbert space `ℂ`, the complexification is isometrically
the `L²` product `H × H`. -/
noncomputable instance instCompleteSpace [CompleteSpace H] :
    CompleteSpace (Space H) := by
  apply (completeSpace_congr
    (e := (realImagLinearIsometryEquiv (H := H)).toLinearEquiv.toEquiv)
    (realImagLinearIsometryEquiv (H := H)).isometry.isUniformEmbedding).mpr
  infer_instance

end RealTensorComplexification

end

end MathlibAnalytic
end MGAP4D
