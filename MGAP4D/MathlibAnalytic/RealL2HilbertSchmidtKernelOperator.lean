import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelBilinear
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/-- The Fréchet--Riesz vector representing the Hilbert--Schmidt kernel
functional `g ↦ ⟪K, f ⊠ g⟫` on real `L²(μ)`. -/
noncomputable def realL2HilbertSchmidtKernelRieszVector
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm
    (realL2HilbertSchmidtKernelBilinear K f)

/-- Fréchet--Riesz gives the exact kernel pairing as the Hilbert inner product
of the representing vector with the right test vector. -/
theorem realL2HilbertSchmidtKernelRieszVector_inner
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (f g : Lp ℝ 2 μ) :
    inner ℝ (realL2HilbertSchmidtKernelRieszVector K f) g =
      realL2HilbertSchmidtKernelPairing K f g := by
  simpa [realL2HilbertSchmidtKernelRieszVector] using
    (InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ) (E := Lp ℝ 2 μ)
      (realL2HilbertSchmidtKernelBilinear K f) g)

/-- The Riesz representative has exactly the norm of its continuous dual
functional. -/
theorem realL2HilbertSchmidtKernelRieszVector_norm
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (f : Lp ℝ 2 μ) :
    ‖realL2HilbertSchmidtKernelRieszVector K f‖ =
      ‖realL2HilbertSchmidtKernelBilinear K f‖ := by
  simpa [realL2HilbertSchmidtKernelRieszVector] using
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm.norm_map
      (realL2HilbertSchmidtKernelBilinear K f)

/-- Hilbert--Schmidt bound for the Riesz representative. -/
theorem realL2HilbertSchmidtKernelRieszVector_norm_le
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (f : Lp ℝ 2 μ) :
    ‖realL2HilbertSchmidtKernelRieszVector K f‖ ≤ ‖K‖ * ‖f‖ := by
  rw [realL2HilbertSchmidtKernelRieszVector_norm]
  exact realL2HilbertSchmidtKernelBilinear_apply_norm_le K f

/-- The Riesz representative is additive in the left test vector. -/
theorem realL2HilbertSchmidtKernelRieszVector_add
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (f₁ f₂ : Lp ℝ 2 μ) :
    realL2HilbertSchmidtKernelRieszVector K (f₁ + f₂) =
      realL2HilbertSchmidtKernelRieszVector K f₁ +
        realL2HilbertSchmidtKernelRieszVector K f₂ := by
  simp [realL2HilbertSchmidtKernelRieszVector]

/-- Over the real field the conjugate-linear Riesz equivalence is ordinary
real-linear, so the representing vector respects real scalar multiplication. -/
theorem realL2HilbertSchmidtKernelRieszVector_smul
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (c : ℝ) (f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtKernelRieszVector K (c • f) =
      c • realL2HilbertSchmidtKernelRieszVector K f := by
  simp [realL2HilbertSchmidtKernelRieszVector]

/-- Unbundled real-linear Hilbert--Schmidt kernel operator. -/
noncomputable def realL2HilbertSchmidtKernelOperatorLinearMap
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ)) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ :=
  { toFun := realL2HilbertSchmidtKernelRieszVector K
    map_add' := realL2HilbertSchmidtKernelRieszVector_add K
    map_smul' := realL2HilbertSchmidtKernelRieszVector_smul K }

/-- Canonical bounded operator associated by Fréchet--Riesz to a square
Hilbert--Schmidt kernel.  Its norm is controlled by the kernel `L²` norm. -/
noncomputable def realL2HilbertSchmidtKernelOperator
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    (𝕜 := ℝ)
    (𝕜₂ := ℝ)
    (E := Lp ℝ 2 μ)
    (F := Lp ℝ 2 μ)
    (σ := RingHom.id ℝ)
    (realL2HilbertSchmidtKernelOperatorLinearMap K)
    ‖K‖
    (realL2HilbertSchmidtKernelRieszVector_norm_le K)

@[simp] theorem realL2HilbertSchmidtKernelOperator_apply
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtKernelOperator K f =
      realL2HilbertSchmidtKernelRieszVector K f := by
  rfl

/-- Exact matrix coefficient of the Hilbert--Schmidt kernel operator. -/
theorem realL2HilbertSchmidtKernelOperator_inner
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (f g : Lp ℝ 2 μ) :
    inner ℝ (realL2HilbertSchmidtKernelOperator K f) g =
      realL2HilbertSchmidtKernelPairing K f g := by
  exact realL2HilbertSchmidtKernelRieszVector_inner K f g

/-- Operator norm is bounded by the Hilbert--Schmidt `L²` norm of the kernel. -/
theorem realL2HilbertSchmidtKernelOperator_norm_le
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ)) :
    ‖realL2HilbertSchmidtKernelOperator K‖ ≤ ‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (realL2HilbertSchmidtKernelOperator K)
    (norm_nonneg K)
  intro f
  exact realL2HilbertSchmidtKernelRieszVector_norm_le K f

/-- Pairing-level symmetry criterion.  This avoids choosing any pointwise
representative or transpose of an `L²` kernel. -/
def RealL2HilbertSchmidtKernelPairingSymmetric
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ)) : Prop :=
  ∀ f g : Lp ℝ 2 μ,
    realL2HilbertSchmidtKernelPairing K f g =
      realL2HilbertSchmidtKernelPairing K g f

/-- Pairing symmetry makes the Fréchet--Riesz Hilbert--Schmidt operator
symmetric in Mathlib's Hilbert-space sense. -/
theorem realL2HilbertSchmidtKernelOperator_isSymmetric
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (hSymm : RealL2HilbertSchmidtKernelPairingSymmetric K) :
    ((realL2HilbertSchmidtKernelOperator K :
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := by
  intro f g
  calc
    inner ℝ (realL2HilbertSchmidtKernelOperator K f) g =
        realL2HilbertSchmidtKernelPairing K f g :=
      realL2HilbertSchmidtKernelOperator_inner K f g
    _ = realL2HilbertSchmidtKernelPairing K g f := hSymm f g
    _ = inner ℝ (realL2HilbertSchmidtKernelOperator K g) f :=
      (realL2HilbertSchmidtKernelOperator_inner K g f).symm
    _ = inner ℝ f (realL2HilbertSchmidtKernelOperator K g) :=
      real_inner_comm _ _

/-- Pairing-level quadratic nonnegativity criterion. -/
def RealL2HilbertSchmidtKernelPairingNonnegative
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ)) : Prop :=
  ∀ f : Lp ℝ 2 μ, 0 ≤ realL2HilbertSchmidtKernelPairing K f f

/-- A symmetric square `L²` kernel with nonnegative pairing quadratic form
produces a positive bounded operator. -/
theorem realL2HilbertSchmidtKernelOperator_isPositive
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (hSymm : RealL2HilbertSchmidtKernelPairingSymmetric K)
    (hNonneg : RealL2HilbertSchmidtKernelPairingNonnegative K) :
    ((realL2HilbertSchmidtKernelOperator K :
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsPositive := by
  rw [LinearMap.isPositive_iff]
  refine ⟨realL2HilbertSchmidtKernelOperator_isSymmetric K hSymm, ?_⟩
  intro f
  rw [realL2HilbertSchmidtKernelOperator_inner K f f]
  exact hNonneg f

/-- Audit-visible generic Fréchet--Riesz Hilbert--Schmidt operator package. -/
structure RealL2HilbertSchmidtKernelOperatorPackage
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ)) : Prop where
  innerFormula :
    ∀ f g : Lp ℝ 2 μ,
      inner ℝ (realL2HilbertSchmidtKernelOperator K f) g =
        realL2HilbertSchmidtKernelPairing K f g
  normBound : ‖realL2HilbertSchmidtKernelOperator K‖ ≤ ‖K‖

/-- Construct the generic Hilbert--Schmidt kernel-operator receipt. -/
theorem realL2HilbertSchmidtKernelOperatorPackage
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ)) :
    RealL2HilbertSchmidtKernelOperatorPackage K :=
  { innerFormula := realL2HilbertSchmidtKernelOperator_inner K
    normBound := realL2HilbertSchmidtKernelOperator_norm_le K }

end

end MathlibAnalytic
end MGAP4D
