import MGAP4D.MathlibAnalytic.CompactPositiveSpectralLogWeights
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp

noncomputable section

universe u v

/-- Natural weighted domain in a dependent Hilbert sum: those square-summable
vectors whose coordinatewise weighted image is again square-summable. -/
noncomputable def realHilbertSumWeightedDiagonalDomain
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)]
    (w : ι → ℝ) : Submodule ℝ (lp G 2) where
  carrier := {x | Memℓp (fun i => w i • x i) 2}
  zero_mem' := by
    change Memℓp (fun i => w i • (0 : lp G 2) i) 2
    have hzero : Memℓp (0 : (i : ι) → G i) 2 := zero_memℓp
    simpa only [lp.coeFn_zero, Pi.zero_apply, smul_zero] using hzero
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun i => w i • (x + y) i) 2
    simpa only [lp.coeFn_add, Pi.add_apply, smul_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    change Memℓp (fun i => w i • (c • x) i) 2
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_smul, mul_comm] using hx.const_smul c

@[simp] theorem mem_realHilbertSumWeightedDiagonalDomain
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)]
    (w : ι → ℝ)
    (x : lp G 2) :
    x ∈ realHilbertSumWeightedDiagonalDomain (G := G) w ↔
      Memℓp (fun i => w i • x i) 2 :=
  Iff.rfl

/-- Coordinatewise multiplication by a real weight, as a genuinely
partially-defined linear operator on the Hilbert sum with its maximal natural
weighted `ℓ²` domain. -/
noncomputable def realHilbertSumWeightedDiagonalLinearPMap
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)]
    (w : ι → ℝ) : lp G 2 →ₗ.[ℝ] lp G 2 where
  domain := realHilbertSumWeightedDiagonalDomain (G := G) w
  toFun :=
    { toFun := fun x =>
        ⟨fun i => w i • ((x : realHilbertSumWeightedDiagonalDomain (G := G) w) : lp G 2) i,
          x.property⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        change w i • (((x : realHilbertSumWeightedDiagonalDomain (G := G) w) : lp G 2) i +
            ((y : realHilbertSumWeightedDiagonalDomain (G := G) w) : lp G 2) i) =
          w i • ((x : realHilbertSumWeightedDiagonalDomain (G := G) w) : lp G 2) i +
            w i • ((y : realHilbertSumWeightedDiagonalDomain (G := G) w) : lp G 2) i
        exact smul_add _ _ _
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        change w i • (c • ((x : realHilbertSumWeightedDiagonalDomain (G := G) w) : lp G 2) i) =
          c • (w i • ((x : realHilbertSumWeightedDiagonalDomain (G := G) w) : lp G 2) i)
        simp [smul_smul, mul_comm] }

@[simp] theorem realHilbertSumWeightedDiagonalLinearPMap_domain
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)]
    (w : ι → ℝ) :
    (realHilbertSumWeightedDiagonalLinearPMap (G := G) w).domain =
      realHilbertSumWeightedDiagonalDomain (G := G) w :=
  rfl

@[simp] theorem realHilbertSumWeightedDiagonalLinearPMap_apply
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)]
    (w : ι → ℝ)
    (x : (realHilbertSumWeightedDiagonalLinearPMap (G := G) w).domain)
    (i : ι) :
    realHilbertSumWeightedDiagonalLinearPMap (G := G) w x i =
      w i • ((x : (realHilbertSumWeightedDiagonalLinearPMap (G := G) w).domain) : lp G 2) i :=
  rfl

/-- The logarithmic generator in intrinsic Hilbert-sum coordinates of the
strictly-positive support of a compact positive real-Hilbert operator.  Its
domain is exactly the maximal weighted `ℓ²` domain for `E(mu) = -log mu`. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    lp
        (fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        2 →ₗ.[ℝ]
      lp
        (fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        2 :=
  realHilbertSumWeightedDiagonalLinearPMap
    (G := fun mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
      eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
    (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)

@[simp] theorem realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_domain_mem_iff
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (x : lp
      (fun mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
      2) :
    x ∈ (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive).domain ↔
      Memℓp
        (fun mu =>
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • x mu)
        2 := by
  change x ∈ realHilbertSumWeightedDiagonalDomain
      (G := fun mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
      (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) ↔ _
  exact mem_realHilbertSumWeightedDiagonalDomain
    (G := fun mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
      eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
    (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) x

@[simp] theorem realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (x : (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
      T hCompact hPositive).domain)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive x mu =
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
        ((x : (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive).domain) :
          lp
            (fun nu : Eigenvalues
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
              eigenspace
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
            2) mu := by
  exact realHilbertSumWeightedDiagonalLinearPMap_apply
    (G := fun nu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
      eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
    (fun nu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu) x mu

end

end MathlibAnalytic
end MGAP4D