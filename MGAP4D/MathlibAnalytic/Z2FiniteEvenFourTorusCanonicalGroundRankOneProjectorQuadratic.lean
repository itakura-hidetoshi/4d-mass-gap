import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCanonicalPerronGroundRightSlope
import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementMixedDifferenceWitness
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set TopologicalSpace
open scoped BigOperators InnerProduct

noncomputable section

/-- Kernel of the orthogonal rank-one projector onto the right-extended
canonical Perron ray.  For positive coupling this is the basis-free form of the
one-dimensional ground spectral projector. -/
noncomputable def finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  let p :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
      H energyIdentity energyNontrivial β
  (inner ℝ p p)⁻¹ * p A * p B

/-- The squared Hilbert norm of the canonical mass-one ground at beta zero is
exactly the inverse boundary cardinality. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_inner_self_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
          H energyIdentity energyNontrivial 0)
        (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
          H energyIdentity energyNontrivial 0) =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ := by
  let C := FiniteEvenFourTorusZ2SliceConfiguration H
  let n : ℝ := Fintype.card C
  have hn : n ≠ 0 := by
    dsimp [n, C]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
  rw [PiLp.inner_apply]
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_zero_apply
    H energyIdentity energyNontrivial hEnergy]
  change (∑ _A : C, n⁻¹ * n⁻¹) = n⁻¹
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn]

/-- Inverse squared norm of the canonical ground converges to the boundary
cardinality.  This is the only denominator entering the rank-one projector. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_inner_self_inv_tendsto
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Tendsto
      (fun β : ℝ =>
        (inner ℝ
          (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
            H energyIdentity energyNontrivial β)
          (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
            H energyIdentity energyNontrivial β))⁻¹)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)) := by
  let p :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
      H energyIdentity energyNontrivial
  let n : ℝ := Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H)
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) ≠ 0)
  have hp : Tendsto p
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (p 0)) :=
    (continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
      H energyIdentity energyNontrivial hEnergy).continuousAt.continuousWithinAt.tendsto
  have hinner :
      Tendsto (fun β : ℝ => inner ℝ (p β) (p β))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds n⁻¹) := by
    have h := hp.inner hp
    rw [finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_inner_self_zero
      H energyIdentity energyNontrivial hEnergy] at h
    simpa [p, n] using h
  have hinv := hinner.inv₀ (inv_ne_zero hn)
  simpa [p, n] using hinv

/-- Exact four-point factorization of the canonical rank-one ground projector
kernel. -/
theorem finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension_mixedDifference_eq
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteKernelMixedCrossDifference
        (finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
          H energyIdentity energyNontrivial β)
        x x' y y' =
      let p :=
        finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
          H energyIdentity energyNontrivial β
      (inner ℝ p p)⁻¹ * (p x - p x') * (p y - p y') := by
  unfold finiteKernelMixedCrossDifference
    finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
  ring

/-- The moving one-dimensional ground projector has an actual positive-side
quadratic mixed coefficient determined entirely by the first Perron-ground
slope.  No second derivative of the ground vector or spectral projector is
used. -/
theorem finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension_mixedDifference_quadraticQuotient
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Tendsto
      (fun β : ℝ =>
        finiteKernelMixedCrossDifference
            (finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
              H energyIdentity energyNontrivial β)
            x x' y y' / β ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        ((Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
          (1 / 4 : ℝ) *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial x -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial x') *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y'))) := by
  let C := FiniteEvenFourTorusZ2SliceConfiguration H
  let n : ℝ := Fintype.card C
  let dx : ℝ :=
    finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial x -
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial x'
  let dy : ℝ :=
    finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial y -
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial y'
  let p :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
      H energyIdentity energyNontrivial
  have hn : n ≠ 0 := by
    dsimp [n, C]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
  have hDen :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_inner_self_inv_tendsto
      H energyIdentity energyNontrivial hEnergy
  have hx :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_coordinateDifference_slope
      H energyIdentity energyNontrivial hEnergy x x'
  have hy :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_coordinateDifference_slope
      H energyIdentity energyNontrivial hEnergy y y'
  have hProd := hDen.mul (hx.mul hy)
  have hEq :
      (fun β : ℝ =>
        finiteKernelMixedCrossDifference
            (finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
              H energyIdentity energyNontrivial β)
            x x' y y' / β ^ 2) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun β : ℝ =>
        (inner ℝ (p β) (p β))⁻¹ *
          ((p β x - p β x') / β) *
          ((p β y - p β y') / β)) := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hβne : β ≠ 0 := ne_of_gt hβ
    rw [finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension_mixedDifference_eq]
    dsimp [p]
    field_simp [hβne]
    ring
  have hFinal := hProd.congr' hEq.symm
  convert hFinal using 1
  · rfl
  · dsimp [n, C, dx, dy] at *
    field_simp [hn]
    ring

end

end MathlibAnalytic
end MGAP4D
