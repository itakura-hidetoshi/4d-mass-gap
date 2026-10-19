import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFullSpatialFeatureMonomialGramV5_LF
import Mathlib.Tactic

/-!
# P4-Q2-LG — original FULL spatial SU(2) Haar homogeneous Wilson Gram energies

The exact original full spatial SU(2) Wilson crossing kernel from LE/LF
is an exponential of the true finite-volume matrix-realification feature.
LF proves its nth homogeneous feature inner product is an exact finite
Gram sum of true full-spatial-link matrix-coordinate monomials.

We integrate this algebraic identity against the ACTUAL original
finite-volume spatial product Haar measure (NOT an independent
replacement for the two original interacting conditional posteriors).
For every finite family of true spatial continuous functions F_i,
the double-Haar Gram equals the finite sum of their squared Haar
moments. Specialization to ψ times the original LF monomials yields
exactly the nth full-spatial homogeneous Wilson energy as a finite
sum of squares.

Consequences formalized without rank assumptions: every degree has
nonnegative energy, zero energy implies ALL constituent moments are
zero, and a single concrete nonzero original spatial monomial moment
forces positive homogeneous energy. Positive Wilson Taylor
coefficients preserve nonnegativity.

This is finite-volume, finite-degree and keeps the authentic spatial
Haar reference. The all-degree spatial moment completeness, full
exponential integrated strict positivity, original physical transfer
injectivity, GI two-context Wilson determinant, H1-C3, and continuum
Yang-Mills mass gap remain separate proof obligations.

No sorry/admit, new axioms, source-frame assumptions, or posterior
replacement.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Coord" => ((Fin 2 × Fin 2) × Bool)
local notation "ProductCoord" => (Link × Coord)
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "FullPhi" => p4Q2LD_originalSpatialMatrixRealFeature H
local notation "Mon" => p4Q2LF_originalSpatialMatrixCoordinateMonomial H

/-- An EXACT finite double-Haar Gram identity for the literal
original full spatial configuration Haar reference, independent
of any source frame or synthetic kernel. -/
theorem p4Q2LG_originalFullSpatialHaarFiniteDoubleGram_eq_momentSquares
    {ι : Type*} [Fintype ι] (F : ι → C(Cfg, ℝ)) :
    (∫ A : Cfg, ∫ B : Cfg,
      (∑ i : ι, F i A * F i B) ∂haar ∂haar) =
    ∑ i : ι, (∫ A : Cfg, F i A ∂haar) ^ 2 := by
  classical
  have hFI (i : ι) : Integrable (fun A : Cfg => F i A) haar :=
    (F i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (A : Cfg) :
      (∫ B : Cfg, (∑ i : ι, F i A * F i B) ∂haar) =
        ∑ i : ι, F i A * (∫ B : Cfg, F i B ∂haar) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
    · intro i hi
      exact (hFI i).const_mul _
  calc
    (∫ A : Cfg, ∫ B : Cfg,
        (∑ i : ι, F i A * F i B) ∂haar ∂haar) =
      ∫ A : Cfg, (∑ i : ι,
        F i A * (∫ B : Cfg, F i B ∂haar)) ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        exact hInner A
    _ = ∑ i : ι, (∫ A : Cfg, F i A ∂haar) ^ 2 := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_mul_const]
        ring
      · intro i hi
        exact (hFI i).mul_const _

/-- Every actual full-spatial finite Haar Gram is nonnegative,
as an exact sum of squares with no positivity assumption on F. -/
theorem p4Q2LG_originalFullSpatialHaarFiniteDoubleGram_nonneg
    {ι : Type*} [Fintype ι] (F : ι → C(Cfg, ℝ)) :
    0 ≤ (∫ A : Cfg, ∫ B : Cfg,
      (∑ i : ι, F i A * F i B) ∂haar ∂haar) := by
  rw [p4Q2LG_originalFullSpatialHaarFiniteDoubleGram_eq_momentSquares]
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

/-- Original full-spatial homogeneous Wilson real-feature energy
against a genuinely continuous signed spatial source, integrated
using the complete spatial Haar reference. -/
noncomputable def p4Q2LG_originalFullSpatialHomogeneousWilsonHaarEnergy
    (ψ : C(Cfg, ℝ)) (n : ℕ) : ℝ :=
  ∫ A : Cfg, ∫ B : Cfg,
    ψ A * ψ B *
      (inner ℝ (FullPhi A) (FullPhi B)) ^ n ∂haar ∂haar

/-- Exact **full spatial configuration** homogeneous Wilson Haar
energy equals the original finite coordinate-monomial moment
SQUARES. No independent Haar posterior, Taylor-series interchange,
or limiting-volume approximation occurs. -/
theorem p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_eq_momentSquares
    (ψ : C(Cfg, ℝ)) (n : ℕ) :
    p4Q2LG_originalFullSpatialHomogeneousWilsonHaarEnergy H ψ n =
      ∑ a : Fin n → ProductCoord,
        (∫ A : Cfg, ψ A * Mon n a A ∂haar) ^ 2 := by
  let F : (Fin n → ProductCoord) → C(Cfg, ℝ) :=
    fun a => ψ * Mon n a
  have hPoint (A B : Cfg) :
      ψ A * ψ B * (inner ℝ (FullPhi A) (FullPhi B)) ^ n =
        ∑ a : Fin n → ProductCoord, F a A * F a B := by
    rw [p4Q2LF_originalFullSpatialFeatureInnerPow_eq_monomialGram]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    change ψ A * ψ B * (Mon n a A * Mon n a B) =
      (ψ A * Mon n a A) * (ψ B * Mon n a B)
    ring
  unfold p4Q2LG_originalFullSpatialHomogeneousWilsonHaarEnergy
  calc
    (∫ A : Cfg, ∫ B : Cfg,
      ψ A * ψ B * (inner ℝ (FullPhi A) (FullPhi B)) ^ n ∂haar ∂haar) =
        ∫ A : Cfg, ∫ B : Cfg,
          (∑ a : Fin n → ProductCoord, F a A * F a B) ∂haar ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      apply integral_congr_ae
      filter_upwards with B
      exact hPoint A B
    _ = ∑ a : Fin n → ProductCoord, (∫ A : Cfg, F a A ∂haar) ^ 2 :=
      p4Q2LG_originalFullSpatialHaarFiniteDoubleGram_eq_momentSquares H F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rfl

/-- Every degree of the true full-spatial Wilson feature Haar
quadratic energy is nonnegative, even for arbitrary signed ψ. -/
theorem p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_nonneg
    (ψ : C(Cfg, ℝ)) (n : ℕ) :
    0 ≤ p4Q2LG_originalFullSpatialHomogeneousWilsonHaarEnergy H ψ n := by
  rw [p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_eq_momentSquares]
  exact Finset.sum_nonneg (fun a ha => sq_nonneg _)

/-- If one full-spatial homogeneous Wilson energy vanishes,
each original degree-n matrix-coordinate monomial Haar moment
must vanish: a precise finite-volume no-cancellation theorem. -/
theorem p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_zero_imp_all_moments_zero
    (ψ : C(Cfg, ℝ)) (n : ℕ)
    (hzero : p4Q2LG_originalFullSpatialHomogeneousWilsonHaarEnergy H ψ n = 0) :
    ∀ a : Fin n → ProductCoord,
      (∫ A : Cfg, ψ A * Mon n a A ∂haar) = 0 := by
  classical
  rw [p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_eq_momentSquares] at hzero
  intro a
  have hle :
      (∫ A : Cfg, ψ A * Mon n a A ∂haar) ^ 2 ≤
        ∑ z : Fin n → ProductCoord,
          (∫ A : Cfg, ψ A * Mon n z A ∂haar) ^ 2 :=
    Finset.single_le_sum
      (f := fun z : Fin n → ProductCoord =>
        (∫ A : Cfg, ψ A * Mon n z A ∂haar) ^ 2)
      (s := Finset.univ) (fun z hz => sq_nonneg _) (Finset.mem_univ a)
  rw [hzero] at hle
  nlinarith [sq_nonneg (∫ A : Cfg, ψ A * Mon n a A ∂haar)]

/-- Any nonzero actual full-spatial coordinate monomial moment
witnesses strictly positive homogeneous energy of exactly that
degree. No source rank or spectral lower bound is assumed. -/
theorem p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_pos_of_moment_ne
    (ψ : C(Cfg, ℝ)) (n : ℕ) (a : Fin n → ProductCoord)
    (hMoment : (∫ A : Cfg, ψ A * Mon n a A ∂haar) ≠ 0) :
    0 < p4Q2LG_originalFullSpatialHomogeneousWilsonHaarEnergy H ψ n := by
  rw [p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_eq_momentSquares]
  have hPositive :
      0 < (∫ A : Cfg, ψ A * Mon n a A ∂haar) ^ 2 :=
    sq_pos_of_ne_zero hMoment
  have hLe :
      (∫ A : Cfg, ψ A * Mon n a A ∂haar) ^ 2 ≤
        ∑ z : Fin n → ProductCoord,
          (∫ A : Cfg, ψ A * Mon n z A ∂haar) ^ 2 :=
    Finset.single_le_sum
      (f := fun z : Fin n → ProductCoord =>
        (∫ A : Cfg, ψ A * Mon n z A ∂haar) ^ 2)
      (s := Finset.univ)
      (fun z hz => sq_nonneg _) (Finset.mem_univ a)
  exact lt_of_lt_of_le hPositive hLe

/-- For positive Wilson coupling, every finite Taylor coefficient
of the ACTUAL all-spatial-link real Wilson homogeneous Haar
energy is nonnegative. -/
theorem p4Q2LG_originalFullSpatialPositiveWilsonTaylorEnergyTerm_nonneg
    (ψ : C(Cfg, ℝ)) (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ (b ^ n / (Nat.factorial n : ℝ)) *
      p4Q2LG_originalFullSpatialHomogeneousWilsonHaarEnergy H ψ n := by
  exact mul_nonneg
    (div_nonneg (pow_nonneg hb n) (by positivity))
    (p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_nonneg H ψ n)

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LG_originalFullSpatialHaarFiniteDoubleGram_eq_momentSquares
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LG_originalFullSpatialHaarFiniteDoubleGram_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_eq_momentSquares
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_zero_imp_all_moments_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LG_originalFullSpatialHomogeneousHaarEnergy_pos_of_moment_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LG_originalFullSpatialPositiveWilsonTaylorEnergyTerm_nonneg
