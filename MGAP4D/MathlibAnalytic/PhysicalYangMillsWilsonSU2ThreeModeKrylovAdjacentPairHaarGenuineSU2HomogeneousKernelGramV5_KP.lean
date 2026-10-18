import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGenuineSU2HaarFiniteGramSquaresV5_KO
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2FeatureTensorMonomialV5_KN
import Mathlib.Tactic

/-!
# P4-Q2-KP — each genuine SU(2) Wilson inner-product homogeneous kernel has
# a manifestly positive double-Haar quadratic form

KN (canonical PR #5688) proves for EACH degree n the exact original
SU(2) matrix-realification coordinate-monomial Gram expansion

  <Phi(g),Phi(h)>^n = sum_a m_a(g) * m_a(h).

KO (canonical PR #5689) proves that integrating a FINITE Gram of
continuous real SU(2) functions twice against the same true normalized
SU(2) Haar reference gives the sum of the squares of their Haar moments.

Combine these exact theorems for any real continuous signed test ψ:

  ∫g ∫h ψ(g)ψ(h)<Phi(g),Phi(h)>^n dν(h)dν(g)
       = sum_a (∫g ψ(g)m_a(g)dν(g))² ≥ 0.

If even ONE degree-n original matrix-coordinate monomial moment of ψ
is nonzero, its genuine order-n double-Haar Wilson Gram is strictly
positive. No independent-Haar POSTERIOR, synthetic GI detector rank,
new axiom/sorry/admit, unverified Taylor interchange, H1-C3, or
continuum 4D Yang–Mills gap is asserted.

This is the exact homogeneous positive-kernel bridge needed before
summation to the full exponential at positive Wilson coupling.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Coord" => ((Fin 2 × Fin 2) × Bool)
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "Mono" => p4Q2KN_originalSU2MatrixCoordinateMonomial

/-- The exact n-th homogeneous REAL Wilson kernel's signed double-Haar
quadratic form equals a finite sum of the SQUARES of actual SU(2)
coordinate-monomial moments of its SAME continuous signed source. -/
theorem p4Q2KP_originalSU2HomogeneousDoubleHaar_eq_monomialMomentsSq
    (ψ : C(Gauge, ℝ)) (n : ℕ) :
    (∫ g : Gauge, ∫ h : Gauge,
      ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n ∂nu ∂nu) =
    ∑ a : Fin n → Coord,
      (∫ g : Gauge, ψ g * Mono n a g ∂nu) ^ 2 := by
  classical
  let F : (Fin n → Coord) → C(Gauge, ℝ) :=
    fun a => ψ * Mono n a
  have hPoint (g h : Gauge) :
      ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n =
        ∑ a : Fin n → Coord, F a g * F a h := by
    rw [p4Q2KN_originalSU2RealFeatureInnerPow_eq_coordinateMonomialGram]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [F]
    simp only [ContinuousMap.mul_apply]
    ring
  calc
    (∫ g : Gauge, ∫ h : Gauge,
      ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n ∂nu ∂nu) =
        ∫ g : Gauge, ∫ h : Gauge,
          (∑ a : Fin n → Coord, F a g * F a h) ∂nu ∂nu := by
      apply integral_congr_ae
      filter_upwards with g
      apply integral_congr_ae
      filter_upwards with h
      exact hPoint g h
    _ = ∑ a : Fin n → Coord, (∫ g : Gauge, F a g ∂nu) ^ 2 :=
      p4Q2KO_originalSU2HaarFiniteDoubleGram_eq_sumMomentsSq F
    _ = ∑ a : Fin n → Coord,
        (∫ g : Gauge, ψ g * Mono n a g ∂nu) ^ 2 := by
      rfl

/-- Every homogeneous term of the TRUE positive-coupling SU(2)
Wilson exponential kernel yields a nonnegative genuine Haar
quadratic form, because each is a sum of literal moment squares. -/
theorem p4Q2KP_originalSU2HomogeneousDoubleHaar_nonneg
    (ψ : C(Gauge, ℝ)) (n : ℕ) :
    0 ≤ (∫ g : Gauge, ∫ h : Gauge,
      ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n ∂nu ∂nu) := by
  rw [p4Q2KP_originalSU2HomogeneousDoubleHaar_eq_monomialMomentsSq]
  exact Finset.sum_nonneg (fun a ha => sq_nonneg _)

/-- If ONE actual matrix coordinate monomial has nonzero signed
Haar moment against a continuous source, the corresponding
homogeneous Wilson double-Haar quadratic form is STRICTLY positive.
This is a proved analytic implication, not an assumed rank. -/
theorem p4Q2KP_originalSU2HomogeneousDoubleHaar_pos_of_monomialMoment_ne
    (ψ : C(Gauge, ℝ)) (n : ℕ) (a : Fin n → Coord)
    (hMoment : (∫ g : Gauge, ψ g * Mono n a g ∂nu) ≠ 0) :
    0 < (∫ g : Gauge, ∫ h : Gauge,
      ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n ∂nu ∂nu) := by
  rw [p4Q2KP_originalSU2HomogeneousDoubleHaar_eq_monomialMomentsSq]
  have hSq :
      0 < (∫ g : Gauge, ψ g * Mono n a g ∂nu) ^ 2 := by
    exact sq_pos_of_ne_zero hMoment
  have hSingle :
      (∫ g : Gauge, ψ g * Mono n a g ∂nu) ^ 2 ≤
        ∑ k : Fin n → Coord,
          (∫ g : Gauge, ψ g * Mono n k g ∂nu) ^ 2 :=
    Finset.single_le_sum
      (f := fun k : Fin n → Coord =>
        (∫ g : Gauge, ψ g * Mono n k g ∂nu) ^ 2)
      (s := Finset.univ) (fun k hk => sq_nonneg _) (Finset.mem_univ a)
  exact lt_of_lt_of_le hSq hSingle

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KP_originalSU2HomogeneousDoubleHaar_eq_monomialMomentsSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KP_originalSU2HomogeneousDoubleHaar_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KP_originalSU2HomogeneousDoubleHaar_pos_of_monomialMoment_ne
