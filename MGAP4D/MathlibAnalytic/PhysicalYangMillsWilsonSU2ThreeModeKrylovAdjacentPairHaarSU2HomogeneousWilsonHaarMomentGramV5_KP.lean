import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2FeatureTensorMonomialV5_KN
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGenuineSU2HaarFiniteGramSquaresV5_KO
import Mathlib.Tactic

/-!
# P4-Q2-KP — genuine SU(2) Wilson homogeneous kernel Haar energy is a sum of squares

KN proves the exact FINITE all-degree coordinate expansion
  <Phi(g),Phi(h)>^n = Σ_(a : Fin n → Coord) monomial_a(g) monomial_a(h)
for the actual SU(2) defining complex matrix realification Phi.
KO proves the exact double Haar Gram identity for ANY finite family
of continuous tests on the SAME original normalized compact SU(2)
Haar REFERENCE measure used by the true interacting Wilson posteriors.

For every n and every continuous signed real SU(2) source ψ, combine
KN and KO to prove

 ∫g ∫h ψ(g)ψ(h)<Phi(g),Phi(h)>^n dν(h)dν(g)
    = Σ_a (∫g ψ(g) monomial_a(g) dν(g))² ≥ 0.

Moreover, if the n-th genuine homogeneous Haar energy is zero, ALL
true degree-n coordinate monomial moments are zero. There is no
infinite Taylor series or limit interchange in this theorem; this
finite homogeneous positivity is the structural input for the exact
Wilson exponential kernel and integral-transform injectivity proof.

No independent-Haar posterior replacement, unproved rank hypothesis,
sorry/new axioms, GI second context, H1-C3 or continuum mass gap.
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
local notation "Mon" => p4Q2KN_originalSU2MatrixCoordinateMonomial

/-- The genuine n-th homogeneous SU(2) Wilson matrix real-feature
quadratic Haar energy of a continuous real signed source. -/
noncomputable def p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy
    (ψ : C(Gauge, ℝ)) (n : ℕ) : ℝ :=
  ∫ g : Gauge, ∫ h : Gauge,
    ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n ∂nu ∂nu

/-- For EVERY finite degree n, the original SU(2) Wilson feature
Haar energy is exactly the finite SUM OF SQUARES of the original
real matrix-coordinate polynomial moments, with no limiting argument. -/
theorem p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_eq_coordinateMomentSquares
    (ψ : C(Gauge, ℝ)) (n : ℕ) :
    p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy ψ n =
      ∑ a : Fin n → Coord,
        (∫ g : Gauge, ψ g * Mon n a g ∂nu) ^ 2 := by
  let F : (Fin n → Coord) → C(Gauge, ℝ) :=
    fun a => ψ * Mon n a
  have hPoint (g h : Gauge) :
      ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n =
        ∑ a : Fin n → Coord, F a g * F a h := by
    rw [p4Q2KN_originalSU2RealFeatureInnerPow_eq_coordinateMonomialGram]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    change ψ g * ψ h * (Mon n a g * Mon n a h) =
      (ψ g * Mon n a g) * (ψ h * Mon n a h)
    ring
  unfold p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy
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
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rfl

/-- Nonnegative n-th original Wilson real-feature homogeneous Haar
energy, for any continuous signed source and any natural degree. -/
theorem p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_nonneg
    (ψ : C(Gauge, ℝ)) (n : ℕ) :
    0 ≤ p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy ψ n := by
  rw [p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_eq_coordinateMomentSquares]
  exact Finset.sum_nonneg (fun a ha => sq_nonneg _)

/-- If the original n-th homogeneous Wilson Haar energy vanishes,
every degree-n coordinate monomial Haar moment must vanish.
This is a separate NO-CANCELLATION result for each finite degree. -/
theorem p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_zero_forces_all_moments_zero
    (ψ : C(Gauge, ℝ)) (n : ℕ)
    (hzero : p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy ψ n = 0) :
    ∀ a : Fin n → Coord,
      (∫ g : Gauge, ψ g * Mon n a g ∂nu) = 0 := by
  classical
  rw [p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_eq_coordinateMomentSquares] at hzero
  intro a
  have hle :
      (∫ g : Gauge, ψ g * Mon n a g ∂nu) ^ 2 ≤
        ∑ z : Fin n → Coord,
          (∫ g : Gauge, ψ g * Mon n z g ∂nu) ^ 2 :=
    Finset.single_le_sum
      (f := fun z : Fin n → Coord =>
        (∫ g : Gauge, ψ g * Mon n z g ∂nu) ^ 2)
      (s := Finset.univ)
      (fun z hz => sq_nonneg _) (Finset.mem_univ a)
  rw [hzero] at hle
  nlinarith [sq_nonneg (∫ g : Gauge, ψ g * Mon n a g ∂nu)]

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_eq_coordinateMomentSquares
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_zero_forces_all_moments_zero
