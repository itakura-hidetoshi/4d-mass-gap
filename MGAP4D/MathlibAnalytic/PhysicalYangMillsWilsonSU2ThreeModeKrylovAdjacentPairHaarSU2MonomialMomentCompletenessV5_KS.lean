import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2FeatureTensorMonomialV5_KN
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Tactic

/-!
# P4-Q2-KS — genuine SU(2) coordinate monomials give complete Haar moment tests

KK/KL give the actual SU(2) coordinate polynomial Stone–Weierstrass density
and continuous Haar moment Riesz separation. KN defines the genuine
finite-degree real/imaginary matrix monomials. We show every product of
actual coordinate generators is some KN monomial, including degree zero,
and use the pinned Algebra.adjoin_eq_span / Submodule.span_le
and the canonical kernel of the bounded linear functional to transfer
annihilation of all monomials to the entire dense algebra.

Thus any nonzero continuous signed SU(2) source has a nonzero ACTUAL
normalized Haar moment against some finite-degree SU(2) coordinate
monomial. Haar remains the original reference measure and is not a
replacement for the interacting Wilson posteriors. No arbitrary rank,
sorry/admit/axiom, or claim about the remaining physical GI detector.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Coord" => ((Fin 2 × Fin 2) × Bool)
local notation "Mono" => p4Q2KN_originalSU2MatrixCoordinateMonomial
local notation "Alg" => p4Q2KK_originalSU2MatrixCoordinateAlgebra
local notation "nu" => normalizedCompactHaar Gauge

theorem p4Q2KS_originalSU2CoordinateMonomial_mul
    (n m : ℕ) (a : Fin n → Coord) (b : Fin m → Coord) :
    Mono n a * Mono m b = Mono (n + m) (Fin.append a b) := by
  ext g
  simp only [ContinuousMap.mul_apply,
    p4Q2KN_originalSU2MatrixCoordinateMonomial_apply]
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem p4Q2KS_originalSU2CoordinateSubmonoid_generated_by_monomials
    (f : C(Gauge, ℝ))
    (hf : f ∈ Submonoid.closure (Set.range p4Q2KK_originalSU2MatrixRealCoordinate)) :
    ∃ n : ℕ, ∃ a : Fin n → Coord, f = Mono n a := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
      obtain ⟨q, rfl⟩ := hf
      refine ⟨1, (fun _ : Fin 1 => q), ?_⟩
      ext g
      simp [p4Q2KN_originalSU2MatrixCoordinateMonomial]
  | one =>
      refine ⟨0, Fin.elim0, ?_⟩
      simp [p4Q2KN_originalSU2MatrixCoordinateMonomial]
  | mul x y _ _ hx hy =>
      obtain ⟨n, a, rfl⟩ := hx
      obtain ⟨m, b, rfl⟩ := hy
      exact ⟨n + m, Fin.append a b,
        p4Q2KS_originalSU2CoordinateMonomial_mul n m a b⟩

theorem p4Q2KS_zero_on_algebra_of_zero_on_all_coordinateMonomials
    (L : C(Gauge, ℝ) →L[ℝ] ℝ)
    (hMon : ∀ (n : ℕ) (a : Fin n → Coord), L (Mono n a) = 0) :
    ∀ f : C(Gauge, ℝ), f ∈ Alg → L f = 0 := by
  intro f hf
  have hSpan : f ∈ Submodule.span ℝ
      (Submonoid.closure
        (Set.range p4Q2KK_originalSU2MatrixRealCoordinate) :
          Set C(Gauge, ℝ)) := by
    change f ∈ Subalgebra.toSubmodule
      (Algebra.adjoin ℝ (Set.range p4Q2KK_originalSU2MatrixRealCoordinate)) at hf
    rwa [Algebra.adjoin_eq_span] at hf
  -- The kernel is a genuine ℝ-submodule. It contains every original
  -- matrix-coordinate monomial, hence also the entire generated span.
  -- This avoids a dependent span-induction motive that accidentally
  -- reintroduces the already-proved algebra-membership hypothesis.
  have hGenerators :
      (Submonoid.closure
        (Set.range p4Q2KK_originalSU2MatrixRealCoordinate) :
          Set C(Gauge, ℝ)) ⊆
      (L.toLinearMap.ker : Set C(Gauge, ℝ)) := by
    intro x hx
    obtain ⟨n, a, rfl⟩ :=
      p4Q2KS_originalSU2CoordinateSubmonoid_generated_by_monomials x hx
    exact LinearMap.mem_ker.mpr (hMon n a)
  have hSpanKer :
      Submodule.span ℝ
        (Submonoid.closure
          (Set.range p4Q2KK_originalSU2MatrixRealCoordinate) :
            Set C(Gauge, ℝ)) ≤
      L.toLinearMap.ker :=
    Submodule.span_le.mpr hGenerators
  exact LinearMap.mem_ker.mp (hSpanKer hSpan)

theorem p4Q2KS_originalSU2Haar_all_monomialMoments_zero_imp_source_zero
    (ψ : C(Gauge, ℝ))
    (hMon : ∀ (n : ℕ) (a : Fin n → Coord),
      (∫ g : Gauge, ψ g * Mono n a g ∂nu) = 0) :
    ψ = 0 := by
  apply p4Q2KL_originalSU2HaarMomentCLM_separates_sources ψ
  apply p4Q2KS_zero_on_algebra_of_zero_on_all_coordinateMonomials
  intro n a
  rw [p4Q2KL_originalSU2HaarMomentCLM_apply]
  have h := hMon n a
  simpa only [mul_comm] using h

theorem p4Q2KS_originalSU2Haar_exists_nonzero_monomialMoment
    (ψ : C(Gauge, ℝ)) (hψ : ψ ≠ 0) :
    ∃ (n : ℕ) (a : Fin n → Coord),
      (∫ g : Gauge, ψ g * Mono n a g ∂nu) ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hψ
    (p4Q2KS_originalSU2Haar_all_monomialMoments_zero_imp_source_zero ψ hn)

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KS_originalSU2CoordinateMonomial_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KS_originalSU2CoordinateSubmonoid_generated_by_monomials
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KS_zero_on_algebra_of_zero_on_all_coordinateMonomials
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KS_originalSU2Haar_all_monomialMoments_zero_imp_source_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KS_originalSU2Haar_exists_nonzero_monomialMoment
