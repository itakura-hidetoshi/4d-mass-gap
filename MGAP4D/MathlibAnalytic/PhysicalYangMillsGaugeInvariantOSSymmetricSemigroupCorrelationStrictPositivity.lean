import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationLogMidpoint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Strict positivity of unregularized physical OS correlations

A strongly continuous symmetric additive semigroup on a real Hilbert space is
injective at every finite nonnegative time.  The proof is elementary and uses
only symmetry, the semigroup law, and strong continuity at time zero: if
`U_t x = 0`, symmetry shows `U_{t/2} x = 0`; iterating along the dyadic times
`t (1/2)^n -> 0` and using strong continuity forces `x = 0`.

Applied to the completed physical OS semigroup, the existing identity

`C_psi(t) = ||T_{t/2} psi||^2`

therefore gives strict positivity for every nonzero physical state, without an
additive epsilon regularization, a spectral theorem, or a new physical
assumption.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Topology
open scoped InnerProductSpace

/-- A strongly continuous symmetric additive semigroup of bounded operators on
a real Hilbert space cannot annihilate a nonzero vector at any finite
nonnegative time.

The key dyadic step is

`||U_s x||^2 = <x, U_{2s} x>`.

Thus vanishing at time `2s` implies vanishing at time `s`; repeated halving and
strong continuity at zero then recover the original vector. -/
theorem symmetricStronglyContinuousSemigroup_ne_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : NNReal → H →L[ℝ] H)
    (hZero : U 0 = ContinuousLinearMap.id ℝ H)
    (hAdd : ∀ s t, U (s + t) = (U s).comp (U t))
    (hSymmetric : ∀ t x y,
      inner ℝ (U t x) y = inner ℝ x (U t y))
    (hContinuous : ∀ x, ContinuousAt (fun t : NNReal => U t x) 0)
    (t : NNReal) {x : H} (hx : x ≠ 0) :
    U t x ≠ 0 := by
  intro htx
  let tau : ℕ → NNReal := fun n => t * (1 / 2 : NNReal) ^ n
  have htauZero : ∀ n : ℕ, U (tau n) x = 0 := by
    intro n
    induction n with
    | zero =>
        simpa [tau] using htx
    | succ n ihn =>
        have hdouble : tau (n + 1) + tau (n + 1) = tau n := by
          dsimp [tau]
          rw [pow_succ]
          calc
            t * ((1 / 2 : NNReal) ^ n * (1 / 2)) +
                t * ((1 / 2 : NNReal) ^ n * (1 / 2)) =
              (t * (1 / 2 : NNReal) ^ n) *
                ((1 / 2 : NNReal) + (1 / 2 : NNReal)) := by
                  ring
            _ = t * (1 / 2 : NNReal) ^ n := by norm_num
        have hsq : ‖U (tau (n + 1)) x‖ ^ 2 = 0 := by
          calc
            ‖U (tau (n + 1)) x‖ ^ 2 =
                inner ℝ (U (tau (n + 1)) x) (U (tau (n + 1)) x) :=
              (real_inner_self_eq_norm_sq _).symm
            _ = inner ℝ x
                (U (tau (n + 1)) (U (tau (n + 1)) x)) :=
              hSymmetric (tau (n + 1)) x (U (tau (n + 1)) x)
            _ = inner ℝ x
                (U (tau (n + 1) + tau (n + 1)) x) := by
              rw [hAdd]
              rfl
            _ = inner ℝ x (U (tau n) x) := by rw [hdouble]
            _ = 0 := by simp [ihn]
        have hnorm : ‖U (tau (n + 1)) x‖ = 0 := by
          nlinarith [norm_nonneg (U (tau (n + 1)) x)]
        exact norm_eq_zero.mp hnorm
  have hratio : (1 / 2 : NNReal) < 1 := by norm_num
  have hpow :
      Tendsto (fun n : ℕ => (1 / 2 : NNReal) ^ n) atTop (nhds 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
  have htau : Tendsto tau atTop (nhds 0) := by
    dsimp [tau]
    simpa using (tendsto_const_nhds.mul hpow :
      Tendsto (fun n : ℕ => t * (1 / 2 : NNReal) ^ n)
        atTop (nhds (t * 0)))
  have hcont :
      Tendsto (fun s : NNReal => U s x) (nhds 0) (nhds x) := by
    simpa [ContinuousAt, hZero] using hContinuous x
  have hseq :
      Tendsto (fun n : ℕ => U (tau n) x) atTop (nhds x) :=
    hcont.comp htau
  have hfun :
      (fun n : ℕ => U (tau n) x) = fun _ : ℕ => (0 : H) :=
    funext htauZero
  rw [hfun] at hseq
  exact hx (tendsto_nhds_unique hseq tendsto_const_nhds)

/-- Every finite-time operator in a strongly continuous symmetric additive
semigroup is injective. -/
theorem symmetricStronglyContinuousSemigroup_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : NNReal → H →L[ℝ] H)
    (hZero : U 0 = ContinuousLinearMap.id ℝ H)
    (hAdd : ∀ s t, U (s + t) = (U s).comp (U t))
    (hSymmetric : ∀ t x y,
      inner ℝ (U t x) y = inner ℝ x (U t y))
    (hContinuous : ∀ x, ContinuousAt (fun t : NNReal => U t x) 0)
    (t : NNReal) :
    Function.Injective (U t) := by
  intro x y hxy
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hnz := symmetricStronglyContinuousSemigroup_ne_zero
    U hZero hAdd hSymmetric hContinuous t hsub
  apply hnz
  simpa only [map_sub, hxy, sub_self]

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Every finite-time completed physical OS operator is injective once the
existing OS inner-product symmetry is available. -/
theorem physicalOperator_injective_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) :
    Function.Injective (T.toPhysicalSemigroup.operator t) := by
  exact symmetricStronglyContinuousSemigroup_injective
    T.toPhysicalSemigroup.operator
    T.toPhysicalSemigroup.operator_zero
    T.toPhysicalSemigroup.operator_add
    hSymmetric
    T.strongContinuousAt_zero
    t

/-- A nonzero physical state remains nonzero under every finite nonnegative
Euclidean-time evolution. -/
theorem physicalOperator_ne_zero_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    T.toPhysicalSemigroup.operator t psi ≠ 0 := by
  intro hzero
  apply hpsi
  apply T.physicalOperator_injective_of_innerSymmetric hSymmetric t
  simpa using hzero

/-- The unregularized physical OS autocorrelation is strictly positive at every
finite nonnegative Euclidean time for every nonzero physical state. -/
theorem physicalCorrelation_pos_of_ne_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    0 < T.physicalCorrelation psi t := by
  have hhalf : t / 2 + t / 2 = t := by
    apply NNReal.eq
    norm_num
  rw [← hhalf,
    T.physicalCorrelation_add_self_eq_norm_sq hSymmetric]
  have hne : T.toPhysicalSemigroup.operator (t / 2) psi ≠ 0 :=
    T.physicalOperator_ne_zero_of_innerSymmetric hSymmetric (t / 2) hpsi
  have hnorm : 0 < ‖T.toPhysicalSemigroup.operator (t / 2) psi‖ :=
    norm_pos_iff.mpr hne
  exact pow_pos hnorm 2

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
