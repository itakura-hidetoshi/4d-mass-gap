import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularYosidaBoundedExponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Contraction of bounded Yosida exponential semigroups

For the same-root regular OS Hilbert sector, the dyadic Yosida resolvent `J_{2^n}` is already a
contraction and the bounded negative Yosida generator is

`A_n = -H_{2^n} = -2^n (I - J_{2^n})`.

The contraction of `J_{2^n}` implies dissipativity of `A_n` directly by Cauchy--Schwarz.  Combining
this with the already constructed Banach-algebra exponential derivative gives

`d/dt ‖exp(t A_n) y‖² ≤ 0`.

Hence every positive-time bounded Yosida exponential is a contraction, both pointwise and in
operator norm.  No spectral functional calculus and no identification with the original OS
semigroup is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology NormedSpace
open scoped InnerProductSpace LinearPMap RealInnerProductSpace

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

/- Pin only the topological-ring proposition locally, as in the bounded-exponential layer. -/
local instance yosidaContractionOperatorIsTopologicalRing
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] :
    IsTopologicalRing (K →L[ℝ] K) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- Generic commutation of a bounded endomorphism with the exponential on its scalar line. -/
private theorem continuousLinearEndomorphism_comm_exp_smul_apply
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (A : K →L[ℝ] K) (t : ℝ) (y : K) :
    A (NormedSpace.exp (t • A) y) = NormedSpace.exp (t • A) (A y) := by
  letI : NormedAlgebra ℚ (K →L[ℝ] K) :=
    NormedAlgebra.restrictScalars ℚ ℝ (K →L[ℝ] K)
  have hcommBase : Commute A (t • A) := by
    change A * (t • A) = (t • A) * A
    ext x
    change A (t • A x) = t • A (A x)
    rw [A.map_smul]
  have hcommExp : Commute A (NormedSpace.exp (t • A)) := hcommBase.exp_right
  have happ := congrArg (fun B : K →L[ℝ] K => B y) hcommExp.eq
  simpa using happ

/-- Generic pointwise derivative of the exponential scalar line through a bounded endomorphism. -/
private theorem continuousLinearEndomorphism_exp_smul_apply_hasDerivAt
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (A : K →L[ℝ] K) (t : ℝ) (y : K) :
    HasDerivAt
      (fun r : ℝ => NormedSpace.exp (r • A) y)
      (A (NormedSpace.exp (t • A) y)) t := by
  have hOp : HasDerivAt
      (fun r : ℝ => NormedSpace.exp (r • A))
      (NormedSpace.exp (t • A) * A) t := by
    exact hasDerivAt_exp_smul_const
      (𝕂 := ℝ) (𝔸 := K →L[ℝ] K) A t
  have hConst : HasFDerivAt
      (fun _ : ℝ => y)
      (0 : ℝ →L[ℝ] K) t :=
    hasFDerivAt_const y t
  have hDerivRaw := (hOp.hasFDerivAt.clm_apply hConst).hasDerivAt
  have hDeriv : HasDerivAt
      (fun r : ℝ => NormedSpace.exp (r • A) y)
      ((NormedSpace.exp (t • A) * A) y) t := by
    simpa using hDerivRaw
  rw [continuousLinearEndomorphism_comm_exp_smul_apply A t y]
  simpa using hDeriv

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The negative dyadic Yosida generator is dissipative. -/
theorem fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian_inner_nonpos
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian n y) y ≤ 0 := by
  have hJ :
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y‖ ≤ ‖y‖ := by
    change
      ‖P.fixedSlotHilbertDirectLimitRegularYosidaResolvent
          (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
          (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n) y‖ ≤ ‖y‖
    exact P.fixedSlotHilbertDirectLimitRegularYosidaResolvent_norm_bound
      (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
      (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n) y
  have hinner :
      inner ℝ (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y) y ≤ inner ℝ y y := by
    calc
      inner ℝ (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y) y ≤
          ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y‖ * ‖y‖ :=
        real_inner_le_norm _ _
      _ ≤ ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg y)
      _ = inner ℝ y y := (real_inner_self_eq_norm_mul_norm y).symm
  have hscale : 0 ≤ fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n :=
    (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n).le
  unfold fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian
  rw [ContinuousLinearMap.neg_apply]
  unfold fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian
  rw [P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_apply, inner_neg_left]
  apply neg_nonpos.mpr
  rw [real_inner_smul_left, inner_sub_left]
  exact mul_nonneg hscale (sub_nonneg.mpr hinner)

/-- Pointwise derivative of the bounded Yosida exponential orbit. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_apply_hasDerivAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (t : ℝ) (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    HasDerivAt
      (fun r : ℝ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n r y)
      (P.fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian n
        (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n t y)) t := by
  let K := P.fixedSlotHilbertDirectLimitRegularSubspace
  letI : CompleteSpace K := P.fixedSlotHilbertDirectLimitRegularSubspace_completeSpace
  let A : K →L[ℝ] K :=
    P.fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian n
  have hA := continuousLinearEndomorphism_exp_smul_apply_hasDerivAt A t y
  simpa only [fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal, K, A] using hA

/-- The squared norm of every bounded Yosida exponential orbit has nonpositive derivative. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_norm_sq_hasDerivAt_nonpos
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (t : ℝ) (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ∃ d : ℝ,
      HasDerivAt
        (fun r : ℝ => ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n r y‖ ^ 2)
        d t ∧ d ≤ 0 := by
  let z := P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n t y
  let A := P.fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian n
  have horbit := P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_apply_hasDerivAt
    n t y
  have hsq := horbit.norm_sq
  refine ⟨2 * inner ℝ z (A z), ?_, ?_⟩
  · simpa only [z, A] using hsq
  · have hAleft :=
      P.fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian_inner_nonpos n z
    have hAright : inner ℝ z (A z) ≤ 0 := by
      rw [real_inner_comm]
      simpa only [A] using hAleft
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) hAright

/-- Positive-time bounded Yosida exponentials are pointwise contractions. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (t : NNReal) (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t y‖ ≤ ‖y‖ := by
  let f : ℝ → ℝ := fun r =>
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n r y‖ ^ 2
  have hdiff : Differentiable ℝ f := by
    intro r
    rcases P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_norm_sq_hasDerivAt_nonpos
      n r y with ⟨d, hd, _⟩
    exact hd.differentiableAt
  have hderiv : ∀ r : ℝ, deriv f r ≤ 0 := by
    intro r
    rcases P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_norm_sq_hasDerivAt_nonpos
      n r y with ⟨d, hd, hdnonpos⟩
    rw [hd.deriv]
    exact hdnonpos
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
  have hmono := image_sub_le_mul_sub_of_deriv_le
    (f := f) hdiff (C := (0 : ℝ)) hderiv (x := (0 : ℝ)) (y := (t : ℝ)) ht
  have hsq :
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    have hzero :
        P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n 0 y = y := by
      rw [P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_zero n]
      rfl
    have hmono' : f (t : ℝ) - f 0 ≤ 0 := by
      simpa using hmono
    have hft : f (t : ℝ) ≤ f 0 := sub_nonpos.mp hmono'
    change
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n (t : ℝ) y‖ ^ 2 ≤
        ‖y‖ ^ 2
    dsimp [f] at hft
    rw [hzero] at hft
    exact hft
  nlinarith [norm_nonneg
    (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t y), norm_nonneg y]

/-- Positive-time bounded Yosida exponentials have operator norm at most one. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_opNorm_le_one
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (t : NNReal) :
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simpa using P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_norm_le n t y

/-- Contraction package for all dyadic bounded Yosida exponentials. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_contraction_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (t : NNReal) :
    (∀ y : P.fixedSlotHilbertDirectLimitRegularSubspace,
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t y‖ ≤ ‖y‖) ∧
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t‖ ≤ 1 := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_norm_le n t,
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_opNorm_le_one n t⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D