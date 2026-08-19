import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularClosedHamiltonian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Finite Laplace resolvent for the same-root regular OS Hamiltonian

For the canonical regular C₀ contraction semigroup, finite Laplace integrals

`R_{λ,h} x = ∫₀ʰ exp(-λs) T_s x ds`

belong to the right-generator domain and satisfy the exact finite-time resolvent identity.  After
bundling them in the graph-closed Hamiltonian domain, the terminal exponentially weighted orbit
vanishes at natural Euclidean times.  Thus every positive shift of the closed Hamiltonian has dense
range; the closed-range theorem upgrades this to surjectivity and hence bijectivity.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace Interval LinearPMap

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

noncomputable def fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) (s : ℝ) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  Real.exp ((-lambda) * s) • P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s

theorem fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_continuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Continuous (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x) := by
  have hscalar : Continuous (fun s : ℝ => Real.exp ((-lambda) * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact hscalar.smul (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x)

theorem fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_intervalIntegrable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) (a b : ℝ) :
    IntervalIntegrable (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x)
      MeasureTheory.volume a b :=
  (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_continuous lambda x)
    .intervalIntegrable a b

@[simp] theorem fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x 0 = x := by
  simp [fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit]

noncomputable def fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) (r : ℝ) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ∫ s in (0 : ℝ)..r, P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s

@[simp] theorem fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x 0 = 0 := by
  simp [fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive]

theorem fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_hasDerivAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) (r : ℝ) :
    HasDerivAt (P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x)
      (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x r) r := by
  simpa only [fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive] using
    ((P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_continuous lambda x)
      .integral_hasStrictDerivAt 0 r).hasDerivAt

noncomputable def fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x (h : ℝ)

theorem fixedSlotHilbertDirectLimitRegular_norm_exponential_terminal_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖Real.exp ((-lambda) * (h : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x‖ ≤
      Real.exp ((-lambda) * (h : ℝ)) * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos ((-lambda) * (h : ℝ)))]
  exact mul_le_mul_of_nonneg_left
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le h x)
    (Real.exp_pos ((-lambda) * (h : ℝ))).le

noncomputable def fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  Real.exp (lambda * r) •
    (P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x ((h : ℝ) + r) -
      P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x r)

@[simp] theorem fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x 0 =
      P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x := by
  simp [fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive,
    fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral]

theorem fixedSlotHilbertDirectLimitRegular_exponentialPrefactor_hasDerivAt_zero
    (lambda : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (lambda * r)) lambda 0 := by
  have hlinear : HasDerivAt (fun r : ℝ => lambda * r) lambda 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_mul lambda
  simpa using hlinear.exp

theorem fixedSlotHilbertDirectLimitRegular_exponentialMovingInterval_hasDerivAt_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    HasDerivAt
      (fun r : ℝ =>
        P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x ((h : ℝ) + r) -
          P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x r)
      (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x (h : ℝ) - x) 0 := by
  have harg : HasDerivAt (fun r : ℝ => (h : ℝ) + r) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add (h : ℝ)
  have hshift : HasDerivAt
      (fun r : ℝ =>
        P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x ((h : ℝ) + r))
      (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x (h : ℝ)) 0 := by
    have hout := P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_hasDerivAt
      lambda x ((h : ℝ) + 0)
    have hcomp := hout.scomp 0 harg
    simpa using hcomp
  have hzero : HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x) x 0 := by
    simpa using P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_hasDerivAt lambda x 0
  exact hshift.sub hzero

theorem fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_hasDerivAt_zero_explicit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x)
      (lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x +
        Real.exp ((-lambda) * (h : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x) 0 := by
  have hscalar := fixedSlotHilbertDirectLimitRegular_exponentialPrefactor_hasDerivAt_zero lambda
  have hinterval :=
    P.fixedSlotHilbertDirectLimitRegular_exponentialMovingInterval_hasDerivAt_zero lambda h x
  have hproduct := hscalar.smul hinterval
  convert hproduct using 1
  · simp only [fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral,
      mul_zero, Real.exp_zero, one_smul, add_zero,
      P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_zero lambda x, sub_zero]
    module
  · unfold fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit
    have hh : Real.toNNReal (h : ℝ) = h := by simp
    rw [hh]

/-- Semigroup action on the exponentially weighted orbit, with the compensating exponential. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_exponentiallyWeightedOrbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (t : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (s : ℝ) (hs : 0 ≤ s) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s) =
      Real.exp (lambda * (t : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x
          (s + (t : ℝ)) := by
  calc
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s) =
      Real.exp ((-lambda) * s) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s) := by
        simp [fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit, map_smul]
    _ = Real.exp ((-lambda) * s) •
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) s := by
        rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_clampedRealOrbit]
    _ = Real.exp ((-lambda) * s) •
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x (s + (t : ℝ)) := by
        rw [P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_endomorphism_eq_add_of_nonneg t x s hs]
    _ = Real.exp (lambda * (t : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x
          (s + (t : ℝ)) := by
        rw [fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit, smul_smul]
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring

theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (t h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x) =
      P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x (t : ℝ) := by
  unfold fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral
  unfold fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t)
    (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_intervalIntegrable
      lambda x 0 (h : ℝ))]
  calc
    (∫ s in (0 : ℝ)..(h : ℝ),
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s)) =
      ∫ s in (0 : ℝ)..(h : ℝ),
        Real.exp (lambda * (t : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x
            (s + (t : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hh : (0 : ℝ) ≤ (h : ℝ) := h.coe_nonneg
        rw [uIcc_of_le hh] at hs
        exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_exponentiallyWeightedOrbit
          lambda t x s hs.1
    _ = Real.exp (lambda * (t : ℝ)) •
        (∫ s in (0 : ℝ)..(h : ℝ),
          P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x
            (s + (t : ℝ))) := by
        rw [intervalIntegral.integral_smul]
    _ = Real.exp (lambda * (t : ℝ)) •
        (∫ s in (t : ℝ)..(h : ℝ) + (t : ℝ),
          P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s) := by
        rw [intervalIntegral.integral_comp_add_right]
        simp
    _ = P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x (t : ℝ) := by
        unfold fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive
        unfold fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive
        congr 1
        symm
        simpa [add_comm] using
          intervalIntegral.integral_interval_sub_left
            (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_intervalIntegrable
              lambda x 0 ((t : ℝ) + (h : ℝ)))
            (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_intervalIntegrable
              lambda x 0 (t : ℝ))

theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h t : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x) t =
      (t : ℝ)⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x (t : ℝ) -
          P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x 0) := by
  unfold fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_finiteLaplaceIntegral]
  rw [P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_zero]

theorem fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
      (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x)
      (lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x +
        Real.exp ((-lambda) * (h : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x) := by
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  have hreal :=
    (P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_hasDerivAt_zero_explicit
      lambda h x).tendsto_slope_zero_right
  have hcomp := hreal.comp fixedSlotHilbertDirectLimit_nnreal_coe_tendsto_zero_right
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_finiteLaplaceIntegral,
    zero_add] using hcomp

theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_mem_rightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x ∈
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x +
      Real.exp ((-lambda) * (h : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x,
    P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_finiteLaplaceIntegral lambda h x⟩

noncomputable def fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x,
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_mem_rightGeneratorDomain lambda h x⟩

@[simp] theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x := rfl

theorem fixedSlotHilbertDirectLimitRegularRightGenerator_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightGenerator
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x) =
      lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x +
        Real.exp ((-lambda) * (h : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x := by
  apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
      (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x))
  exact P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_finiteLaplaceIntegral lambda h x

noncomputable def fixedSlotHilbertDirectLimitRegularRightHamiltonianShift
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain →ₗ[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  lambda • P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain.subtype +
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian

@[simp] theorem fixedSlotHilbertDirectLimitRegularRightHamiltonianShift_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (z : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianShift lambda z =
      lambda • (z : P.fixedSlotHilbertDirectLimitRegularSubspace) +
        P.fixedSlotHilbertDirectLimitRegularRightHamiltonian z := rfl

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonianShift_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianShift lambda
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x) =
      x - Real.exp ((-lambda) * (h : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x := by
  rw [P.fixedSlotHilbertDirectLimitRegularRightHamiltonianShift_apply,
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain_coe,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply,
    P.fixedSlotHilbertDirectLimitRegularRightGenerator_finiteLaplaceIntegral]
  module

noncomputable def fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_le_closed.1
      (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_mem_rightGeneratorDomain lambda h x)⟩

@[simp] theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain lambda h x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x := rfl

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain lambda h x) =
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x) := by
  exact (P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_le_closed.2
    (x := P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x)
    (y := P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain lambda h x) rfl).symm

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain lambda h x) =
      x - Real.exp ((-lambda) * (h : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x := by
  simpa only [P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_finiteLaplaceIntegral,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianShift_apply,
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain_coe,
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain_coe] using
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonianShift_finiteLaplaceIntegral lambda h x

theorem fixedSlotHilbertDirectLimitRegular_exponentialWeight_nat_tendsto_zero
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n : ℕ => Real.exp ((-lambda) * (n : ℝ))) atTop (nhds 0) := by
  have hnonneg : 0 ≤ Real.exp (-lambda) := Real.exp_nonneg _
  have hlt : Real.exp (-lambda) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hlambda)
  have hpow : Tendsto (fun n : ℕ => (Real.exp (-lambda)) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt
  apply hpow.congr'
  exact Filter.Eventually.of_forall fun n => by
    change Real.exp (-lambda) ^ n = Real.exp ((-lambda) * (n : ℝ))
    rw [← Real.exp_nat_mul]
    congr 1
    ring

theorem fixedSlotHilbertDirectLimitRegular_exponentialTerminal_nat_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ => Real.exp ((-lambda) * (n : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (n : NNReal) x)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun n : ℕ => Real.exp ((-lambda) * (n : ℝ)) * ‖x‖)
  · intro n
    simpa using P.fixedSlotHilbertDirectLimitRegular_norm_exponential_terminal_le
      lambda (n : NNReal) x
  · simpa only [zero_mul] using
      (fixedSlotHilbertDirectLimitRegular_exponentialWeight_nat_tendsto_zero hlambda).mul_const ‖x‖

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_finiteLaplace_tendsto
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda
          (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain
            lambda (n : NNReal) x))
      atTop (nhds x) := by
  have hterminal :=
    P.fixedSlotHilbertDirectLimitRegular_exponentialTerminal_nat_tendsto_zero hlambda x
  have hsub : Tendsto
      (fun n : ℕ => x - Real.exp ((-lambda) * (n : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (n : NNReal) x)
      atTop (nhds (x - 0)) := tendsto_const_nhds.sub hterminal
  simpa only [sub_zero,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_finiteLaplaceIntegral] using hsub

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_denseRange
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Dense (Set.range (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  apply mem_closure_of_tendsto
    (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_finiteLaplace_tendsto hlambda x)
  exact Filter.Eventually.of_forall fun n =>
    ⟨P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain
      lambda (n : NNReal) x, rfl⟩

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_surjective
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Surjective (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda) :=
  (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_surjective_iff_denseRange
    hlambda).2
    (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_denseRange hlambda)

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_bijective
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Bijective (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda) :=
  ⟨P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_injective hlambda,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_surjective hlambda⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
