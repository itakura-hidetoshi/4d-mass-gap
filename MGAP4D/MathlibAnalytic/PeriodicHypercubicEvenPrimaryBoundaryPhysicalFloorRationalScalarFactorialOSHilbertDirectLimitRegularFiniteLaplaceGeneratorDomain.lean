import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularHamiltonianLaplaceResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularYosidaExponentialConvergence
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

/-!
# Positive resolvent range and the actual regular OS generator domain

The canonical regular factorial-OS construction already contains two same-root objects:

* finite Laplace vectors `R_{lambda,h} x`, known to lie in the actual right-generator domain and to
  satisfy the exact finite-time Hamiltonian-shift identity;
* the bounded positive resolvent `R_lambda = (lambda I + Hbar)⁻¹` of the nonnegative self-adjoint
  graph-closed Hamiltonian.

This file identifies them at infinite Euclidean time.  Closed-shift injectivity shows that every
finite Laplace vector is the positive resolvent applied to its finite-time shifted value.  Exponential
terminal decay therefore gives

`R_{lambda,n} x -> R_lambda x`.

Passing the original semigroup action through this limit yields the exact resolvent-orbit formula

`T_t R_lambda x = exp(lambda t) (R_lambda x - R_{lambda,t} x)`.

The right-hand side has an explicit derivative at zero, proving directly -- without assuming the
original generator is already closed -- that the whole range of the positive resolvent lies in the
actual right-generator domain.  Surjectivity of `lambda I + Hbar` then gives the reverse domain
inclusion and hence exact equality between the original semigroup generator domain and the closed
Hamiltonian domain.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

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

/-- The canonical coercion from nonnegative real time to real time preserves the strict
right-neighborhood filter at zero. -/
theorem fixedSlotHilbertDirectLimitRegular_nnreal_coe_tendsto_zero_right :
    Tendsto (fun h : NNReal => (h : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
  change Filter.map NNReal.toReal
      (nhdsWithin (0 : NNReal) (Ioi 0)) ≤
    nhdsWithin (0 : ℝ) (Ioi 0)
  rw [NNReal.map_coe_nhdsGT]
  simp only [NNReal.coe_zero]
  exact le_rfl

/-- A finite Laplace vector is exactly the positive resolvent applied to its closed-Hamiltonian
shift.  This is simply uniqueness of the preimage under the injective positive shift. -/
theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_eq_positiveResolvent_closedShift
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (h : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x =
      P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda
          (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain lambda h x)) := by
  have hdom :
      P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain lambda h x =
        P.fixedSlotHilbertDirectLimitRegularPositiveResolventDomain lambda hlambda
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda
            (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain lambda h x)) := by
    apply P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_injective hlambda
    exact
      (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_positiveResolventDomain
        lambda hlambda
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda
          (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain lambda h x))).symm
  have hcoe := congrArg
    (fun z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain =>
      (z : P.fixedSlotHilbertDirectLimitRegularSubspace)) hdom
  simpa only [P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain_coe,
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_apply] using hcoe

/-- Natural-time finite Laplace vectors converge strongly to the positive resolvent. -/
theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_nat_tendsto_positiveResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda (n : NNReal) x)
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x)) := by
  have hshift :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_finiteLaplace_tendsto
      hlambda x
  have hmap :=
    (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda).continuous.continuousAt.tendsto.comp
      hshift
  convert hmap using 1
  funext n
  exact
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_eq_positiveResolvent_closedShift
      lambda hlambda (n : NNReal) x

/-- The exponentially weighted terminal orbit at width `n+t` is the fixed scalar multiple of the
`T_t`-image of the terminal orbit at width `n`. -/
theorem fixedSlotHilbertDirectLimitRegularExponentialTerminal_nat_add_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (n : ℕ) :
    Real.exp ((-lambda) * ((((n : NNReal) + t : NNReal) : ℝ))) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism ((n : NNReal) + t) x =
      Real.exp ((-lambda) * (t : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (Real.exp ((-lambda) * (n : ℝ)) •
            P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (n : NNReal) x) := by
  rw [map_smul, smul_smul]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply]
  rw [add_comm t (n : NNReal)]
  congr 1
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Positive exponential decay persists after adding a fixed nonnegative time to the natural cutoff. -/
theorem fixedSlotHilbertDirectLimitRegularExponentialTerminal_nat_add_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ =>
        Real.exp ((-lambda) * ((((n : NNReal) + t : NNReal) : ℝ))) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism ((n : NNReal) + t) x)
      atTop (nhds 0) := by
  have hbase :=
    P.fixedSlotHilbertDirectLimitRegular_exponentialTerminal_nat_tendsto_zero hlambda x
  have hmap :=
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t).continuous.continuousAt.tendsto.comp
      hbase
  have hmap0 : Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (Real.exp ((-lambda) * (n : ℝ)) •
            P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (n : NNReal) x))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, map_zero] using hmap
  have hscalar : Tendsto
      (fun _ : ℕ => Real.exp ((-lambda) * (t : ℝ))) atTop
      (nhds (Real.exp ((-lambda) * (t : ℝ)))) := tendsto_const_nhds
  have hsmul := hscalar.smul hmap0
  have hfun :
      (fun n : ℕ =>
        Real.exp ((-lambda) * ((((n : NNReal) + t : NNReal) : ℝ))) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism ((n : NNReal) + t) x) =
      (fun n : ℕ =>
        Real.exp ((-lambda) * (t : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
            (Real.exp ((-lambda) * (n : ℝ)) •
              P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (n : NNReal) x)) := by
    funext n
    exact P.fixedSlotHilbertDirectLimitRegularExponentialTerminal_nat_add_eq lambda t x n
  rw [hfun]
  simpa only [smul_zero] using hsmul

/-- Closed positive shifts of finite Laplace vectors with cutoff `n+t` converge to the original
vector. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_finiteLaplace_nat_add_tendsto
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda
          (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralClosedDomain
            lambda ((n : NNReal) + t) x))
      atTop (nhds x) := by
  have hterminal :=
    P.fixedSlotHilbertDirectLimitRegularExponentialTerminal_nat_add_tendsto_zero hlambda t x
  have hsub : Tendsto
      (fun n : ℕ => x -
        Real.exp ((-lambda) * ((((n : NNReal) + t : NNReal) : ℝ))) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism ((n : NNReal) + t) x)
      atTop (nhds (x - 0)) := tendsto_const_nhds.sub hterminal
  simpa only [sub_zero,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_finiteLaplaceIntegral] using hsub

/-- Finite Laplace vectors with cutoff `n+t` converge to the same positive resolvent. -/
theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_nat_add_tendsto_positiveResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda ((n : NNReal) + t) x)
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x)) := by
  have hshift :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_finiteLaplace_nat_add_tendsto
      hlambda t x
  have hmap :=
    (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda).continuous.continuousAt.tendsto.comp
      hshift
  convert hmap using 1
  funext n
  exact
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_eq_positiveResolvent_closedShift
      lambda hlambda ((n : NNReal) + t) x

/-- Real formula whose positive-time restriction will be the orbit of a positive-resolvent vector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  Real.exp (lambda * r) •
    (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x -
      P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x r)

@[simp]
theorem fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula lambda hlambda x 0 =
      P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x := by
  simp [fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula]

/-- The shifted finite-Laplace primitives converge to the positive-resolvent orbit formula. -/
theorem fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_nat_tendsto_positiveResolventOrbitFormula
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive
          lambda (n : NNReal) x (t : ℝ))
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula
        lambda hlambda x (t : ℝ))) := by
  have hwidth :=
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_nat_add_tendsto_positiveResolvent
      lambda hlambda t x
  have hconst : Tendsto
      (fun _ : ℕ => P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda t x)
      atTop (nhds (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda t x)) :=
    tendsto_const_nhds
  have hsub := hwidth.sub hconst
  have hscalar : Tendsto
      (fun _ : ℕ => Real.exp (lambda * (t : ℝ))) atTop
      (nhds (Real.exp (lambda * (t : ℝ)))) := tendsto_const_nhds
  have hsmul := hscalar.smul hsub
  have hfun :
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive
          lambda (n : NNReal) x (t : ℝ)) =
      (fun n : ℕ => Real.exp (lambda * (t : ℝ)) •
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral
            lambda ((n : NNReal) + t) x -
          P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda t x)) := by
    funext n
    simp [fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive,
      fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral]
  rw [hfun]
  simpa [fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula,
    fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral] using hsmul

/-- Exact semigroup action on every positive-resolvent vector. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolvent_semigroup_action
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x) =
      P.fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula
        lambda hlambda x (t : ℝ) := by
  have hfinite :=
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_nat_tendsto_positiveResolvent
      lambda hlambda x
  have hleft :=
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t).continuous.continuousAt.tendsto.comp
      hfinite
  have hleft' : Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda (n : NNReal) x))
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x))) := by
    simpa only [Function.comp_apply] using hleft
  have hright :=
    P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_nat_tendsto_positiveResolventOrbitFormula
      lambda hlambda t x
  have hfun :
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda (n : NNReal) x)) =
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive
          lambda (n : NNReal) x (t : ℝ)) := by
    funext n
    exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_finiteLaplaceIntegral
      lambda t (n : NNReal) x
  rw [hfun] at hleft'
  exact tendsto_nhds_unique hleft' hright

/-- The positive-resolvent orbit formula has derivative `lambda R_lambda x - x` at zero. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula_hasDerivAt_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula lambda hlambda x)
      (lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x - x)
      0 := by
  have hscalar := fixedSlotHilbertDirectLimitRegular_exponentialPrefactor_hasDerivAt_zero lambda
  have hconst : HasDerivAt
      (fun _ : ℝ => P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x)
      0 0 :=
    hasDerivAt_const (x := (0 : ℝ))
      (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x)
  have hprimitive :=
    P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_hasDerivAt lambda x 0
  have hsub := hconst.sub hprimitive
  have hproduct := hscalar.smul hsub
  convert hproduct using 1
  simp only [fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula,
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_apply,
    P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_zero,
    mul_zero, Real.exp_zero, one_smul]
  module

/-- Difference quotient of a positive-resolvent vector is the slope of its explicit orbit formula. -/
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_positiveResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
        (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x) t =
      (t : ℝ)⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula
            lambda hlambda x (t : ℝ) -
          P.fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula
            lambda hlambda x 0) := by
  unfold fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
  rw [P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_semigroup_action]
  rw [P.fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula_zero]

/-- Every positive-resolvent vector has the expected actual right-generator value. -/
theorem fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_positiveResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
      (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x)
      (lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x - x) := by
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  have hreal :=
    (P.fixedSlotHilbertDirectLimitRegularPositiveResolventOrbitFormula_hasDerivAt_zero
      lambda hlambda x).tendsto_slope_zero_right
  have hcomp := hreal.comp fixedSlotHilbertDirectLimitRegular_nnreal_coe_tendsto_zero_right
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_positiveResolvent,
    zero_add] using hcomp

/-- The range of every positive resolvent lies in the actual generator domain of the original OS
semigroup. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolvent_mem_rightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x ∈
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x - x,
    P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_positiveResolvent lambda hlambda x⟩

/-- Positive resolvent bundled in the original actual generator domain. -/
noncomputable def fixedSlotHilbertDirectLimitRegularPositiveResolventGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x,
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_mem_rightGeneratorDomain lambda hlambda x⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularPositiveResolventGeneratorDomain_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    (P.fixedSlotHilbertDirectLimitRegularPositiveResolventGeneratorDomain lambda hlambda x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x := rfl

/-- Exact original generator value on positive-resolvent vectors. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_positiveResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightGenerator
        (P.fixedSlotHilbertDirectLimitRegularPositiveResolventGeneratorDomain lambda hlambda x) =
      lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x - x := by
  apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
      (P.fixedSlotHilbertDirectLimitRegularPositiveResolventGeneratorDomain lambda hlambda x))
  exact P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_positiveResolvent lambda hlambda x

/-- Exact original Hamiltonian value on positive-resolvent vectors. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_positiveResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularPositiveResolventGeneratorDomain lambda hlambda x) =
      x - lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda x := by
  rw [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply]
  rw [P.fixedSlotHilbertDirectLimitRegularRightGenerator_positiveResolvent]
  module

/-- Every vector in the graph-closed Hamiltonian domain already belongs to the actual original
right-generator domain. -/
theorem fixedSlotHilbertDirectLimitRegularClosedDomain_mem_rightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    (z : P.fixedSlotHilbertDirectLimitRegularSubspace) ∈
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain := by
  let y : P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift 1 z
  have hdom :
      P.fixedSlotHilbertDirectLimitRegularPositiveResolventDomain 1 one_pos y = z := by
    apply P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_injective one_pos
    simpa only [y] using
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_positiveResolventDomain
        1 one_pos y
  have hmem :=
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_mem_rightGeneratorDomain 1 one_pos y
  rw [P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_apply, hdom] at hmem
  exact hmem

/-- Exact equality of the actual semigroup generator domain and the graph-closed Hamiltonian domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_eq_closedRightHamiltonian_domain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain := by
  apply le_antisymm
  · intro x hx
    exact P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_le_closed.1 hx
  · intro x hx
    exact P.fixedSlotHilbertDirectLimitRegularClosedDomain_mem_rightGeneratorDomain ⟨x, hx⟩

/-- A closed-Hamiltonian-domain vector regarded canonically as an actual original generator-domain
vector, using the proved domain equality. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨(z : P.fixedSlotHilbertDirectLimitRegularSubspace),
    P.fixedSlotHilbertDirectLimitRegularClosedDomain_mem_rightGeneratorDomain z⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z :
      P.fixedSlotHilbertDirectLimitRegularSubspace) = z := rfl

/-- On the now-equal domain, the original OS Hamiltonian is exactly the graph-closed Hamiltonian. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_of_closedDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z) =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z := by
  have h :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_of_rightGenerator
      (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z)
  have hdom :
      P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator
          (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z) = z := by
    apply Subtype.ext
    rfl
  rw [hdom] at h
  exact h.symm

/-- Equivalently, the actual infinitesimal generator is `-Hbar` on the full common domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_of_closedDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularRightGenerator
        (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z) =
      -P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z := by
  have hneg := congrArg Neg.neg
    (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_of_closedDomain z)
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply, neg_neg] using hneg

/-- Core generator/domain identification package. -/
theorem fixedSlotHilbertDirectLimitRegularClosedGeneratorIdentification_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) ∧
    (∀ z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain,
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z) =
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z) ∧
    (∀ z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain,
      P.fixedSlotHilbertDirectLimitRegularRightGenerator
          (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z) =
        -P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_eq_closedRightHamiltonian_domain,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_of_closedDomain,
    P.fixedSlotHilbertDirectLimitRegularRightGenerator_of_closedDomain⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D