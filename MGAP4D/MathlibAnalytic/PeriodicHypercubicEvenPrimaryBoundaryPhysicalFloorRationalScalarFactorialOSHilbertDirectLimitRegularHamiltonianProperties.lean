import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularGeneratorCore
import Mathlib.Tactic

/-!
# Symmetry, nonnegativity, covariance, and closability of the same-root OS Hamiltonian

The dense same-root generator core is now available on the complete regular factorial-OS Hilbert
sector.  This file transfers finite-time OS symmetry to the infinitesimal generator, derives
Hamiltonian nonnegativity from contraction, proves semigroup covariance of the domain/operator, and
closes sequential closability using dense-domain symmetry.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology Set
open scoped InnerProductSpace

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

theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t) y =
      inner ℝ x (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient y t) := by
  unfold fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
  rw [real_inner_smul_left
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x - x) y (t : ℝ)⁻¹]
  rw [real_inner_smul_right x
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t y - y) (t : ℝ)⁻¹]
  rw [inner_sub_left, inner_sub_right]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_symmetric t x y]

theorem fixedSlotHilbertDirectLimitRegularRightGenerator_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator x)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace) =
      inner ℝ (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator y) := by
  have hx := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue x
  have hy := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue y
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hx hy
  have hyconst : Tendsto
      (fun _ : NNReal => (y : P.fixedSlotHilbertDirectLimitRegularSubspace))
      (nhdsWithin 0 (Ioi 0)) (nhds (y : P.fixedSlotHilbertDirectLimitRegularSubspace)) :=
    tendsto_const_nhds
  have hxconst : Tendsto
      (fun _ : NNReal => (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      (nhdsWithin 0 (Ioi 0)) (nhds (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) :=
    tendsto_const_nhds
  have hleft : Tendsto
      (fun t : NNReal => inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) t)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace))
      (nhdsWithin 0 (Ioi 0))
      (nhds (inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator x)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace))) :=
    Filter.Tendsto.inner (𝕜 := ℝ) hx hyconst
  have hright : Tendsto
      (fun t : NNReal => inner ℝ
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
          (y : P.fixedSlotHilbertDirectLimitRegularSubspace) t))
      (nhdsWithin 0 (Ioi 0))
      (nhds (inner ℝ (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator y))) :=
    Filter.Tendsto.inner (𝕜 := ℝ) hxconst hy
  have hfun :
      (fun t : NNReal => inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) t)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace)) =
      (fun t : NNReal => inner ℝ
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
          (y : P.fixedSlotHilbertDirectLimitRegularSubspace) t)) := by
    funext t
    exact P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_inner_symmetric t x y
  rw [hfun] at hleft
  exact tendsto_nhds_unique hleft hright

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace) =
      inner ℝ (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian y) := by
  simp only [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply,
    inner_neg_left, inner_neg_right]
  exact congrArg Neg.neg
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_inner_symmetric x y)

theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_le_self
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) x ≤
      inner ℝ x x := by
  calc
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) x ≤
        ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x‖ * ‖x‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le t x)
        (norm_nonneg x)
    _ = inner ℝ x x := (real_inner_self_eq_norm_mul_norm x).symm

theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_inner_nonpos
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) (ht : 0 < t) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t) x ≤ 0 := by
  have hsub :
      inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x - x) x ≤ 0 := by
    rw [inner_sub_left]
    exact sub_nonpos.mpr
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_le_self t x)
  have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
  have hinv : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr htReal.le
  have hmul := mul_nonpos_of_nonneg_of_nonpos hinv hsub
  unfold fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
  rw [real_inner_smul_left
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x - x) x (t : ℝ)⁻¹]
  exact hmul

theorem fixedSlotHilbertDirectLimitRegularRightGenerator_inner_nonpos
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator x)
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace) ≤ 0 := by
  have hx := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue x
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hx
  have hxconst : Tendsto
      (fun _ : NNReal => (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      (nhdsWithin 0 (Ioi 0)) (nhds (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) :=
    tendsto_const_nhds
  have hinner : Tendsto
      (fun t : NNReal => inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) t)
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      (nhdsWithin 0 (Ioi 0))
      (nhds (inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator x)
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace))) :=
    Filter.Tendsto.inner (𝕜 := ℝ) hx hxconst
  apply le_of_tendsto_of_tendsto hinner tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_inner_nonpos x t ht

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    0 ≤ inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
  rw [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply, inner_neg_left]
  exact neg_nonneg.mpr
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_inner_nonpos x)

theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_endomorphism
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s x) t =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t) := by
  simp only [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient, map_smul, map_sub]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply t s x]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply s t x]
  rw [add_comm t s]

theorem fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) ∈
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain := by
  refine ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
      (P.fixedSlotHilbertDirectLimitRegularRightGenerator x), ?_⟩
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  have hx := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue x
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hx
  have hmap :=
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s).continuous.continuousAt.tendsto.comp hx
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_endomorphism] using hmap

theorem fixedSlotHilbertDirectLimitRegularRightGenerator_endomorphism
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRightGenerator
        ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s x,
          P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant s x⟩ =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator x) := by
  apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
      ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s x,
        P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant s x⟩)
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  have hx := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue x
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hx
  have hmap :=
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s).continuous.continuousAt.tendsto.comp hx
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_endomorphism] using hmap

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_endomorphism
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s x,
          P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant s x⟩ =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x) := by
  simp only [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply, map_neg]
  rw [P.fixedSlotHilbertDirectLimitRegularRightGenerator_endomorphism]

theorem fixedSlotHilbertDirectLimitRegularRightGenerator_sequentially_closable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : ℕ → P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain}
    {eta : P.fixedSlotHilbertDirectLimitRegularSubspace}
    (hx : Tendsto
      (fun n => (x n : P.fixedSlotHilbertDirectLimitRegularSubspace)) atTop (nhds 0))
    (hgenerator : Tendsto
      (fun n => P.fixedSlotHilbertDirectLimitRegularRightGenerator (x n)) atTop (nhds eta)) :
    eta = 0 := by
  apply P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_dense.eq_zero_of_inner_left ℝ
  intro z hz
  let zD : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain := ⟨z, hz⟩
  have hzconst : Tendsto
      (fun _ : ℕ => (zD : P.fixedSlotHilbertDirectLimitRegularSubspace))
      atTop (nhds (zD : P.fixedSlotHilbertDirectLimitRegularSubspace)) :=
    tendsto_const_nhds
  have hAzconst : Tendsto
      (fun _ : ℕ => P.fixedSlotHilbertDirectLimitRegularRightGenerator zD)
      atTop (nhds (P.fixedSlotHilbertDirectLimitRegularRightGenerator zD)) :=
    tendsto_const_nhds
  have hleft : Tendsto
      (fun n => inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator (x n))
        (zD : P.fixedSlotHilbertDirectLimitRegularSubspace))
      atTop
      (nhds (inner ℝ eta (zD : P.fixedSlotHilbertDirectLimitRegularSubspace))) :=
    Filter.Tendsto.inner (𝕜 := ℝ) hgenerator hzconst
  have hright : Tendsto
      (fun n => inner ℝ
        (x n : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator zD))
      atTop (nhds 0) := by
    have h := Filter.Tendsto.inner (𝕜 := ℝ) hx hAzconst
    simpa using h
  have hfun :
      (fun n => inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator (x n))
        (zD : P.fixedSlotHilbertDirectLimitRegularSubspace)) =
      (fun n => inner ℝ
        (x n : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator zD)) := by
    funext n
    exact P.fixedSlotHilbertDirectLimitRegularRightGenerator_inner_symmetric (x n) zD
  rw [hfun] at hleft
  exact tendsto_nhds_unique hleft hright

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_sequentially_closable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : ℕ → P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain}
    {eta : P.fixedSlotHilbertDirectLimitRegularSubspace}
    (hx : Tendsto
      (fun n => (x n : P.fixedSlotHilbertDirectLimitRegularSubspace)) atTop (nhds 0))
    (hHamiltonian : Tendsto
      (fun n => P.fixedSlotHilbertDirectLimitRegularRightHamiltonian (x n)) atTop (nhds eta)) :
    eta = 0 := by
  have hgenerator : Tendsto
      (fun n => P.fixedSlotHilbertDirectLimitRegularRightGenerator (x n))
      atTop (nhds (-eta)) := by
    simpa [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply] using hHamiltonian.neg
  have hzero : -eta = 0 :=
    P.fixedSlotHilbertDirectLimitRegularRightGenerator_sequentially_closable hx hgenerator
  exact neg_eq_zero.mp hzero

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_dense_symmetric_nonnegative
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Dense (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :
      Set P.fixedSlotHilbertDirectLimitRegularSubspace) ∧
    (∀ x y : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain,
      inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
          (y : P.fixedSlotHilbertDirectLimitRegularSubspace) =
        inner ℝ (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
          (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian y)) ∧
    (∀ x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain,
      0 ≤ inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_dense,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_symmetric,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_nonneg⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
