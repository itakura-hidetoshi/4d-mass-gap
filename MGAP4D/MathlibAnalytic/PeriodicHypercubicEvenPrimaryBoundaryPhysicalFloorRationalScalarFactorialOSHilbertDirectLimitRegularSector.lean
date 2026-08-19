import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRationalSemigroup
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

/-!
# Canonical zero-time regular sector of the factorial OS rational semigroup

The canonical same-root factorial OS construction now supplies a contraction semigroup at every
nonnegative rational time on the completed direct-limit Hilbert carrier. Rational semigroup laws
and contractivity alone do not imply strong continuity at time zero, so we isolate without adding a
continuity hypothesis the maximal vector sector on which the already-constructed rational semigroup
is genuinely regular at zero.

We use Mathlib's nonnegative rationals `NNRat` as the proof-free topological time parameter, prove
that the regular vectors form a real submodule, prove invariance under every rational-time
contraction, and derive a quantitative orbit estimate and uniform continuity. These are precisely
the inputs for the subsequent dense extension to nonnegative real time.

No stochastic-continuity assumption, real-time operator, generator, Hamiltonian, spectral theorem,
or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
open UniformSpace

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

/-- Completed direct-limit rational contraction, reparameterized by nonnegative rationals. -/
noncomputable def fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNRat) :
    P.fixedSlotHilbertDirectLimitCompletion →L[ℝ]
      P.fixedSlotHilbertDirectLimitCompletion :=
  P.fixedSlotHilbertDirectLimitTimeTranslateCLM (t : ℚ) t.2

@[simp]
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM 0 =
      ContinuousLinearMap.id ℝ P.fixedSlotHilbertDirectLimitCompletion := by
  simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM] using
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM_zero

/-- Additive semigroup law in the proof-free `NNRat` parameter. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNRat) :
    (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s).comp
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t) =
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t + s) := by
  simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM] using
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM_add
      (t : ℚ) (s : ℚ) t.2 s.2

/-- Pointwise form of the additive rational semigroup law. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNRat)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x) =
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t + s) x := by
  have h := congrArg
    (fun A : P.fixedSlotHilbertDirectLimitCompletion →L[ℝ]
        P.fixedSlotHilbertDirectLimitCompletion => A x)
    (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_add s t)
  exact h

/-- Every `NNRat` time operator remains a contraction. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNRat)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x‖ ≤ ‖x‖ := by
  exact P.fixedSlotHilbertDirectLimitTimeTranslate_norm_le (t : ℚ) t.2 x

/-- Canonical zero-time regular sector of the rational contraction semigroup. -/
noncomputable def fixedSlotHilbertDirectLimitRegularSubspace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Submodule ℝ P.fixedSlotHilbertDirectLimitCompletion where
  carrier := {x |
    Tendsto
      (fun t : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x)
      (𝓝 0) (𝓝 x)}
  zero_mem' := by
    have hconst : Tendsto
        (fun _ : NNRat => (0 : P.fixedSlotHilbertDirectLimitCompletion))
        (𝓝 0) (𝓝 0) := tendsto_const_nhds
    simpa using hconst
  add_mem' := by
    intro x y hx hy
    change Tendsto
      (fun t : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x)
      (𝓝 0) (𝓝 x) at hx
    change Tendsto
      (fun t : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t y)
      (𝓝 0) (𝓝 y) at hy
    change Tendsto
      (fun t : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t (x + y))
      (𝓝 0) (𝓝 (x + y))
    simpa only [map_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    change Tendsto
      (fun t : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x)
      (𝓝 0) (𝓝 x) at hx
    change Tendsto
      (fun t : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t (c • x))
      (𝓝 0) (𝓝 (c • x))
    simpa only [map_smul] using hx.const_smul c

/-- Membership is exactly zero-time strong continuity of the rational orbit. -/
theorem mem_fixedSlotHilbertDirectLimitRegularSubspace_iff
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    x ∈ P.fixedSlotHilbertDirectLimitRegularSubspace ↔
      Tendsto
        (fun t : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x)
        (𝓝 0) (𝓝 x) :=
  Iff.rfl

/-- Rational time translation preserves the canonical regular sector. -/
theorem fixedSlotHilbertDirectLimitRegularSubspace_invariant
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (x : P.fixedSlotHilbertDirectLimitCompletion) ∈
      P.fixedSlotHilbertDirectLimitRegularSubspace := by
  change Tendsto
    (fun t : NNRat =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          (x : P.fixedSlotHilbertDirectLimitCompletion)))
    (𝓝 0)
    (𝓝 (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
      (x : P.fixedSlotHilbertDirectLimitCompletion)))
  have hx := x.2
  change Tendsto
    (fun t : NNRat =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
        (x : P.fixedSlotHilbertDirectLimitCompletion))
    (𝓝 0) (𝓝 (x : P.fixedSlotHilbertDirectLimitCompletion)) at hx
  have hcomp :=
    (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s).continuous.continuousAt.tendsto.comp hx
  change Tendsto
    (fun t : NNRat =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (x : P.fixedSlotHilbertDirectLimitCompletion)))
    (𝓝 0)
    (𝓝 (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
      (x : P.fixedSlotHilbertDirectLimitCompletion))) at hcomp
  have hcomm :
      (fun t : NNRat =>
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (x : P.fixedSlotHilbertDirectLimitCompletion))) =
        (fun t : NNRat =>
          P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
              (x : P.fixedSlotHilbertDirectLimitCompletion))) := by
    funext t
    calc
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (x : P.fixedSlotHilbertDirectLimitCompletion)) =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + t)
          (x : P.fixedSlotHilbertDirectLimitCompletion) :=
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add t s
          (x : P.fixedSlotHilbertDirectLimitCompletion)
      _ = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t + s)
          (x : P.fixedSlotHilbertDirectLimitCompletion) := by rw [add_comm]
      _ = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
            (x : P.fixedSlotHilbertDirectLimitCompletion)) :=
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add s t
          (x : P.fixedSlotHilbertDirectLimitCompletion)).symm
  rw [hcomm]
  exact hcomp

/-- The defect between two ordered orbit times is bounded by the corresponding zero-time defect. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_sub_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNRat)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t + s) x -
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x‖ ≤
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x - x‖ := by
  rw [← P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add s t x]
  rw [← map_sub]
  exact P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le s _

/-- A regular vector has a right-continuous rational orbit at every nonnegative rational time. -/
theorem fixedSlotHilbertDirectLimitRegularSubspace_tendsto_add_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun t : NNRat =>
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t + s)
          (x : P.fixedSlotHilbertDirectLimitCompletion))
      (𝓝 0)
      (𝓝 (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (x : P.fixedSlotHilbertDirectLimitCompletion))) := by
  have hx := x.2
  change Tendsto
    (fun t : NNRat =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
        (x : P.fixedSlotHilbertDirectLimitCompletion))
    (𝓝 0) (𝓝 (x : P.fixedSlotHilbertDirectLimitCompletion)) at hx
  have hs :=
    (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s).continuous.continuousAt.tendsto.comp hx
  change Tendsto
    (fun t : NNRat =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (x : P.fixedSlotHilbertDirectLimitCompletion)))
    (𝓝 0)
    (𝓝 (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
      (x : P.fixedSlotHilbertDirectLimitCompletion))) at hs
  have hfun :
      (fun t : NNRat =>
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t + s)
          (x : P.fixedSlotHilbertDirectLimitCompletion)) =
        (fun t : NNRat =>
          P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
              (x : P.fixedSlotHilbertDirectLimitCompletion))) := by
    funext t
    exact
      (P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add s t
        (x : P.fixedSlotHilbertDirectLimitCompletion)).symm
  rw [hfun]
  exact hs

/-- A regular rational orbit is uniformly continuous. This is the quantitative input for canonical
extension to nonnegative real time. -/
theorem fixedSlotHilbertDirectLimitRegularSubspace_uniformContinuous_orbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    UniformContinuous
      (fun t : NNRat =>
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (x : P.fixedSlotHilbertDirectLimitCompletion)) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hx0 := x.2
  change Tendsto
    (fun t : NNRat =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
        (x : P.fixedSlotHilbertDirectLimitCompletion))
    (𝓝 0) (𝓝 (x : P.fixedSlotHilbertDirectLimitCompletion)) at hx0
  rw [Metric.tendsto_nhds_nhds] at hx0
  obtain ⟨δ, hδ, hclose⟩ := hx0 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a b hab
  rcases le_total a b with hab_le | hba_le
  · let d : NNRat := b - a
    have hba : a + d = b := by
      dsimp [d]
      exact add_tsub_cancel_of_le hab_le
    have hdδ : dist d 0 < δ := by
      have hdist : dist d 0 = dist b a := by
        rw [NNRat.dist_eq, NNRat.dist_eq]
        change dist ((b - a : NNRat) : ℚ) 0 = dist (b : ℚ) (a : ℚ)
        rw [NNRat.coe_sub hab_le]
        simp only [dist_eq_norm, sub_zero]
      rw [hdist, dist_comm]
      exact hab
    have hzero := hclose (x_1 := d) hdδ
    rw [dist_eq_norm] at hzero ⊢
    rw [← hba]
    exact lt_of_le_of_lt
      (P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_sub_norm_le a d
        (x : P.fixedSlotHilbertDirectLimitCompletion)) hzero
  · let d : NNRat := a - b
    have hab' : b + d = a := by
      dsimp [d]
      exact add_tsub_cancel_of_le hba_le
    have hdδ : dist d 0 < δ := by
      have hdist : dist d 0 = dist a b := by
        rw [NNRat.dist_eq, NNRat.dist_eq]
        change dist ((a - b : NNRat) : ℚ) 0 = dist (a : ℚ) (b : ℚ)
        rw [NNRat.coe_sub hba_le]
        simp only [dist_eq_norm, sub_zero]
      rw [hdist]
      exact hab
    have hzero := hclose (x_1 := d) hdδ
    rw [dist_eq_norm] at hzero ⊢
    rw [← hab']
    rw [norm_sub_rev]
    exact lt_of_le_of_lt
      (P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_sub_norm_le b d
        (x : P.fixedSlotHilbertDirectLimitCompletion)) hzero

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
