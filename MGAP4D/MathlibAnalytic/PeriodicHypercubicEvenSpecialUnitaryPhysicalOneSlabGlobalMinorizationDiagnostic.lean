import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridge
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

/-- Canonical number of local Wilson-energy terms appearing in one symmetric
physical Euclidean-time slab: one copy of the spatial plaquettes, after the two
half-spatial actions are combined, plus one copy of the temporal crossing
links.

The definition deliberately uses the canonical lists already driving the raw
Wilson kernel, rather than duplicating a coordinate-count formula. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume
    (H : ℕ) : ℕ :=
  (periodicHypercubicEvenSpatialSlicePlaquetteList H).length +
    (periodicHypercubicEvenSpatialSliceLinkList H).length

/-- The corresponding crude global Wilson-action budget.  The factor `2` is
the sharp pointwise range bound for each conventional `SU(N)` Wilson
plaquette energy currently available in the raw model. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    (H : ℕ) : ℝ :=
  2 *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H : ℝ)

/-- Every spatial-slice Wilson action is bounded by twice the number of
canonical spatial plaquettes. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
    (H N : ℕ)
    (hN : 0 < N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A ≤
      2 * ((periodicHypercubicEvenSpatialSlicePlaquetteList H).length : ℝ) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  generalize periodicHypercubicEvenSpatialSlicePlaquetteList H = ps
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp :
          specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) ≤ 2 :=
        specialUnitaryWilsonPlaquetteEnergy_le_two hN _
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      nlinarith

/-- Every temporal crossing action is bounded by twice the number of canonical
spatial links crossing the slab. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_le_two_mul_length
    (H N : ℕ)
    (hN : 0 < N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B ≤
      2 * ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil => simp
  | cons e es ih =>
      have he :
          specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e) ≤ 2 :=
        specialUnitaryWilsonPlaquetteEnergy_le_two hN _
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      nlinarith

/-- The literal symmetric one-slab Wilson action has a configuration-independent
upper bound equal to the global action budget.

This is an actual-model estimate: no transfer-gap, top-sector simplicity,
thermodynamic-limit, or continuum-limit assumption enters. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
    (H N : ℕ)
    (hN : 0 < N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
  have hA :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H N hN A
  have hB :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H N hN B
  have hcross :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_le_two_mul_length
      H N hN A B
  have hhalfA :
      (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A ≤
        (1 / 2 : ℝ) *
          (2 * ((periodicHypercubicEvenSpatialSlicePlaquetteList H).length : ℝ)) :=
    mul_le_mul_of_nonneg_left hA (by norm_num)
  have hhalfB :
      (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N B ≤
        (1 / 2 : ℝ) *
          (2 * ((periodicHypercubicEvenSpatialSlicePlaquetteList H).length : ℝ)) :=
    mul_le_mul_of_nonneg_left hB (by norm_num)
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume
  have hsum := add_le_add (add_le_add hhalfA hcross) hhalfB
  push_cast
  nlinarith

/-- The crude global pointwise minorization floor extracted solely from the
uniform action budget. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
    (H : ℕ)
    (beta : ℝ) : ℝ :=
  Real.exp
    (-beta *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)

/-- The global floor is strictly positive for every fixed finite slab. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
    (H : ℕ)
    (beta : ℝ) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
  exact Real.exp_pos _

/-- At nonnegative coupling the crude floor is at most one. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_one
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤ 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hbudget :
      0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    positivity
  nlinarith

/-- Literal global minorization of the actual one-slab Wilson Boltzmann kernel.
Every pair of boundary configurations has kernel value at least the explicit
floor `exp (- beta * globalActionBudget H)`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
  apply Real.exp_le_exp.mpr
  have haction :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H N hN A B
  have hscaled := mul_le_mul_of_nonneg_left haction hbeta
  nlinarith

/-- If the extensive exponent `beta_n * globalActionBudget(H_n)` diverges to
`+∞`, then the certified global minorization floor converges to zero.

This diagnoses the *certificate*: it does not assert that the actual physical
transfer gap converges to zero. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_tendsto_zero
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ)
    (hExtensive :
      Tendsto
        (fun n =>
          beta n *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
              (halfExtent n))
        atTop atTop) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
          (halfExtent n) (beta n))
      atTop (𝓝 0) := by
  have hneg :
      Tendsto
        (fun n =>
          -(beta n *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
              (halfExtent n)))
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hExtensive
  have hexp := Real.tendsto_exp_atBot.comp hneg
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor,
    neg_mul] using hexp

/-- Under the same extensive scaling, the crude global-minorization certificate
cannot possess any positive scale-independent lower bound.

Again, this is deliberately a statement about this proof route only.  It is not
a no-gap theorem for the Wilson transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_no_positive_uniform_lower_bound
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ)
    (hExtensive :
      Tendsto
        (fun n =>
          beta n *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
              (halfExtent n))
        atTop atTop) :
    ¬ ∃ ε : ℝ, 0 < ε ∧
      ∀ n,
        ε ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
            (halfExtent n) (beta n) := by
  have hzero :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_tendsto_zero
      halfExtent beta hExtensive
  intro h
  rcases h with ⟨ε, hε, hall⟩
  have heventually :
      ∀ᶠ n in atTop,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
            (halfExtent n) (beta n) < ε :=
    (tendsto_order.1 hzero).2 ε hε
  rcases heventually.exists with ⟨n, hn⟩
  exact (not_lt_of_ge (hall n)) hn

/-- Audit-visible diagnostic package for a single finite slab.  It records both
the actual-model action upper bound and the resulting positive kernel floor,
without pretending that this coarse floor is the scale-uniform squared-defect
coercivity characterized by the preceding defect bridge. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  actionUpper :
    ∀ A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  kernelFloor :
    ∀ A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
          H beta ≤
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B
  floorPositive :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta
  floorLeOne :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta ≤ 1

/-- Construct the complete finite-slab global-minorization diagnostic. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
      H N hN beta hbeta where
  actionUpper :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H N hN
  kernelFloor :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
      H N hN beta hbeta
  floorPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H beta
  floorLeOne :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_one
      H beta hbeta

end

end MathlibAnalytic
end MGAP4D
