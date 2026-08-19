import MGAP4D.MathlibAnalytic.NNRatToNNRealUniformContinuousExtension
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularSector
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitSymmetricPositive
import Mathlib.Tactic

/-!
# Canonical nonnegative-real orbit of the factorial OS regular sector

For every vector in the canonical zero-time regular sector, the preceding package proves uniform
continuity of its nonnegative-rational orbit.  Since nonnegative rationals embed isometrically and
densely into `NNReal`, that orbit has a unique canonical uniformly continuous real-half-line
extension.

This file constructs the extension and proves rational agreement, zero-time recovery, contractivity,
linearity in the initial vector, and the real-time continuation of OS symmetry and positivity.
Nothing here assumes that every completed direct-limit vector is regular: the construction exposes
exactly the maximal sector currently justified by the same-root Wilson/OS data.

The remaining step for a genuine endomorphism-valued `C₀` semigroup is to prove that every real-time
value of a regular orbit remains in the regular sector and then close the real semigroup law.  That
step is deliberately not hidden in the definition below.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology Set

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

/-- Canonical real-half-line orbit of a zero-time regular vector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRealOrbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    NNReal → P.fixedSlotHilbertDirectLimitCompletion :=
  MGAP4D.nnratUniformlyExtend
    (fun q : NNRat =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
        (x : P.fixedSlotHilbertDirectLimitCompletion))

/-- The canonical real orbit is uniformly continuous. -/
theorem fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    UniformContinuous (P.fixedSlotHilbertDirectLimitRegularRealOrbit x) := by
  exact MGAP4D.nnratUniformlyExtend_uniformContinuous _
    (P.fixedSlotHilbertDirectLimitRegularSubspace_uniformContinuous_orbit x)

/-- The real orbit agrees exactly with the canonical rational semigroup at every rational time. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (q : NNRat) :
    P.fixedSlotHilbertDirectLimitRegularRealOrbit x (MGAP4D.nnratToNNReal q) =
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
        (x : P.fixedSlotHilbertDirectLimitCompletion) := by
  exact MGAP4D.nnratUniformlyExtend_nnratToNNReal _
    (P.fixedSlotHilbertDirectLimitRegularSubspace_uniformContinuous_orbit x) q

/-- Zero real time recovers the initial regular vector. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealOrbit_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealOrbit x 0 =
      (x : P.fixedSlotHilbertDirectLimitCompletion) := by
  rw [← MGAP4D.nnratToNNReal_zero]
  rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
  rw [P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_zero]
  rfl

/-- Contractivity persists at every nonnegative real time by density and closedness. -/
theorem fixedSlotHilbertDirectLimitRegularRealOrbit_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) :
    ‖P.fixedSlotHilbertDirectLimitRegularRealOrbit x t‖ ≤ ‖(x :
      P.fixedSlotHilbertDirectLimitCompletion)‖ := by
  let S : Set NNReal := {s |
    ‖P.fixedSlotHilbertDirectLimitRegularRealOrbit x s‖ ≤ ‖(x :
      P.fixedSlotHilbertDirectLimitCompletion)‖}
  have hclosed : IsClosed S := by
    exact isClosed_le continuous_const
      (continuous_norm.comp
        (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous)
  have hrange : Set.range MGAP4D.nnratToNNReal ⊆ S := by
    intro s hs
    rcases hs with ⟨q, rfl⟩
    change
      ‖P.fixedSlotHilbertDirectLimitRegularRealOrbit x (MGAP4D.nnratToNNReal q)‖ ≤ _
    rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
    exact P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le q x
  have hclosure : closure (Set.range MGAP4D.nnratToNNReal) ⊆ S :=
    closure_minimal hrange hclosed
  have ht : t ∈ closure (Set.range MGAP4D.nnratToNNReal) := by
    rw [MGAP4D.nnratToNNReal_denseRange.closure_eq]
    trivial
  exact hclosure ht

/-- Real orbit extension is additive in the initial regular vector. -/
theorem fixedSlotHilbertDirectLimitRegularRealOrbit_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRealOrbit (x + y) t =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x t +
        P.fixedSlotHilbertDirectLimitRegularRealOrbit y t := by
  let f : NNRat → P.fixedSlotHilbertDirectLimitCompletion := fun q =>
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
      ((x + y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
        P.fixedSlotHilbertDirectLimitCompletion)
  let g : NNReal → P.fixedSlotHilbertDirectLimitCompletion := fun s =>
    P.fixedSlotHilbertDirectLimitRegularRealOrbit x s +
      P.fixedSlotHilbertDirectLimitRegularRealOrbit y s
  have hg : ∀ q : NNRat, g (MGAP4D.nnratToNNReal q) = f q := by
    intro q
    dsimp [g, f]
    rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
    rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
    rw [map_add]
    rfl
  have hgc : Continuous g := by
    exact
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous.add
        (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous y).continuous
  have hEq := MGAP4D.nnratUniformlyExtend_unique f g hg hgc
  exact congrFun hEq t

/-- Real orbit extension is homogeneous in the initial regular vector. -/
theorem fixedSlotHilbertDirectLimitRegularRealOrbit_smul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (c : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRealOrbit (c • x) t =
      c • P.fixedSlotHilbertDirectLimitRegularRealOrbit x t := by
  let f : NNRat → P.fixedSlotHilbertDirectLimitCompletion := fun q =>
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
      ((c • x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
        P.fixedSlotHilbertDirectLimitCompletion)
  let g : NNReal → P.fixedSlotHilbertDirectLimitCompletion := fun s =>
    c • P.fixedSlotHilbertDirectLimitRegularRealOrbit x s
  have hg : ∀ q : NNRat, g (MGAP4D.nnratToNNReal q) = f q := by
    intro q
    dsimp [g, f]
    rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
    rw [map_smul]
    rfl
  have hgc : Continuous g :=
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous.const_smul c
  have hEq := MGAP4D.nnratUniformlyExtend_unique f g hg hgc
  exact congrFun hEq t

/-- At each real time the canonical extension is a real-linear map from the regular sector into the
ambient completed direct-limit Hilbert carrier. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRealTimeLinearMap
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →ₗ[ℝ]
      P.fixedSlotHilbertDirectLimitCompletion where
  toFun x := P.fixedSlotHilbertDirectLimitRegularRealOrbit x t
  map_add' x y := P.fixedSlotHilbertDirectLimitRegularRealOrbit_add x y t
  map_smul' c x := P.fixedSlotHilbertDirectLimitRegularRealOrbit_smul c x t

/-- The real-time linear map is a contraction and hence continuous. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRealTimeCLM
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitCompletion :=
  (P.fixedSlotHilbertDirectLimitRegularRealTimeLinearMap t).mkContinuous 1 (by
    intro x
    simpa using P.fixedSlotHilbertDirectLimitRegularRealOrbit_norm_le x t)

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealTimeCLM_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeCLM t x =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x t :=
  rfl

/-- The real-time extension retains the same-root OS symmetry on regular vectors. -/
theorem fixedSlotHilbertDirectLimitRegularRealTime_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealTimeCLM t x)
        (y : P.fixedSlotHilbertDirectLimitCompletion) =
      inner ℝ (x : P.fixedSlotHilbertDirectLimitCompletion)
        (P.fixedSlotHilbertDirectLimitRegularRealTimeCLM t y) := by
  let S : Set NNReal := {s |
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealTimeCLM s x)
        (y : P.fixedSlotHilbertDirectLimitCompletion) =
      inner ℝ (x : P.fixedSlotHilbertDirectLimitCompletion)
        (P.fixedSlotHilbertDirectLimitRegularRealTimeCLM s y)}
  have hclosed : IsClosed S := by
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hrange : Set.range MGAP4D.nnratToNNReal ⊆ S := by
    intro s hs
    rcases hs with ⟨q, rfl⟩
    change
      inner ℝ
          (P.fixedSlotHilbertDirectLimitRegularRealOrbit x (MGAP4D.nnratToNNReal q))
          (y : P.fixedSlotHilbertDirectLimitCompletion) =
        inner ℝ (x : P.fixedSlotHilbertDirectLimitCompletion)
          (P.fixedSlotHilbertDirectLimitRegularRealOrbit y (MGAP4D.nnratToNNReal q))
    rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
    rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
    exact P.fixedSlotHilbertDirectLimitTimeTranslate_inner_symmetric
      (q : ℚ) q.2 x y
  have hclosure : closure (Set.range MGAP4D.nnratToNNReal) ⊆ S :=
    closure_minimal hrange hclosed
  apply hclosure
  rw [MGAP4D.nnratToNNReal_denseRange.closure_eq]
  trivial

/-- The real-time extension remains positive semidefinite on every regular vector. -/
theorem fixedSlotHilbertDirectLimitRegularRealTime_inner_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    0 ≤ inner ℝ (x : P.fixedSlotHilbertDirectLimitCompletion)
      (P.fixedSlotHilbertDirectLimitRegularRealTimeCLM t x) := by
  let S : Set NNReal := {s |
    0 ≤ inner ℝ (x : P.fixedSlotHilbertDirectLimitCompletion)
      (P.fixedSlotHilbertDirectLimitRegularRealTimeCLM s x)}
  have hclosed : IsClosed S := by
    exact isClosed_le continuous_const (by fun_prop)
  have hrange : Set.range MGAP4D.nnratToNNReal ⊆ S := by
    intro s hs
    rcases hs with ⟨q, rfl⟩
    change 0 ≤ inner ℝ (x : P.fixedSlotHilbertDirectLimitCompletion)
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit x (MGAP4D.nnratToNNReal q))
    rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
    exact P.fixedSlotHilbertDirectLimitTimeTranslate_inner_nonneg (q : ℚ) q.2 x
  have hclosure : closure (Set.range MGAP4D.nnratToNNReal) ⊆ S :=
    closure_minimal hrange hclosed
  apply hclosure
  rw [MGAP4D.nnratToNNReal_denseRange.closure_eq]
  trivial

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
