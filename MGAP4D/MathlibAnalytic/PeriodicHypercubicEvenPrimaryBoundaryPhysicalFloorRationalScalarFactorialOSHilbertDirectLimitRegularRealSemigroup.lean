import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularRealOrbit
import Mathlib.Tactic

/-!
# Canonical real-time C₀ contraction semigroup on the factorial OS regular sector

The preceding same-root factorial OS construction provides a uniformly continuous `NNReal` orbit
for every vector in the canonical zero-time regular sector, but its values were intentionally left
in the ambient completed direct-limit Hilbert carrier.  This file closes exactly the remaining
semigroup step without adding any stochastic-continuity hypothesis.

The key observation is that every already-constructed rational-time contraction commutes with the
canonical real-time orbit extension.  The identity is true on dense nonnegative-rational times by
the rational semigroup law and passes to all nonnegative-real times by continuity.  It immediately
implies that each real-time orbit value is again regular at zero.  We can therefore corestrict the
real-time maps to the regular sector and close the full additive real semigroup law by the same
density argument.

The resulting endomorphism-valued family has

* identity at zero,
* the additive `NNReal` semigroup law,
* pointwise and operator-norm contractivity,
* strong continuity at zero on every regular vector,
* rational-time agreement,
* the inherited same-root OS symmetry and positivity.

No generator, Hamiltonian, self-adjointness theorem, spectral calculus, or mass-gap transfer is
introduced here.  Those belong only after this C₀-semigroup layer is canonical.
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

/-- A rational-time contraction commutes with the canonical real-time orbit extension.  The proof
uses only rational semigroup coherence, rational agreement of the extension, and density. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_regularRealOrbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (q : NNRat)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
        (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t) =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x
        (MGAP4D.nnratToNNReal q + t) := by
  let S : Set NNReal := {s |
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
        (P.fixedSlotHilbertDirectLimitRegularRealOrbit x s) =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x
        (MGAP4D.nnratToNNReal q + s)}
  have hleft : Continuous (fun s : NNReal =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
        (P.fixedSlotHilbertDirectLimitRegularRealOrbit x s)) :=
    (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q).continuous.comp
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous
  have hright : Continuous (fun s : NNReal =>
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x
        (MGAP4D.nnratToNNReal q + s)) :=
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous.comp
      (continuous_const.add continuous_id)
  have hclosed : IsClosed S := by
    exact isClosed_eq hleft hright
  have hrange : Set.range MGAP4D.nnratToNNReal ⊆ S := by
    intro s hs
    rcases hs with ⟨r, rfl⟩
    change
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
          (P.fixedSlotHilbertDirectLimitRegularRealOrbit x
            (MGAP4D.nnratToNNReal r)) =
        P.fixedSlotHilbertDirectLimitRegularRealOrbit x
          (MGAP4D.nnratToNNReal q + MGAP4D.nnratToNNReal r)
    calc
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
          (P.fixedSlotHilbertDirectLimitRegularRealOrbit x
            (MGAP4D.nnratToNNReal r)) =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM r
            (x : P.fixedSlotHilbertDirectLimitCompletion)) := by
          rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
      _ = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (r + q)
          (x : P.fixedSlotHilbertDirectLimitCompletion) :=
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add q r
          (x : P.fixedSlotHilbertDirectLimitCompletion)
      _ = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (q + r)
          (x : P.fixedSlotHilbertDirectLimitCompletion) := by rw [add_comm]
      _ = P.fixedSlotHilbertDirectLimitRegularRealOrbit x
          (MGAP4D.nnratToNNReal (q + r)) :=
        (P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat x (q + r)).symm
      _ = P.fixedSlotHilbertDirectLimitRegularRealOrbit x
          (MGAP4D.nnratToNNReal q + MGAP4D.nnratToNNReal r) := by
        rw [MGAP4D.nnratToNNReal_add]
  have hclosure : closure (Set.range MGAP4D.nnratToNNReal) ⊆ S :=
    closure_minimal hrange hclosed
  apply hclosure
  rw [MGAP4D.nnratToNNReal_denseRange.closure_eq]
  trivial

/-- Every real-time value of a regular orbit is again a zero-time regular vector.  Thus the
canonical real extension is genuinely invariant on the maximal regular sector. -/
theorem fixedSlotHilbertDirectLimitRegularRealOrbit_mem_regularSubspace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRealOrbit x t ∈
      P.fixedSlotHilbertDirectLimitRegularSubspace := by
  change Tendsto
    (fun q : NNRat =>
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
        (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t))
    (𝓝 0)
    (𝓝 (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t))
  have hzeroAt : ContinuousAt MGAP4D.nnratToNNReal (0 : NNRat) :=
    MGAP4D.nnratToNNReal_isometry.continuous.continuousAt
  have hzeroRaw : Tendsto MGAP4D.nnratToNNReal
      (𝓝 (0 : NNRat))
      (𝓝 (MGAP4D.nnratToNNReal (0 : NNRat))) :=
    hzeroAt.tendsto
  have hzero : Tendsto MGAP4D.nnratToNNReal
      (𝓝 (0 : NNRat)) (𝓝 (0 : NNReal)) := by
    simpa using hzeroRaw
  have hconst : Tendsto (fun _ : NNRat => t)
      (𝓝 (0 : NNRat)) (𝓝 t) := tendsto_const_nhds
  have htime : Tendsto (fun q : NNRat => MGAP4D.nnratToNNReal q + t)
      (𝓝 (0 : NNRat)) (𝓝 t) := by
    simpa using hzero.add hconst
  have horbit :=
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous.continuousAt.tendsto.comp
      htime
  change Tendsto
    (fun q : NNRat =>
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x
        (MGAP4D.nnratToNNReal q + t))
    (𝓝 0)
    (𝓝 (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t)) at horbit
  have hfun :
      (fun q : NNRat =>
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
          (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t)) =
      (fun q : NNRat =>
        P.fixedSlotHilbertDirectLimitRegularRealOrbit x
          (MGAP4D.nnratToNNReal q + t)) := by
    funext q
    exact P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_regularRealOrbit q x t
  rw [hfun]
  exact horbit

/-- The canonical real-time orbit, now regarded as a vector of the regular sector itself. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRealTimeVector
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ⟨P.fixedSlotHilbertDirectLimitRegularRealOrbit x t,
    P.fixedSlotHilbertDirectLimitRegularRealOrbit_mem_regularSubspace x t⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealTimeVector_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ((P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) :
      P.fixedSlotHilbertDirectLimitCompletion) =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x t :=
  rfl

/-- Real-time semigroup law on regular vectors.  Once invariance is known, equality on dense
rational outer times extends to every nonnegative real outer time. -/
theorem fixedSlotHilbertDirectLimitRegularRealOrbit_semigroup
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealOrbit
        (P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x) s =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x (t + s) := by
  let S : Set NNReal := {u |
    P.fixedSlotHilbertDirectLimitRegularRealOrbit
        (P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x) u =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x (t + u)}
  have hleft : Continuous (fun u : NNReal =>
      P.fixedSlotHilbertDirectLimitRegularRealOrbit
        (P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x) u) :=
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous
      (P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x)).continuous
  have hright : Continuous (fun u : NNReal =>
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x (t + u)) :=
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous.comp
      (continuous_const.add continuous_id)
  have hclosed : IsClosed S := by
    exact isClosed_eq hleft hright
  have hrange : Set.range MGAP4D.nnratToNNReal ⊆ S := by
    intro u hu
    rcases hu with ⟨q, rfl⟩
    calc
      P.fixedSlotHilbertDirectLimitRegularRealOrbit
          (P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x)
          (MGAP4D.nnratToNNReal q) =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
          ((P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x :
            P.fixedSlotHilbertDirectLimitRegularSubspace) :
            P.fixedSlotHilbertDirectLimitCompletion) :=
        P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat
          (P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x) q
      _ = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
          (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t) := by
        rw [P.fixedSlotHilbertDirectLimitRegularRealTimeVector_coe]
      _ = P.fixedSlotHilbertDirectLimitRegularRealOrbit x
          (MGAP4D.nnratToNNReal q + t) :=
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_regularRealOrbit q x t
      _ = P.fixedSlotHilbertDirectLimitRegularRealOrbit x
          (t + MGAP4D.nnratToNNReal q) := by rw [add_comm]
  have hclosure : closure (Set.range MGAP4D.nnratToNNReal) ⊆ S :=
    closure_minimal hrange hclosed
  apply hclosure
  rw [MGAP4D.nnratToNNReal_denseRange.closure_eq]
  trivial

/-- Real-linear endomorphism of the regular sector at a fixed nonnegative real time. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRealTimeEndomorphismLinearMap
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →ₗ[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace where
  toFun x := P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x
  map_add' x y := by
    apply Subtype.ext
    exact P.fixedSlotHilbertDirectLimitRegularRealOrbit_add x y t
  map_smul' c x := by
    apply Subtype.ext
    exact P.fixedSlotHilbertDirectLimitRegularRealOrbit_smul c x t

/-- Continuous linear endomorphism of the regular sector.  The construction keeps the inherited
Hilbert norm and the same contraction constant one. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphismLinearMap t).mkContinuous 1 (by
    intro x
    change ‖P.fixedSlotHilbertDirectLimitRegularRealOrbit x t‖ ≤
      1 * ‖(x : P.fixedSlotHilbertDirectLimitCompletion)‖
    simpa only [one_mul] using
      P.fixedSlotHilbertDirectLimitRegularRealOrbit_norm_le x t)

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x =
      P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x :=
  rfl

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_coe_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ((P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) :
      P.fixedSlotHilbertDirectLimitCompletion) =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x t :=
  rfl

/-- Rational-time agreement of the endomorphism-valued real semigroup. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_nnrat
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (q : NNRat)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ((P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism
        (MGAP4D.nnratToNNReal q) x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) :
      P.fixedSlotHilbertDirectLimitCompletion) =
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
        (x : P.fixedSlotHilbertDirectLimitCompletion) := by
  change P.fixedSlotHilbertDirectLimitRegularRealOrbit x
      (MGAP4D.nnratToNNReal q) =
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
      (x : P.fixedSlotHilbertDirectLimitCompletion)
  exact P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat x q

/-- Pointwise contractivity of every real-time regular-sector endomorphism. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x‖ ≤ ‖x‖ := by
  change ‖P.fixedSlotHilbertDirectLimitRegularRealOrbit x t‖ ≤
    ‖(x : P.fixedSlotHilbertDirectLimitCompletion)‖
  exact P.fixedSlotHilbertDirectLimitRegularRealOrbit_norm_le x t

/-- Operator norm of the real-time regular-sector endomorphism is at most one. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_opNorm_le_one
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal) :
    ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t‖ ≤ 1 := by
  exact
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t).opNorm_le_bound
      zero_le_one (fun x => by
        simpa only [one_mul] using
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le t x)

/-- Zero real time is the identity endomorphism. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_zero_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism 0 x = x := by
  apply Subtype.ext
  change P.fixedSlotHilbertDirectLimitRegularRealOrbit x 0 =
    (x : P.fixedSlotHilbertDirectLimitCompletion)
  exact P.fixedSlotHilbertDirectLimitRegularRealOrbit_zero x

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism 0 =
      ContinuousLinearMap.id ℝ P.fixedSlotHilbertDirectLimitRegularSubspace := by
  apply ContinuousLinearMap.ext
  intro x
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_zero_apply x

/-- Pointwise additive real semigroup law, in the conventional `T_s (T_t x) = T_{s+t} x` form. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (s + t) x := by
  apply Subtype.ext
  change
    P.fixedSlotHilbertDirectLimitRegularRealOrbit
        (P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x) s =
      P.fixedSlotHilbertDirectLimitRegularRealOrbit x (s + t)
  simpa only [add_comm] using
    P.fixedSlotHilbertDirectLimitRegularRealOrbit_semigroup s t x

/-- Endomorphism-valued additive semigroup law. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNReal) :
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s).comp
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (s + t) := by
  apply ContinuousLinearMap.ext
  intro x
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply s t x

/-- Strong continuity at zero on every vector of the canonical regular Hilbert sector. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun t : NNReal => P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x)
      (𝓝 0) (𝓝 x) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  have hx : Tendsto
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit x)
      (𝓝 (0 : NNReal))
      (𝓝 (P.fixedSlotHilbertDirectLimitRegularRealOrbit x 0)) :=
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous.continuousAt
  rw [Metric.tendsto_nhds_nhds] at hx
  obtain ⟨δ, hδ, hclose⟩ := hx ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have h := hclose ht
  change dist (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t)
      (x : P.fixedSlotHilbertDirectLimitCompletion) < ε
  simpa using h

/-- Same-root OS symmetry, now stated for the genuine real-time regular-sector endomorphisms. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) y =
      inner ℝ x
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t y) := by
  change
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t)
        (y : P.fixedSlotHilbertDirectLimitCompletion) =
      inner ℝ (x : P.fixedSlotHilbertDirectLimitCompletion)
        (P.fixedSlotHilbertDirectLimitRegularRealOrbit y t)
  exact P.fixedSlotHilbertDirectLimitRegularRealTime_inner_symmetric t x y

/-- Same-root OS positivity, now stated for the genuine real-time regular-sector endomorphisms. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    0 ≤ inner ℝ x
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) := by
  change 0 ≤ inner ℝ (x : P.fixedSlotHilbertDirectLimitCompletion)
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t)
  exact P.fixedSlotHilbertDirectLimitRegularRealTime_inner_nonneg t x

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
