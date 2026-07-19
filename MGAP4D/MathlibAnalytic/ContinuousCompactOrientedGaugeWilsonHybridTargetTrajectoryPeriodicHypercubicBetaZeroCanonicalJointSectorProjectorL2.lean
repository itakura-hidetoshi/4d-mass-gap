import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFluctuationJointSectorEigenvalueL2
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The coordinate factor used by the canonical joint-sector projector.  The
factor is `Q i` on a selected coordinate and `I - Q i` on an unselected
coordinate. -/
def continuousLinearMapJointSectorFactorL2
    {ι : Type*}
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (i : ι) :
    V →L[ℝ] V :=
  if i ∈ s then Q i else 1 - Q i

@[simp]
theorem continuousLinearMapJointSectorFactorL2_eq_of_mem
    {ι : Type*}
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    {i : ι}
    (hi : i ∈ s) :
    continuousLinearMapJointSectorFactorL2 Q s i = Q i := by
  simp [continuousLinearMapJointSectorFactorL2, hi]

@[simp]
theorem continuousLinearMapJointSectorFactorL2_eq_of_not_mem
    {ι : Type*}
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    {i : ι}
    (hi : i ∉ s) :
    continuousLinearMapJointSectorFactorL2 Q s i = 1 - Q i := by
  simp [continuousLinearMapJointSectorFactorL2, hi]

/-- Pairwise commuting coordinates give pairwise commuting selected/complement
factors. -/
theorem continuousLinearMapJointSectorFactorL2_pairwise_comm
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    (Finset.univ : Set ι).Pairwise
      (Commute on continuousLinearMapJointSectorFactorL2 Q s) := by
  classical
  intro i hi j hj hij
  dsimp only [Function.onFun]
  apply ContinuousLinearMap.ext
  intro f
  change
    continuousLinearMapJointSectorFactorL2 Q s i
        (continuousLinearMapJointSectorFactorL2 Q s j f) =
      continuousLinearMapJointSectorFactorL2 Q s j
        (continuousLinearMapJointSectorFactorL2 Q s i f)
  by_cases his : i ∈ s
  · by_cases hjs : j ∈ s
    · simpa [continuousLinearMapJointSectorFactorL2, his, hjs] using
        hComm i j f
    · simp [continuousLinearMapJointSectorFactorL2, his, hjs,
        hComm i j f]
  · by_cases hjs : j ∈ s
    · simp [continuousLinearMapJointSectorFactorL2, his, hjs,
        hComm i j f]
    · simp [continuousLinearMapJointSectorFactorL2, his, hjs,
        hComm i j f]
      abel

/-- The canonical joint-sector projector is the order-independent
noncommutative product

`∏ i, if i ∈ s then Q i else I - Q i`.

The `Finset.noncommProd` construction records the supplied pairwise
commutativity and therefore does not choose an arbitrary enumeration. -/
noncomputable def continuousLinearMapJointSectorProjectorL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    V →L[ℝ] V :=
  Finset.univ.noncommProd
    (continuousLinearMapJointSectorFactorL2 Q s)
    (continuousLinearMapJointSectorFactorL2_pairwise_comm Q s hComm)

/-- A selected idempotent coordinate absorbs its canonical joint-sector
projector on the left. -/
theorem continuousLinearMap_mul_jointSectorProjectorL2_eq_self_of_mem
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {i : ι}
    (hi : i ∈ s) :
    Q i * continuousLinearMapJointSectorProjectorL2 Q s hComm =
      continuousLinearMapJointSectorProjectorL2 Q s hComm := by
  classical
  let factor : ι → V →L[ℝ] V :=
    continuousLinearMapJointSectorFactorL2 Q s
  have hFactorComm :
      (Finset.univ : Set ι).Pairwise (Commute on factor) := by
    exact continuousLinearMapJointSectorFactorL2_pairwise_comm Q s hComm
  have hExtract :=
    Finset.mul_noncommProd_erase
      (Finset.univ : Finset ι)
      (Finset.mem_univ i)
      factor
      hFactorComm
  have hQFactor : Q i * factor i = factor i := by
    have hFactorEq : factor i = Q i := by
      dsimp [factor]
      exact continuousLinearMapJointSectorFactorL2_eq_of_mem Q s hi
    rw [hFactorEq]
    apply ContinuousLinearMap.ext
    intro f
    change Q i (Q i f) = Q i f
    exact hIdempotent i f
  change
    Q i * Finset.univ.noncommProd factor hFactorComm =
      Finset.univ.noncommProd factor hFactorComm
  rw [← hExtract, ← mul_assoc, hQFactor]

/-- An unselected idempotent coordinate kills its canonical joint-sector
projector on the left. -/
theorem continuousLinearMap_mul_jointSectorProjectorL2_eq_zero_of_not_mem
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {i : ι}
    (hi : i ∉ s) :
    Q i * continuousLinearMapJointSectorProjectorL2 Q s hComm = 0 := by
  classical
  let factor : ι → V →L[ℝ] V :=
    continuousLinearMapJointSectorFactorL2 Q s
  have hFactorComm :
      (Finset.univ : Set ι).Pairwise (Commute on factor) := by
    exact continuousLinearMapJointSectorFactorL2_pairwise_comm Q s hComm
  have hExtract :=
    Finset.mul_noncommProd_erase
      (Finset.univ : Finset ι)
      (Finset.mem_univ i)
      factor
      hFactorComm
  have hQFactor : Q i * factor i = 0 := by
    have hFactorEq : factor i = 1 - Q i := by
      dsimp [factor]
      exact continuousLinearMapJointSectorFactorL2_eq_of_not_mem Q s hi
    rw [hFactorEq]
    apply ContinuousLinearMap.ext
    intro f
    change Q i (f - Q i f) = 0
    rw [map_sub, hIdempotent]
    exact sub_self _
  change
    Q i * Finset.univ.noncommProd factor hFactorComm = 0
  rw [← hExtract, ← mul_assoc, hQFactor, zero_mul]

/-- Pointwise selected-coordinate law for the canonical joint-sector
projector. -/
theorem continuousLinearMap_jointSectorProjectorL2_apply_fixed_of_mem
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {i : ι}
    (hi : i ∈ s)
    (f : V) :
    Q i (continuousLinearMapJointSectorProjectorL2 Q s hComm f) =
      continuousLinearMapJointSectorProjectorL2 Q s hComm f := by
  have hOperator :=
    continuousLinearMap_mul_jointSectorProjectorL2_eq_self_of_mem
      Q s hIdempotent hComm hi
  have hApply := congrArg (fun T : V →L[ℝ] V => T f) hOperator
  change
    Q i (continuousLinearMapJointSectorProjectorL2 Q s hComm f) =
      continuousLinearMapJointSectorProjectorL2 Q s hComm f at hApply
  exact hApply

/-- Pointwise unselected-coordinate law for the canonical joint-sector
projector. -/
theorem continuousLinearMap_jointSectorProjectorL2_apply_zero_of_not_mem
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {i : ι}
    (hi : i ∉ s)
    (f : V) :
    Q i (continuousLinearMapJointSectorProjectorL2 Q s hComm f) = 0 := by
  have hOperator :=
    continuousLinearMap_mul_jointSectorProjectorL2_eq_zero_of_not_mem
      Q s hIdempotent hComm hi
  have hApply := congrArg (fun T : V →L[ℝ] V => T f) hOperator
  change
    Q i (continuousLinearMapJointSectorProjectorL2 Q s hComm f) = 0 at hApply
  exact hApply

/-- The range of the canonical projector lies in the joint-sector submodule
selected by the same subset. -/
theorem continuousLinearMap_jointSectorProjectorL2_apply_mem_jointSectorSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (f : V) :
    continuousLinearMapJointSectorProjectorL2 Q s hComm f ∈
      continuousLinearMapJointSectorSubmoduleL2 Q s := by
  rw [continuousLinearMapJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro i hi
    exact
      continuousLinearMap_jointSectorProjectorL2_apply_fixed_of_mem
        Q s hIdempotent hComm hi f
  · intro i hi
    exact
      continuousLinearMap_jointSectorProjectorL2_apply_zero_of_not_mem
        Q s hIdempotent hComm hi f

/-- The canonical joint-sector projector for the actual 324-link beta-zero
fluctuation family. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  continuousLinearMapJointSectorProjectorL2
    (fun edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          edge)
    s
    (fun target source f =>
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
        target source f)

/-- Every vector produced by the actual canonical projector belongs to its
specified fluctuation joint sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSectorProjectorL2_apply_mem_jointSector
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
        s f ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        s := by
  classical
  have hGeneric :=
    continuousLinearMap_jointSectorProjectorL2_apply_mem_jointSectorSubmoduleL2
      (Q := fun edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            edge)
      s
      (fun edge g =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
          edge g)
      (fun target source g =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source g)
      f
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2,
    ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
    using hGeneric

/-- The actual beta-zero Hamiltonian acts on every canonical projected vector
with the sector weight `card s`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_jointSectorProjector_eq_card_smul
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
          s f) =
      (s.card : ℝ) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
          s f := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_eq_card_smul_of_mem_fluctuationJointSector
      s
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSectorProjectorL2_apply_mem_jointSector
        s f)

/-- A nonzero canonical projected vector realizes the corresponding sector
weight as an actual heat-bath point-spectrum value. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_card_mem_heatBathPointSpectrumL2_of_jointSectorProjector_apply_ne_zero
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hNonzero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
        s f ≠ 0) :
    (s.card : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_card_mem_heatBathPointSpectrumL2_of_nonzero_mem_fluctuationJointSector
      s
      hNonzero
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSectorProjectorL2_apply_mem_jointSector
        s f)

/-- Compact receipt for the canonical actual beta-zero joint-sector projector
and its Hamiltonian eigenvalue law. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCanonicalJointSectorProjectorL2Receipt :
    Prop :=
  ∀ (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
        s f ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        s ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
          s f) =
      (s.card : ℝ) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
          s f

/-- The actual canonical beta-zero joint-sector projector receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCanonicalJointSectorProjectorL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCanonicalJointSectorProjectorL2Receipt := by
  intro s f
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSectorProjectorL2_apply_mem_jointSector
      s f,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_jointSectorProjector_eq_card_smul
      s f⟩

end

end MathlibAnalytic
end MGAP4D
