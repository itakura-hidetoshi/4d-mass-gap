import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicPositiveClosureTimeOneNonzeroV5_PZ37ANC
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AND — nonzero real L2 state of the true periodic positive closure

Use precisely the original full-periodic Wilson Gibbs positive-closure
pushforward, not ANA's separately normalized temporal-gauge half-path law.
ANC's unchanged time-one cylinder is measurable and nonzero a.e. for suitable
physical top-orthogonal two-mode coefficients. Its inherited pointwise bound
and the true marginal's probability property give MemLp 2. The exact same
function then represents a genuinely nonzero real L2 class.

No OS reflection-positive quotient identification, one-slab intertwining,
volume-uniform norm lower bound, or continuum Yang-Mills gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AND_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37AND_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AND_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AND_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AND_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AND_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- An explicit name for the unchanged original normalized full-periodic
Gibbs positive-closure pushforward used in ANB and ANC. -/
noncomputable def p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure (PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
  Measure.map
    (fun A : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
        (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta).gibbsMeasure

/-- The true periodic marginal has mass one, directly from the measurable
restriction map and the original normalized Gibbs probability. -/
theorem p4Q2PZ37AND_originalPeriodicPositiveClosure_isProbabilityMeasure
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta) := by
  have hBoundary : Measurable
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin 2) ℂ =>
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A) := by
    exact measurable_pi_lambda _ fun e => measurable_pi_apply e.1
  have hPositive : Measurable
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin 2) ℂ =>
        (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) := by
    exact measurable_pi_lambda _ fun e => measurable_pi_apply e.1
  letI : IsProbabilityMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta).gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta)
  unfold p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure
  exact Measure.isProbabilityMeasure_map (hBoundary.prodMk hPositive).aemeasurable

/-- The same pointwise two-mode bound holds after the actual closure
coordinate extraction. No comparison of interacting L2 norms is used. -/
theorem p4Q2PZ37AND_timeOnePositiveClosureObservable_norm_le
    (H : ℕ) (c0 c1 : ℝ)
    (z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 z‖ ≤
      |c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
      |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖ := by
  exact p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_norm_le H c0 c1
    ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H 2 z).1)

/-- Square-integrability of every such literal cylinder for the true
full-periodic Gibbs positive-closure marginal. -/
theorem p4Q2PZ37AND_truePeriodicTimeOnePositiveClosure_memLp
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    MemLp (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1)
      2 (p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta) := by
  letI : IsProbabilityMeasure
      (p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta) :=
    p4Q2PZ37AND_originalPeriodicPositiveClosure_isProbabilityMeasure H beta hbeta
  exact MemLp.of_bound
    (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable_measurable
      H c0 c1).aestronglyMeasurable
    (|c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
      |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖)
    (Filter.Eventually.of_forall
      (p4Q2PZ37AND_timeOnePositiveClosureObservable_norm_le H c0 c1))

/-- The actual real L2 class for the unchanged genuine periodic marginal. -/
noncomputable def p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    Lp ℝ 2 (p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta) :=
  (p4Q2PZ37AND_truePeriodicTimeOnePositiveClosure_memLp H beta hbeta c0 c1).toLp
    (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1)

/-- Its representative is the exact ANC time-one function, with the same
coefficients and coordinates, a.e. for the true periodic marginal. -/
theorem p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2_coeFn
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2 H beta hbeta c0 c1
      =ᵐ[p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta]
        p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 := by
  exact (p4Q2PZ37AND_truePeriodicTimeOnePositiveClosure_memLp
    H beta hbeta c0 c1).coeFn_toLp

/-- The original physical top-orthogonal two-mode coefficients furnish a
nonzero genuine-periodic positive-closure real L2 vector. Top-orthogonality
is asserted in the original physical one-slab Hilbert space only; it is not
silently transferred to an OS quotient or to the Gibbs L2 inner product. -/
theorem p4Q2PZ37AND_exists_nonzero_truePeriodicPositiveClosureTimeOneL2
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ c0 c1 : ℝ,
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta hbeta ∧
      ∃ ψ : Lp ℝ 2
          (p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta),
        ψ ≠ 0 ∧
        ψ =ᵐ[p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta]
          p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 := by
  obtain ⟨c0, c1, hTop, hNonzero⟩ :=
    p4Q2PZ37ANC_exists_nonzero_truePeriodicGibbsPositiveClosureTimeOneCylinder
      H beta hbeta
  let μ := p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta
  let F := p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1
  let ψ := p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2 H beta hbeta c0 c1
  have hFne : ¬ (F =ᵐ[μ] (fun _ => (0 : ℝ))) := hNonzero
  have hRep : ψ =ᵐ[μ] F :=
    p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2_coeFn H beta hbeta c0 c1
  have hψne : ψ ≠ 0 := by
    intro hzero
    have hψzero : ψ =ᵐ[μ] (fun _ => (0 : ℝ)) := by
      rw [hzero]
      simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 μ)
    exact hFne (hRep.symm.trans hψzero)
  exact ⟨c0, c1, hTop, ψ, hψne, hRep⟩

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AND_originalPeriodicPositiveClosure_isProbabilityMeasure
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AND_timeOnePositiveClosureObservable_norm_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AND_truePeriodicTimeOnePositiveClosure_memLp
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2_coeFn
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AND_exists_nonzero_truePeriodicPositiveClosureTimeOneL2
