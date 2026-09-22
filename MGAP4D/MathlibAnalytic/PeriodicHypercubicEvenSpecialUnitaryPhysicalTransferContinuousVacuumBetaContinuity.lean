import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNonnegativeTopBetaContinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

/-!
# Coupling continuity of the existing continuous physical Wilson vacuum

Continuous kernel sections are mapped into the fixed Haar L2 space and paired
with the existing nonnegative physical vacuum. The resulting continuous scalar
is identified with the existing continuous top synthesis. Division by the
positive continuous top norm gives the original continuous vacuum representative.

This avoids evaluating an L2 equivalence class at a point and avoids comparing
feature spaces whose construction depends on the coupling. On the compact
boundary, the resulting continuous-map topology is the uniform/sup-norm topology.

All conclusions are at fixed finite volume and N > 0 on beta >= 0, including
beta = 0. No uniform-in-volume gap or continuity of a response supremum is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem crossingAction_continuous (H N : ℕ) :
    Continuous
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N p.1 p.2) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil =>
      simpa using
        (continuous_const : Continuous
          (fun _ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (0 : ℝ)))
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhol :
          Continuous
            (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
              (p.1 e)⁻¹ * p.2 e) :=
        (((continuous_apply e).comp continuous_fst).inv).mul
          ((continuous_apply e).comp continuous_snd)
      have henergy := (continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hhol
      exact henergy.add ih

/-- The literal finite Wilson kernel is jointly continuous in its real coupling
and its two boundary configurations, without a positivity restriction on beta. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_joint_continuous
    (H N : ℕ) :
    Continuous
      (fun p : ℝ ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N p.1 p.2.1 p.2.2) := by
  have hleft :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H N).comp
      (continuous_fst : Continuous
        (Prod.fst :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → _))
  have hright :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H N).comp
      (continuous_snd : Continuous
        (Prod.snd :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → _))
  have haction :
      Continuous
        (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N p.1 p.2) := by
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    exact ((continuous_const.mul hleft).add (crossingAction_continuous H N)).add
      (continuous_const.mul hright)
  have hexp := Real.continuous_exp.comp
    (continuous_fst.neg.mul (haction.comp continuous_snd))
  simpa only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    using hexp

private theorem topNorm_halfLine_continuous (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta.1 beta.2‖) := by
  let lam : Set.Ici (0 : ℝ) → ℝ := fun beta =>
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta.1 beta.2‖
  have hL : LipschitzWith
      (Real.toNNReal (periodicHypercubicEvenOneSlabActionBudget H)) lam := by
    apply LipschitzWith.of_dist_le'
    intro gamma beta
    change |lam gamma - lam beta| ≤
      periodicHypercubicEvenOneSlabActionBudget H * |gamma.1 - beta.1|
    simpa only [lam, Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H N hN beta.1 gamma.1 beta.2 gamma.2
  exact hL.continuous

/-- Kernel smoothing transports the Hilbert-norm continuous canonical vacuum
into the original continuous top synthesis, jointly in coupling and boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopSynthesis_joint_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopSynthesis
          H N hN p.1.1 p.1.2 p.2) := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Omega : Set.Ici (0 : ℝ) → Lp ℝ 2 mu := fun beta =>
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta.1 beta.2).1
  let k : (Set.Ici (0 : ℝ) × X) → C(X, ℝ) := fun p =>
    ⟨fun A => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N p.1.1 A p.2,
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N p.1.1).comp (continuous_id.prodMk continuous_const)⟩
  have hk : Continuous k := by
    apply ContinuousMap.continuous_of_continuous_uncurry k
    have hp : Continuous
        (fun q : (Set.Ici (0 : ℝ) × X) × X => (q.1.1.1, (q.2, q.1.2))) := by
      fun_prop
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_joint_continuous
      H N).comp hp
  have hkL2 : Continuous
      (fun p : Set.Ici (0 : ℝ) × X =>
        ContinuousMap.toLp (E := ℝ) 2 mu ℝ (k p)) :=
    (ContinuousMap.toLp (E := ℝ) 2 mu ℝ).continuous.comp hk
  have hOmega : Continuous Omega :=
    continuous_subtype_val.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_halfLine_continuous
        H N hN)
  have hinner : Continuous
      (fun p : Set.Ici (0 : ℝ) × X =>
        inner ℝ (Omega p.1) (ContinuousMap.toLp (E := ℝ) 2 mu ℝ (k p))) :=
    (hOmega.comp continuous_fst).inner hkL2
  have heq :
      (fun p : Set.Ici (0 : ℝ) × X =>
        inner ℝ (Omega p.1) (ContinuousMap.toLp (E := ℝ) 2 mu ℝ (k p))) =
      (fun p : Set.Ici (0 : ℝ) × X =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopSynthesis
          H N hN p.1.1 p.1.2 p.2) := by
    funext p
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopSynthesis_eq_integral_kernel,
      L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := mu) (𝕜 := ℝ) (k p)] with A hA
    rw [realL2Scalar_inner_eq_mul, hA]
    rfl
  exact heq ▸ hinner

/-- Joint continuity of the existing canonical continuous vacuum representative.
Its defining denominator is the strictly positive finite-volume top norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_joint_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN p.1.1 p.1.2 p.2) := by
  have hlam := topNorm_halfLine_continuous H N hN
  have hinv := hlam.inv₀ (fun beta =>
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta.1 beta.2).ne')
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
  exact (hinv.comp continuous_fst).mul
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopSynthesis_joint_continuous
      H N hN)

/-- Continuity into the continuous-function space on the compact boundary.
Here the continuous-map topology is exactly the sup-norm topology. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_supNorm_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        (⟨periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta.1 beta.2,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
            H N hN beta.1 beta.2⟩ :
          C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N, ℝ))) := by
  exact ContinuousMap.continuous_of_continuous_uncurry _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_joint_continuous
      H N hN)

/-- Strict positivity of the original representative discharges the reciprocal
condition everywhere on the nonnegative coupling half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_inv_joint_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN p.1.1 p.1.2 p.2)⁻¹) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_joint_continuous
      H N hN).inv₀ (fun p =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN p.1.1 p.1.2 p.2).ne')

end

end MGAP4D.MathlibAnalytic
