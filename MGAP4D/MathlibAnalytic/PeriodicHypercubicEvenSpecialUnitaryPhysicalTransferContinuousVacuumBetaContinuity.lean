import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNonnegativeTopBetaContinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

/-!
# Coupling continuity of the existing continuous physical Wilson vacuum

Continuous kernel sections are mapped into the fixed Haar L2 space and paired
with the existing nonnegative physical vacuum. The resulting continuous scalar
is identified with the existing vacuum synthesis function. Division by the
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

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000

/-- Prove the pairing identity before specializing the L2 vector. This keeps
rewriting independent of the construction of the canonical vacuum. The pinned
`ContinuousMap.toLp` API uses a Borel space, not only measurable open sets. -/
private theorem realL2_inner_continuousMapToLp_eq_integral
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (f : Lp ℝ 2 mu) (k : C(X, ℝ)) :
    inner ℝ f (ContinuousMap.toLp (E := ℝ) 2 mu ℝ k) =
      ∫ A, f A * k A ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := mu) (𝕜 := ℝ) k] with A hA
  exact (realL2Scalar_inner_eq_mul (f A) _).trans
    (congrArg (fun t : ℝ => f A * t) hA)

/-- Keep the inner-product topology and the `toLp` map abstract while proving
continuity. Specializing this scalar-integral theorem does not elaborate a new
inner-product expression over the concrete Wilson Haar measure. -/
private theorem continuous_realL2_kernel_integral
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (f : P → Lp ℝ 2 mu) (k : P → C(X, ℝ))
    (hf : Continuous f) (hk : Continuous k) :
    Continuous (fun p => ∫ A, f p A * k p A ∂mu) := by
  have hkL2 : Continuous
      (fun p => ContinuousMap.toLp (E := ℝ) 2 mu ℝ (k p)) :=
    (ContinuousMap.toLp (E := ℝ) 2 mu ℝ).continuous.comp hk
  have hinner : Continuous
      (fun p => inner ℝ (f p) (ContinuousMap.toLp (E := ℝ) 2 mu ℝ (k p))) :=
    hf.inner hkL2
  have heq :
      (fun p => inner ℝ (f p) (ContinuousMap.toLp (E := ℝ) 2 mu ℝ (k p))) =
      (fun p => ∫ A, f p A * k p A ∂mu) := by
    funext p
    exact realL2_inner_continuousMapToLp_eq_integral mu (f p) (k p)
  exact Eq.mp (congrArg (fun g : P → ℝ => Continuous g) heq) hinner

/-- Curry and pass to L2 while the kernel is still an abstract parameter. -/
private theorem continuous_realL2_jointKernel_integral
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (f : P → Lp ℝ 2 mu) (K : P × X → ℝ)
    (hf : Continuous f) (hK : Continuous K) :
    Continuous (fun p => ∫ A, f p A * K (p, A) ∂mu) := by
  let k : C(P, C(X, ℝ)) := ContinuousMap.curry ⟨K, hK⟩
  exact continuous_realL2_kernel_integral mu f k hf k.continuous

-- Local instance registration does not make the declaration name module-private.
-- Explicit module-specific names keep this file compatible with the marginal-geometry imports.
local instance continuousVacuumBetaContinuitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance continuousVacuumBetaContinuitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance continuousVacuumBetaContinuitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance continuousVacuumBetaContinuitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance continuousVacuumBetaContinuitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance continuousVacuumBetaContinuitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
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
    -- Match the defining expression (left + crossing) + right.
    exact ((continuous_const.mul hleft).add
      (crossingAction_continuous H N)).add (continuous_const.mul hright)
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
      (Real.toNNReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)) lam := by
    apply LipschitzWith.of_dist_le'
    intro gamma beta
    change |lam gamma - lam beta| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        |gamma.1 - beta.1|
    simpa only [lam, Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H N hN beta.1 gamma.1 beta.2 gamma.2
  exact hL.continuous

/-- Forget gauge invariance through the existing subtype projection. -/
private theorem vacuumAsL2_halfLine_continuous (H N : ℕ) (hN : 0 < N) :
    Continuous (fun beta : Set.Ici (0 : ℝ) =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta.1 beta.2).1) := by
  exact continuous_subtype_val.comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_halfLine_continuous
      H N hN)

/-- The fixed integration variable is placed last before abstract currying. -/
private theorem vacuumKernel_reindexed_continuous (H N : ℕ) :
    Continuous (fun q : (Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N q.1.1.1 q.2 q.1.2) := by
  have hp : Continuous
      (fun q : (Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (q.1.1.1, (q.2, q.1.2))) :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_joint_continuous
    H N).comp hp

/-- Keep the concrete integral-continuity proof separate from the feature-space
identification, so kernel checking does not replay both constructions together. -/
private theorem vacuumKernel_integral_joint_continuous (H N : ℕ) (hN : 0 < N) :
    Continuous (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      ∫ A,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN p.1.1 p.1.2).1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N p.1.1 A p.2
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  exact continuous_realL2_jointKernel_integral
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN p.1.1 p.1.2).1)
    (fun q => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N q.1.1.1 q.2 q.1.2)
    ((vacuumAsL2_halfLine_continuous H N hN).comp continuous_fst)
    (vacuumKernel_reindexed_continuous H N)

/-- Functional equality with the original synthesis is an independent opaque
proof boundary, not a new definition of the physical vacuum. -/
private theorem vacuumSynthesis_eq_kernelIntegral (H N : ℕ) (hN : 0 < N) :
    (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
        H N hN p.1.1 p.1.2 p.2) =
    (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      ∫ A,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN p.1.1 p.1.2).1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N p.1.1 A p.2
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  funext p
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_eq_integral_kernel
    H N hN p.1.1 p.1.2 p.2

/-- Kernel smoothing transports the Hilbert-norm continuous canonical vacuum
into the existing vacuum synthesis function, jointly in coupling and boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_joint_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
          H N hN p.1.1 p.1.2 p.2) := by
  exact Eq.mpr
    (congrArg (fun g : (Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ => Continuous g)
      (vacuumSynthesis_eq_kernelIntegral H N hN))
    (vacuumKernel_integral_joint_continuous H N hN)

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
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_joint_continuous
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
  exact (ContinuousMap.curry ⟨_,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_joint_continuous
      H N hN⟩).continuous

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
