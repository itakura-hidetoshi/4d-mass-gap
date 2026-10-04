import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PhysicalDirectedClosureTransferContraction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeEvolvedProjectiveQ0Limit
import Mathlib.Tactic

/-!
# Reduce evolved strong convergence to three-mode synthesis coherence

PR #5089 shows that the actual normalized pair transfer is contractive on the
completed physical pair carrier and reduces the directed-closure continuum
operator route to exact cross-scale operator compatibility.

For the theorem-generated three-mode excitation, full operator compatibility
is stronger than is needed merely to obtain evolved strong limits.

At scale n and natural time m, compose

  R^3 --Syn_n--> physical pair Haar L2
      --S_n^m--> physical pair Haar L2
      --J_n--> common projective continuum L2.

Because Syn_n is isometric and lands in the physical pair carrier, while S_n
is contractive on that carrier, this evolved synthesis is uniformly
contractive:

  ||A_{n,m} c|| <= ||c||.

A general varying-contraction lemma then says:

  c_n -> c,
  A_n c -> z,
  ||A_n v|| <= ||v||
  -------------------
  A_n c_n -> z.

Therefore the #5082 coefficient subsequence needs only pointwise strong
coherence of the evolved three-dimensional synthesis, not compatibility of an
operator on the whole selected finite marginal.

The resulting strong limits automatically inherit the existing q0^m bound from
#5084.

This sharply narrows the remaining H1-C3 existence input to a finite-dimensional
Krylov-synthesis coherence problem.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

/-- Uniformly contractive varying operators preserve convergence when both the
input vector and the image of its limit vector converge. -/
theorem tendsto_varying_contraction_apply_of_tendsto_fixed
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : ℕ → E →L[ℝ] H)
    (hA : ∀ n x, ‖A n x‖ ≤ ‖x‖)
    (c : ℕ → E) (cInf : E) (z : H)
    (hc : Tendsto c atTop (𝓝 cInf))
    (hfixed : Tendsto (fun n => A n cInf) atTop (𝓝 z)) :
    Tendsto (fun n => A n (c n)) atTop (𝓝 z) := by
  have hconst :
      Tendsto (fun _ : ℕ => cInf) atTop (𝓝 cInf) :=
    tendsto_const_nhds
  have hcsub :
      Tendsto (fun n => c n - cInf) atTop (𝓝 0) := by
    simpa using hc.sub hconst
  have hnormsub :
      Tendsto (fun n => ‖c n - cInf‖) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      ((continuous_norm.tendsto (0 : E)).comp hcsub)
  have hdiff :
      Tendsto (fun n => A n (c n - cInf)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero
      (fun n => norm_nonneg (A n (c n - cInf)))
      (fun n => hA n (c n - cInf))
      hnormsub
  have hadd :
      Tendsto
        (fun n => A n (c n - cInf) + A n cInf)
        atTop (𝓝 z) := by
    simpa using hdiff.add hfixed
  apply hadd.congr'
  exact Filter.Eventually.of_forall fun n => by
    change A n (c n - cInf) + A n cInf = A n (c n)
    rw [← (A n).map_add, sub_add_cancel]

local instance su2ThreeModeEvolvedSynthesisTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2ThreeModeEvolvedSynthesisCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2ThreeModeEvolvedSynthesisSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2ThreeModeEvolvedSynthesisMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2ThreeModeEvolvedSynthesisBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2ThreeModeEvolvedSynthesisSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2ThreeModeEvolvedSynthesisSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2ThreeModeEvolvedSynthesisNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section EvolvedSynthesis

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- Natural powers of normalized pair transfer remain contractive on the
completed physical pair carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_norm_le_one
    (H m : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2)
    (hx :
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2) :
    ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive b hb ^ m) x‖ ≤ ‖x‖ := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive b hb
  change ‖(T ^ m) x‖ ≤ ‖x‖
  induction m generalizing x with
  | zero =>
      simp
  | succ m ih =>
      have hxT :
          T x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2 := by
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
            H 2 specialUnitaryTwoWilsonRankPositive b hb hx
      change ‖(T ^ m) (T x)‖ ≤ ‖x‖
      exact
        (ih (T x) hxT).trans
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_norm_le_one
            H b hb x hx)

/-- The first-three-mode synthesis after m genuine finite transfer steps,
embedded into the single common projective continuum carrier. -/
noncomputable def physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
    (n m : ℕ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
      Q R L n).toContinuousLinearMap.comp
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) ^ m).comp
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        (halfExtent n)).toContinuousLinearMap)

/-- Every finite evolved three-mode synthesis has operator bound one. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_norm_le
    (n m : ℕ)
    (c : EuclideanSpace ℝ (Fin 3)) :
    ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
        Q R L n m c‖ ≤ ‖c‖ := by
  unfold physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
  change
    ‖physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding Q R L n
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) ^ m)
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c))‖ ≤ ‖c‖
  rw [
    (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
      Q R L n).norm_map]
  calc
    ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) ^ m)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c)‖
      ≤
        ‖periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c‖ := by
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_norm_le_one
              (halfExtent n) m (beta n) (hbeta n)
              (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
                (halfExtent n) c)
              (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_mem_physicalPairCarrier
                (halfExtent n) c)
    _ = ‖c‖ :=
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_norm
        (halfExtent n) c

/-- The exact chosen finite excitation is obtained by applying the evolved
synthesis to the chosen #5082 coefficient. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_eq_evolvedSynthesis
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n m : ℕ) :
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
        Q R L hInvariant n m =
      physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
        Q R L n m
        (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
          Q hInvariant n) := by
  rfl

/-- Pointwise strong coherence of only the evolved three-dimensional synthesis.

This is strictly weaker data than a compatible operator on every selected
finite marginal. -/
structure PhysicalYangMillsSU2ThreeModeEvolvedSynthesisCoherenceInput where
  continuumSynthesis :
    ℕ → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      Lp ℝ 2 L.continuumMeasure
  finiteSynthesis_tendsto :
    ∀ (m : ℕ) (c : EuclideanSpace ℝ (Fin 3)),
      Tendsto
        (fun n =>
          physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
            Q R L n m c)
        atTop
        (𝓝 (continuumSynthesis m c))

namespace PhysicalYangMillsSU2ThreeModeEvolvedSynthesisCoherenceInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeEvolvedSynthesisCoherenceInput
        Q R L)

/-- The continuum evolved synthesis is itself contractive pointwise. -/
theorem continuumSynthesis_norm_le
    (m : ℕ)
    (c : EuclideanSpace ℝ (Fin 3)) :
    ‖C.continuumSynthesis m c‖ ≤ ‖c‖ := by
  have hnorm :
      Tendsto
        (fun n =>
          ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
            Q R L n m c‖)
        atTop
        (𝓝 ‖C.continuumSynthesis m c‖) :=
    (continuous_norm.tendsto _).comp
      (C.finiteSynthesis_tendsto m c)
  exact
    le_of_tendsto' hnorm
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_norm_le
          Q R L n m c)

/-- Pointwise three-mode synthesis coherence is enough to give, along the
#5082 coefficient subsequence, strong limits at every fixed natural time. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
            (fun j =>
              physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                Q R L hInvariant (phi j) m)
            atTop
            (𝓝 (C.continuumSynthesis m cInf)) := by
  obtain ⟨phi, hphi, cInf, hcInf, hcTendsto⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_exists_strictMono_tendsto
      Q hInvariant
  refine ⟨phi, hphi, cInf, hcInf, ?_⟩
  intro m
  have hfixed :
      Tendsto
        (fun j =>
          physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
            Q R L (phi j) m cInf)
        atTop
        (𝓝 (C.continuumSynthesis m cInf)) := by
    exact
      (C.finiteSynthesis_tendsto m cInf).comp
        hphi.tendsto_atTop
  have hvary :
      Tendsto
        (fun j =>
          physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
            Q R L (phi j) m
            (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
              Q hInvariant (phi j)))
        atTop
        (𝓝 (C.continuumSynthesis m cInf)) := by
    apply
      tendsto_varying_contraction_apply_of_tendsto_fixed
        (fun j =>
          physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
            Q R L (phi j) m)
        (fun j c =>
          physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_norm_le
            Q R L (phi j) m c)
        (fun j =>
          physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
            Q hInvariant (phi j))
        cInf
        (C.continuumSynthesis m cInf)
    · simpa [Function.comp_def] using hcTendsto
    · exact hfixed
  simpa only [
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_eq_evolvedSynthesis
  ] using hvary

/-- Combining mode-coherence strong limits with #5084 transports the full
uniform q0^m estimate to every continuum evolved limit. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝 (C.continuumSynthesis m cInf)) ∧
            ‖C.continuumSynthesis m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  obtain ⟨phi, hphi, cInf, hcInf, hStrong⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L C hInvariant
  refine ⟨phi, hphi, cInf, hcInf, ?_⟩
  intro m
  refine ⟨hStrong m, ?_⟩
  exact
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveStrongLimit_norm_le_uniform_q0
      Q R L hInvariant s hs hcut phi m
      (C.continuumSynthesis m cInf)
      (hStrong m)

end PhysicalYangMillsSU2ThreeModeEvolvedSynthesisCoherenceInput

end EvolvedSynthesis

end

end MathlibAnalytic
end MGAP4D
