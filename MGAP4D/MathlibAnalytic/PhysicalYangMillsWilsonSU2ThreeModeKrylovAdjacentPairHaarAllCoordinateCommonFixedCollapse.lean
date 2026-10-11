import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualCoordinateOrthogonalProjections
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarPiAEIntersectionTransport
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Tactic

/-!
# P4-Q2-CS: ACTUAL pair-Haar coordinate projections' exact common fixed sector

CR constructed the literal single-coordinate conditional-expectation
orthogonal projections on the genuine left/right spatial pair-Haar L².
Here we prove that ALL of those actual projections have EXACTLY the
real a.e.-constant sector as their simultaneous common fixed vectors.

The key is a finite induction using the PREEXISTING genuinely
product-Haar two-support Fubini/AE-sigma-algebra intersection theorem.
Intersecting the sigma-algebras omitting each actual coordinate leaves
the bottom sigma-algebra. Any a.e.-measurable real function with respect
to that trivial sigma-algebra is a.e. constant.

We obtain the exact zero locus of the finite sum of original pair-Haar
projection defect squared norms, without asserting pairwise commutation
or a positive quantitative Poincare coefficient.

A final theorem provides that, IF genuine pairwise commutation is later
proved, the corresponding actual CQ sweep automatically has an a.e.
constant output. This assumption is VISIBLE and is not inferred from
positive-beta Wilson joint conditional laws.

No sorry, admit, axioms, reverse physical Wilson gap, uniform spectral
gap or continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- Finite intersection of actual coordinate-retention sigma-algebras.
This is Fubini gluing, not a general commuting-conditional-expectation law.
The explicit anchor works even before assuming the index type nonempty. -/
private theorem p4Q2CS_finite_allSupports
    {Ω ι K κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [MeasurableSpace K]
    (ω : Measure Ω) (η : Measure K) [IsProbabilityMeasure η]
    (e : Ω ≃ᵐ (ι → K))
    (he : MeasurePreserving e ω (Measure.pi (fun _ : ι => η)))
    (anchor : κ) (p : κ → ι → Prop) [∀ k, DecidablePred (p k)]
    (f : Ω → ℝ)
    (h : ∀ k : κ,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := K) (p k)) ∘ e)
          (inferInstance : MeasurableSpace ({i : ι // p k i} → K))]
        f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K) (fun i => ∀ k : κ, p k i)) ∘ e)
        (inferInstance : MeasurableSpace ({i : ι // ∀ k : κ, p k i} → K))]
      f ω := by
  classical
  have hfin : ∀ s : Finset κ,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := K)
              (fun i => p anchor i ∧ ∀ k ∈ s, p k i)) ∘ e)
          (inferInstance : MeasurableSpace
            ({i : ι // p anchor i ∧ ∀ k ∈ s, p k i} → K))]
        f ω := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hp :
            (fun i : ι => p anchor i ∧ ∀ k ∈ (∅ : Finset κ), p k i) =
              p anchor := by
          funext i
          simp
        rw [hp]
        exact h anchor
    | @insert k s hk hs =>
        have hAnd :=
          aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
            ω η e he
            (fun i : ι => p anchor i ∧ ∀ t ∈ s, p t i) (p k)
            f hs (h k)
        have hp :
            (fun i : ι => p anchor i ∧ ∀ t ∈ insert k s, p t i) =
              (fun i : ι => (p anchor i ∧ ∀ t ∈ s, p t i) ∧ p k i) := by
          funext i
          apply propext
          constructor
          · rintro ⟨ha, hall⟩
            refine ⟨⟨ha, ?_⟩, hall k (Finset.mem_insert_self k s)⟩
            intro t ht
            exact hall t (Finset.mem_insert_of_mem ht)
          · rintro ⟨⟨ha, hall⟩, hk'⟩
            refine ⟨ha, ?_⟩
            intro t ht
            rcases Finset.mem_insert.mp ht with rfl | ht'
            · exact hk'
            · exact hall t ht'
        rw [hp]
        exact hAnd
  have hall := hfin Finset.univ
  have hp :
      (fun i : ι => p anchor i ∧ ∀ k ∈ (Finset.univ : Finset κ), p k i) =
        (fun i : ι => ∀ k : κ, p k i) := by
    funext i
    apply propext
    constructor
    · intro hh k
      exact hh.2 k (Finset.mem_univ k)
    · intro hh
      exact ⟨hh anchor, fun k _ => hh k⟩
  rw [hp] at hall
  exact hall

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N

/-- Every actual left/right coordinate-Haar projection fixes x exactly
if and only if x itself is genuinely pair-Haar-a.e. constant.
There is NO pairwise-commutation premise. -/
theorem p4Q2CS_actualPairHaar_allCoordinateFixed_iff_aeConst
    (x : JH) :
    (∀ i : I, P i x = x) ↔
      ∃ c : ℝ, (x : Joint → ℝ) =ᵐ[muPair] fun _ => c := by
  classical
  constructor
  · intro hfixed
    let e :=
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N
    let η : Measure G := normalizedCompactHaar G
    have he : MeasurePreserving e muPair (Measure.pi (fun _ : I => η)) := by
      simpa [e, η] using
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
          H N)
    have hsingle : ∀ i : I,
        AEStronglyMeasurable[
          MeasurableSpace.comap
            ((pairHaarPiRestriction (K := G) (fun j : I => j ≠ i)) ∘ e)
            (inferInstance : MeasurableSpace ({j : I // j ≠ i} → G))]
          (x : Joint → ℝ) muPair := by
      intro i
      exact
        (p4Q2CR_actualPairHaarCoordinateProjection_fixed_iff
          H N i x).mp (hfixed i)
    have hAll :=
      p4Q2CS_finite_allSupports muPair η e he
        (Sum.inl (p4Q2BA_sixColorRepresentatives H 0) : I)
        (fun i j : I => j ≠ i) (x : Joint → ℝ) hsingle
    have hp :
        (fun j : I => ∀ i : I, j ≠ i) = (fun _ : I => False) := by
      funext j
      apply propext
      constructor
      · intro hj
        exact hj j rfl
      · intro hf
        exact False.elim hf
    rw [hp] at hAll
    have hbot :
        Measurable[⊥]
          ((pairHaarPiRestriction (K := G) (fun _ : I => False)) ∘ e) := by
      letI : MeasurableSpace Joint := ⊥
      change Measurable
        ((pairHaarPiRestriction (K := G) (fun _ : I => False)) ∘ e)
      rw [measurable_pi_iff]
      intro i
      exact False.elim i.property
    have htrivial : AEStronglyMeasurable[⊥] (x : Joint → ℝ) muPair :=
      hAll.mono (measurable_iff_comap_le.mp hbot)
    obtain ⟨c, hc⟩ :=
      stronglyMeasurable_bot_iff.mp htrivial.stronglyMeasurable_mk
    refine ⟨c, ?_⟩
    simpa [hc] using htrivial.ae_eq_mk
  · rintro ⟨c, hc⟩ i
    apply (p4Q2CR_actualPairHaarCoordinateProjection_fixed_iff
      H N i x).2
    have hconst :
        AEStronglyMeasurable[
          p4Q2CR_actualPairHaarOffCoordinateSigma H N i]
          (fun _ : Joint => c) muPair :=
      aestronglyMeasurable_const
    exact hconst.congr hc.symm

/-- Sum of squared true coordinate-conditional projection defects on
the ACTUAL independent pair-Haar L² space. No Wilson fiber substitution. -/
noncomputable def p4Q2CS_actualPairHaarCoordinateDefectEnergy
    (x : JH) : ℝ :=
  ∑ i : I, ‖x - P i x‖ ^ 2

/-- The genuine unnormalized pair-Haar all-coordinate energy is exactly
zero on the a.e. constants and on no other real L² vectors.
This is qualitative definiteness WITHOUT a claimed spectral-gap constant. -/
theorem p4Q2CS_actualPairHaarCoordinateDefectEnergy_zero_iff_aeConst
    (x : JH) :
    p4Q2CS_actualPairHaarCoordinateDefectEnergy H N x = 0 ↔
      ∃ c : ℝ, (x : Joint → ℝ) =ᵐ[muPair] fun _ => c := by
  rw [p4Q2CS_actualPairHaarCoordinateDefectEnergy,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x - P i x‖)]
  have hiff :
      (∀ i : I, ‖x - P i x‖ ^ 2 = 0) ↔
        (∀ i : I, P i x = x) := by
    constructor
    · intro hz i
      have hnorm : ‖x - P i x‖ = 0 := by
        nlinarith [hz i, norm_nonneg (x - P i x)]
      have hsub : x - P i x = 0 := norm_eq_zero.mp hnorm
      exact (sub_eq_zero.mp hsub).symm
    · intro hz i
      rw [hz i]
      simp
  simp only [Finset.mem_univ, forall_const] at *
  exact hiff.trans
    (p4Q2CS_actualPairHaar_allCoordinateFixed_iff_aeConst H N x)

/-- In the presence of the STILL-UNPROVED pairwise Haar coordinate
commutation, CQ's full finite sweep has an a.e.-constant output.
The next task is proving commutation by literal independent Haar Fubini,
not imposing it as a new permanent assumption. -/
private theorem p4Q2CS_sweep_fixed_of_mem
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ι → E →L[ℝ] E)
    (hId : ∀ i x, R i (R i x) = R i x)
    (hComm : ∀ i j x, R i (R j x) = R j (R i x))
    (i : ι) (rest : List ι) (hi : i ∈ rest) (x : E) :
    R i (p4Q2CQ_projectionSweep R rest x) =
      p4Q2CQ_projectionSweep R rest x := by
  induction rest generalizing x with
  | nil =>
      simp at hi
  | cons j tail ih =>
      simp only [List.mem_cons] at hi
      rcases hi with hij | hit
      · subst j
        change R i (p4Q2CQ_projectionSweep R tail (R i x)) =
          p4Q2CQ_projectionSweep R tail (R i x)
        rw [p4Q2CQ_projection_commute_sweep R hComm i tail (R i x),
          hId i x]
      · change R i (p4Q2CQ_projectionSweep R tail (R j x)) =
          p4Q2CQ_projectionSweep R tail (R j x)
        exact ih hit (R j x)

/-- A fully explicit finite-sweep constancy result for the actual
pair-Haar coordinate projections, conditional on their commutation. -/
theorem p4Q2CS_actualPairHaarSweep_aeConst_of_commuting
    (hComm : ∀ i j : I, ∀ x : JH,
      P i (P j x) = P j (P i x))
    (x : JH) :
    ∃ c : ℝ,
      (p4Q2CQ_projectionSweep P (p4Q2CQ_finiteCoordinates I) x :
        Joint → ℝ) =ᵐ[muPair] fun _ => c := by
  classical
  have hmem (i : I) : i ∈ p4Q2CQ_finiteCoordinates I := by
    unfold p4Q2CQ_finiteCoordinates
    apply List.mem_ofFn.mpr
    refine ⟨(Fintype.equivFin I) i, ?_⟩
    simp
  have hfix : ∀ i : I,
      P i (p4Q2CQ_projectionSweep P (p4Q2CQ_finiteCoordinates I) x) =
        p4Q2CQ_projectionSweep P (p4Q2CQ_finiteCoordinates I) x := by
    intro i
    exact p4Q2CS_sweep_fixed_of_mem P
      (p4Q2CR_actualPairHaarCoordinateProjection_idempotent H N)
      hComm i (p4Q2CQ_finiteCoordinates I) (hmem i) x
  exact
    (p4Q2CS_actualPairHaar_allCoordinateFixed_iff_aeConst
      H N (p4Q2CQ_projectionSweep P (p4Q2CQ_finiteCoordinates I) x)).mp hfix

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
