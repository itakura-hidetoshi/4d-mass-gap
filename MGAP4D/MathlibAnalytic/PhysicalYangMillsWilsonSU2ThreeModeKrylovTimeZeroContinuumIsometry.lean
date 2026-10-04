import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovFiniteMarginalCauchyDefect
import Mathlib.Tactic

/-!
# Time-zero continuum isometry from the finite-marginal Krylov Cauchy route

PR #5096 reduces existence of all fixed-natural-time continuum Krylov limits to
one finite union-marginal Cauchy defect.

At natural time zero there is additional exact structure.

For every finite scale n, the evolved three-mode synthesis at m = 0 is simply

  R^3 --Syn_n--> pair Haar L2 --J_n--> common continuum L2,

where Syn_n and J_n are linear isometries. Hence

  ||A_{n,0} c|| = ||c||

for every coefficient c.

The #5091 basis-coherence theorem, instantiated with the #5096 Cauchy-generated
Krylov modes, gives strong convergence

  A_{n,0} c -> A_{∞,0} c.

Norm continuity therefore forces

  ||A_{∞,0} c|| = ||c||.

Thus the theorem-generated continuum time-zero synthesis is itself a genuine
linear isometry. In particular, the compactness-selected coefficient
c_∞ with ||c_∞|| = 1 produces a nonzero continuum initial excitation of exact
norm one.

This closes nontriviality of the Cauchy-defect continuum trajectory without
reusing the separate #5083 coherent-readout strong-limit construction.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2KrylovTimeZeroTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovTimeZeroCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovTimeZeroSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovTimeZeroMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovTimeZeroBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovTimeZeroSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovTimeZeroSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2KrylovTimeZeroNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section TimeZero

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

/-- At natural time zero, every finite evolved three-mode synthesis is exactly
isometric. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_zero_norm
    (n : ℕ)
    (c : EuclideanSpace ℝ (Fin 3)) :
    ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
        Q R L n 0 c‖ = ‖c‖ := by
  unfold physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
  change
    ‖physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding Q R L n
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) ^ 0)
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c))‖ = ‖c‖
  rw [
    (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
      Q R L n).norm_map]
  simpa using
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_norm
      (halfExtent n) c

namespace PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput
        (Q := Q) (R := R))

include C

/-- The #5096 theorem-generated continuum synthesis preserves every norm at
natural time zero. -/
theorem continuumSynthesis_zero_norm
    (c : EuclideanSpace ℝ (Fin 3)) :
    ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
        Q R L
        (toEvolvedBasisCoherenceInput Q R L C)
        0 c‖ = ‖c‖ := by
  have hStrong :
      Tendsto
        (fun n =>
          physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
            Q R L n 0 c)
        atTop
        (𝓝
          (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
            Q R L
            (toEvolvedBasisCoherenceInput Q R L C)
            0 c)) :=
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.finiteSynthesis_tendsto
      Q R L
      (toEvolvedBasisCoherenceInput Q R L C)
      0 c
  have hNorm :
      Tendsto
        (fun n =>
          ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
            Q R L n 0 c‖)
        atTop
        (𝓝
          ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
            Q R L
            (toEvolvedBasisCoherenceInput Q R L C)
            0 c‖) :=
    hStrong.norm
  have hConst :
      Tendsto
        (fun _ : ℕ => ‖c‖)
        atTop
        (𝓝 ‖c‖) :=
    tendsto_const_nhds
  have hFiniteNorm :
      Tendsto
        (fun n =>
          ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
            Q R L n 0 c‖)
        atTop
        (𝓝 ‖c‖) := by
    simpa only [
      physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_zero_norm
        Q R L
    ] using hConst
  exact tendsto_nhds_unique hNorm hFiniteNorm

/-- The theorem-generated continuum time-zero three-mode synthesis is a genuine
linear isometry. -/
noncomputable def continuumTimeZeroSynthesisLinearIsometry :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ]
      Lp ℝ 2 L.continuumMeasure where
  toLinearMap :=
    (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
      Q R L
      (toEvolvedBasisCoherenceInput Q R L C)
      0).toLinearMap
  norm_map' := continuumSynthesis_zero_norm Q R L C

@[simp]
theorem continuumTimeZeroSynthesisLinearIsometry_apply
    (c : EuclideanSpace ℝ (Fin 3)) :
    continuumTimeZeroSynthesisLinearIsometry Q R L C c =
      PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
        Q R L
        (toEvolvedBasisCoherenceInput Q R L C)
        0 c :=
  rfl

/-- The Cauchy-defect route theorem-generates one exact norm-one nonzero
continuum initial excitation, together with all fixed-time strong limits and
their q0^m decay. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_nonzero_continuum_initial_and_evolved_strong_limits_q0
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
        ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
            Q R L
            (toEvolvedBasisCoherenceInput Q R L C)
            0 cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝
                (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                  Q R L
                  (toEvolvedBasisCoherenceInput Q R L C)
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (toEvolvedBasisCoherenceInput Q R L C)
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  obtain ⟨phi, hphi, cInf, hcInf, hAll⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L C hInvariant s hs hcut
  refine ⟨phi, hphi, cInf, hcInf, ?_, hAll⟩
  simpa [hcInf] using
    continuumSynthesis_zero_norm Q R L C cInf

end PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput

end TimeZero

end

end MathlibAnalytic
end MGAP4D
