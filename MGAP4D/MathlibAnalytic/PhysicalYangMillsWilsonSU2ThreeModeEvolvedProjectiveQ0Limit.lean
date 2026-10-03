import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeProjectiveStrongLimit
import Mathlib.Tactic

/-!
# Uniform q0 control passes to evolved projective strong limits

The exact finite three-mode excitation of #5081 is unit, physical, and belongs
to the completed physical pair non-top sector.  PR #5083 embeds it isometrically
into one common projective-limit continuum L2 carrier and produces a nonzero
strong limit at time zero.

For a fixed natural transfer time m, this file embeds the genuinely evolved
finite pair

  S_pair,n^m x_n

through the same canonical pair-Haar -> boundary-Haar -> projective-marginal ->
continuum-L2 isometry.

The already-proved full-pair estimate gives

  ||S_pair,n^m x_n|| <= q0^m.

Because the projective embedding is isometric, the same bound holds in the
common continuum carrier at every finite scale.  Therefore *whenever* the
evolved embedded sequence has a strong limit, that limit automatically obeys
the same q0^m norm bound.

This isolates the remaining H1-C3 obstruction sharply: the quantitative decay
is already closed; what remains is existence/coherence of the evolved strong
limits (and then their identification with a continuum discrete-time
operator).

No H1-D5 compatibility, vacuum/top alignment, or pair-top convergence is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2ThreeModeEvolvedProjectiveTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2ThreeModeEvolvedProjectiveCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2ThreeModeEvolvedProjectiveSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2ThreeModeEvolvedProjectiveMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2ThreeModeEvolvedProjectiveBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2ThreeModeEvolvedProjectiveSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2ThreeModeEvolvedProjectiveSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2ThreeModeEvolvedProjectiveNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section EvolvedProjectiveQ0

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
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- The finite m-step evolved exact three-mode excitation, embedded into the
single projective-limit continuum L2 carrier. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
    (n m : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
      Q R L n
      ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m)
        (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
          Q hInvariant n))

/-- At natural time zero the evolved image is exactly the #5083 initial
projective image. -/
@[simp]
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_zero
    (n : ℕ) :
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
        Q R L hInvariant n 0 =
      physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
          Q hInvariant n) := by
  simp [
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage]

/-- The common-carrier image of every finite m-step evolved excitation retains
the exact scale-uniform q0^m bound. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_norm_le_uniform_q0
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n m : ℕ) :
    ‖physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
        Q R L hInvariant n m‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  unfold
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
  rw [physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_norm]
  exact
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_pow_norm_le_uniform_q0
      Q hInvariant s hs hcut n m

/-- Any strong limit of the m-step evolved embedded sequence inherits the same
q0^m norm bound.  Thus no additional quantitative estimate is needed at the
continuum passage; only evolved strong convergence remains. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveStrongLimit_norm_le_uniform_q0
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (phi : ℕ → ℕ) (m : ℕ)
    (z : Lp ℝ 2 L.continuumMeasure)
    (hz :
      Tendsto
        (fun j =>
          physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
            Q R L hInvariant (phi j) m)
        atTop
        (𝓝 z)) :
    ‖z‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  have hnorm :
      Tendsto
        (fun j =>
          ‖physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
            Q R L hInvariant (phi j) m‖)
        atTop
        (𝓝 ‖z‖) :=
    (continuous_norm.tendsto z).comp hz
  exact
    le_of_tendsto' hnorm
      (fun j =>
        physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_norm_le_uniform_q0
          Q R L hInvariant s hs hcut (phi j) m)

/-- The #5083 nonzero projective strong limit is exactly the natural-time-zero
case of the evolved-image family. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_exists_zero_time_strong_limit
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ y : Lp ℝ 2 L.continuumMeasure,
        ‖y‖ = 1 ∧
        Tendsto
          (fun j =>
            physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
              Q R L hInvariant (phi j) 0)
          atTop
          (𝓝 y) := by
  obtain ⟨phi, hphi, cInf, hcInf, hInitial, hyNorm⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_projective_strong_limit
      Q R L hInvariant C
  refine
    ⟨phi, hphi,
      physicalYangMillsSU2ThreeModeContinuumSynthesis
        Q R L hInvariant C cInf,
      hyNorm, ?_⟩
  simpa only [
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_zero
  ] using hInitial

end EvolvedProjectiveQ0

end

end MathlibAnalytic
end MGAP4D
