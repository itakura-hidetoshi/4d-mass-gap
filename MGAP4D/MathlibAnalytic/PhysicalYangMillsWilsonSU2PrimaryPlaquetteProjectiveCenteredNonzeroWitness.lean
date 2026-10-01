import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteProjectiveCenteredStrongLimit
import Mathlib.Tactic

/-!
# Nonzero centered projective excitation from continuum-coherent SU(2) modes

PR #4995 shows that each vacuum-centered finite Wilson OS primary-plaquette
state converges strongly in the projective-limit L2 carrier.  The remaining
question at this layer is whether a centered limit can be nonzero.

The continuum-coherent Gram--Schmidt modes retain their finite-marginal
orthogonality.  For two distinct mode indices, choose one sufficiently large
projective marginal containing both source supports.  Both continuum vectors
are then represented by two members of the same finite orthonormal family, so
their continuum inner product is zero.

Since the continuum vacuum is a single unit vector, two orthogonal unit modes
cannot both lie on its one-dimensional line.  Therefore at least one of the
first two continuum Gram--Schmidt modes has a nonzero vacuum-centered part.
Combining this with #4995 gives an actual nonzero strong limit of finite
vacuum-orthogonal Wilson OS representatives.

No transfer-gap estimate is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

local instance projectiveCenteredNonzeroWitnessSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance projectiveCenteredNonzeroWitnessSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance projectiveCenteredNonzeroWitnessFiniteMarginalProbability
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (J : Finset EuclideanFourSpace) :
    IsProbabilityMeasure (F.finiteMarginal J) :=
  F.finiteMarginalProbability J

local instance projectiveCenteredNonzeroWitnessContinuumProbability
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Distinct continuum-coherent primary-plaquette Gram--Schmidt modes remain
orthogonal in the single projective-limit continuum L2 carrier. -/
theorem primaryPlaquetteGramSchmidtContinuumL2Mode_inner_eq_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    {i j : ℕ}
    (hij : i ≠ j) :
    inner ℝ
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L i)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L j) = 0 := by
  have hBoth :
      ∀ᶠ n in atTop,
        R.marginalIndex i ⊆ R.marginalIndex n ∧
        R.marginalIndex j ⊆ R.marginalIndex n :=
    (C.marginalSupportEventually i).and (C.marginalSupportEventually j)
  obtain ⟨n, hin, hjn⟩ := hBoth.exists
  have hi :=
    C.primaryPlaquetteGramSchmidtMode_continuum i n hin
  have hj :=
    C.primaryPlaquetteGramSchmidtMode_continuum j n hjn
  calc
    inner ℝ
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L i)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L j) =
      inner ℝ
        (L.finiteMarginalL2Pullback (R.marginalIndex n)
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n i))
        (L.finiteMarginalL2Pullback (R.marginalIndex n)
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n j)) := by
      rw [← hi, ← hj]
    _ =
      inner ℝ
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n i)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n j) := by
      exact L.finiteMarginalL2Pullback_inner
        (R.marginalIndex n)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n i)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n j)
    _ = 0 := by
      exact
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_orthonormal n).inner_eq_zero
          hij

/-- The first two continuum-coherent Gram--Schmidt modes are orthogonal unit
vectors.  This compact receipt is the only finite-dimensional geometry needed
for the nonzero centered witness below. -/
theorem primaryPlaquetteGramSchmidtContinuumL2Mode_zero_one_receipt
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    ‖R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L 0‖ = 1 ∧
    ‖R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L 1‖ = 1 ∧
    inner ℝ
      (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L 0)
      (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L 1) = 0 := by
  exact ⟨C.primaryPlaquetteGramSchmidtContinuumL2Mode_norm 0,
    C.primaryPlaquetteGramSchmidtContinuumL2Mode_norm 1,
    C.primaryPlaquetteGramSchmidtContinuumL2Mode_inner_eq_zero (by norm_num)⟩

/-- At least one of the first two continuum Gram--Schmidt modes has a nonzero
component orthogonal to the continuum vacuum. -/
theorem exists_primaryPlaquetteGramSchmidtCenteredContinuumL2Mode_ne_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    ∃ k : ℕ, (k = 0 ∨ k = 1) ∧
      C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode k ≠ 0 := by
  let vac : Lp ℝ 2 L.continuumMeasure :=
    Lp.const 2 L.continuumMeasure (1 : ℝ)
  let e0 :=
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L 0
  let e1 :=
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L 1
  have hgeom := C.primaryPlaquetteGramSchmidtContinuumL2Mode_zero_one_receipt
  have he0norm : ‖e0‖ = 1 := by simpa [e0] using hgeom.1
  have he1norm : ‖e1‖ = 1 := by simpa [e1] using hgeom.2.1
  have he01 : inner ℝ e0 e1 = 0 := by simpa [e0, e1] using hgeom.2.2
  have hvacnorm : ‖vac‖ = 1 := by
    have hv :=
      R.projectiveFiniteOSEmbed_vacuum_eq_one L U 0
    have hnorm :=
      R.projectiveFiniteOSEmbed_norm L hInvariant 0
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
          Q.toWeakStarBridge hInvariant 0)
    rw [hv] at hnorm
    simpa [vac] using hnorm.trans
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum_norm
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant 0)
  have hvacinner : inner ℝ vac vac = 1 := by
    rw [real_inner_self_eq_norm_sq, hvacnorm]
    norm_num
  by_cases h0 :
      C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode 0 ≠ 0
  · exact ⟨0, ⟨Or.inl rfl, h0⟩⟩
  · have h0zero :
        C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode 0 = 0 :=
      not_ne_iff.mp h0
    by_cases h1 :
        C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode 1 ≠ 0
    · exact ⟨1, ⟨Or.inr rfl, h1⟩⟩
    · have h1zero :
          C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode 1 = 0 :=
        not_ne_iff.mp h1
      let a0 : ℝ := inner ℝ vac e0
      let a1 : ℝ := inner ℝ vac e1
      have he0 : e0 = a0 • vac := by
        have hz := h0zero
        change finiteVacuumCentered vac e0 = 0 at hz
        unfold finiteVacuumCentered at hz
        simpa [a0] using (sub_eq_zero.mp hz)
      have he1 : e1 = a1 • vac := by
        have hz := h1zero
        change finiteVacuumCentered vac e1 = 0 at hz
        unfold finiteVacuumCentered at hz
        simpa [a1] using (sub_eq_zero.mp hz)
      have ha0 : a0 ≠ 0 := by
        intro ha0
        have he0zero : e0 = 0 := by
          simpa [ha0] using he0
        rw [he0zero, norm_zero] at he0norm
        norm_num at he0norm
      have ha1 : a1 ≠ 0 := by
        intro ha1
        have he1zero : e1 = 0 := by
          simpa [ha1] using he1
        rw [he1zero, norm_zero] at he1norm
        norm_num at he1norm
      have hmul : a0 * a1 = 0 := by
        have h := he01
        rw [he0, he1, real_inner_smul_left, real_inner_smul_right, hvacinner] at h
        simpa [mul_assoc] using h
      exact False.elim ((mul_ne_zero ha0 ha1) hmul)

/-- There is an actual nonzero projective strong limit of finite Wilson OS
vacuum-orthogonal representatives from the first two primary-plaquette modes. -/
theorem exists_nonzero_vacuumOrthogonal_projectiveStrongLimit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    ∃ k : ℕ, ∃ y : Lp ℝ 2 L.continuumMeasure,
      y ≠ 0 ∧
      Tendsto
        (fun n =>
          R.projectiveFiniteOSEmbed L hInvariant n
            (C.finiteOSCenteredPhysicalState k n))
        atTop (𝓝 y) := by
  obtain ⟨k, _hk, hy⟩ :=
    C.exists_primaryPlaquetteGramSchmidtCenteredContinuumL2Mode_ne_zero U
  exact
    ⟨k, C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode k, hy,
      C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_tendsto U k⟩

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData

end

end MathlibAnalytic
end MGAP4D
