import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTruePlaquetteKernelVariancePosV5_MV
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorWeakFrozenNoGoV5_JL
import Mathlib.Tactic

/-!
# P4-Q2-MW — the ACTUAL signed interacting-Wilson receiver variance
# is the remaining obstruction, even though real plaquettes fluctuate

MV proves EVERY actual original spatial SU(2) Wilson plaquette has
STRICTLY POSITIVE variance under the normalized true positive
one-slab Wilson kernel, at each H and b>=0. This cannot be exchanged
for strict nondegeneracy of the signed receiver.

The existing MU normalized signed two-interacting-posterior score
variance is IDENTICALLY the true MS Wilson kernel variance of MQ's
exact continuous one-link score.

Consequently:
(1) If the true score takes two distinct values on the ORIGINAL
spatial configuration space, its actual Wilson-kernel variance is >0.
(2) If the actual score variance is zero, the original continuous
signed receiver score is pointwise CONSTANT on the genuine spatial
configuration space, by strictly positive Wilson kernel/full Haar
support — not merely Haar-a.e. constant.
(3) If the true score variance is zero, the original centered
GAUSS-LAW Wilson plaquette physical GI readout is ZERO for every
actual spatial plaquette, using MU's verified physical Cauchy–Schwarz
and the positivity of the actual original transfer and kernel norms.
(4) Thus nonzero real centered physical GI readout NECESSARILY
implies strictly positive original signed score variance.
(5) At the ACTUAL decoupled frozen beta=0 endpoint, JL proves
the original two-interacting-posterior signed JH fiber Riesz
representer is ZERO. Its original MQ signed score is therefore
identically zero and its genuine Wilson conditional variance is zero.

This makes the analytic obstruction honest:
  strict Var_K(W_{H,p})>0 does NOT yield
  Var_K(Psi_(e,z))>0, much less
  Cov_K(W_{H,p},Psi_(e,z)) != 0,
  let alone any H-uniform positive GI coercivity floor.
One must prove actual positive-beta signed receiver nonconstancy and
a connected-correlation LOWER certificate on the existing model
before H1-C3 and continuum 4D Yang-Mills mass gap can be closed.

No independent-Haar posterior, new physical detector/source/rank,
Dobrushin, sorry, admit or axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "Mass" => p4Q2MR_originalWilsonKernelMass H b
local notation "Mean" => p4Q2MS_originalWilsonKernelConditionalMean H b
local notation "Var" => p4Q2MS_originalWilsonKernelConditionalVariance H b
local notation "PsiC" => p4Q2MU_originalSignedWilsonScoreContinuous H b hb
local notation "ScoreVar" => p4Q2MU_originalSignedScoreWilsonConditionalVariance H b hb
local notation "GI" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
local notation "tN" => p4Q2LW_originalPhysicalTransferNorm H b hb
local notation "Centered" => p4Q2MS_originalPhysicalCenteredWilsonPlaquetteSource H b

/-- MU's signed original two-interacting-posterior score variance is
literally the SAME positive genuine Wilson kernel conditional
variance as MS defined for every continuous source. -/
theorem p4Q2MW_originalSignedScoreVariance_eq_actualKernelVariance
    (e : Link) (z : Cfg × Cfg) :
    ScoreVar e z = Var z (PsiC e z) := by
  change
    Mean z
      ((PsiC e z - (Mean z (PsiC e z)) • (1 : C(Cfg, ℝ))) *
        (PsiC e z - (Mean z (PsiC e z)) • (1 : C(Cfg, ℝ)))) =
      Var z (PsiC e z)
  exact
    (p4Q2MU_originalWilsonVariance_eq_centeredMeanSq
      H b z (PsiC e z)).symm

/-- A witnessed nonconstant ORIGINAL signed two-interacting-Wilson
posterior receiver score has strictly positive Wilson-kernel
conditional variance. This theorem does not assert that the
witness exists at arbitrary positive coupling. -/
theorem p4Q2MW_originalSignedScoreVariance_pos_of_distinct
    (e : Link) (z : Cfg × Cfg)
    (A₀ A₁ : Cfg) (h : PsiC e z A₀ ≠ PsiC e z A₁) :
    0 < ScoreVar e z := by
  rw [p4Q2MW_originalSignedScoreVariance_eq_actualKernelVariance]
  exact p4Q2MV_originalWilsonVariance_pos_of_distinct_values
    H b z (PsiC e z) A₀ A₁ h

/-- If the actual signed score's conditional Wilson variance is zero,
then it is CONSTANT pointwise across all true SU(2) spatial link
configurations (not merely Haar-a.e.). The positive Wilson kernel
and full Haar support are used by MV's strict-variance theorem. -/
theorem p4Q2MW_originalSignedScoreVariance_zero_forces_constant
    (e : Link) (z : Cfg × Cfg)
    (hZero : ScoreVar e z = 0) (A₀ A₁ : Cfg) :
    PsiC e z A₀ = PsiC e z A₁ := by
  by_contra hDiff
  have hPos := p4Q2MW_originalSignedScoreVariance_pos_of_distinct
    H b hb e z A₀ A₁ hDiff
  rw [hZero] at hPos
  exact (lt_irrefl (0 : ℝ)) hPos

/-- The TRUE centered Gauss-law plaquette source signed GI readout
vanishes whenever the REAL original signed two-posterior receiver
score's Wilson-kernel conditional variance vanishes.
This follows from MU's proved upper bound and MS/LW's actual strictly
positive kernel and physical transfer normalizations. -/
theorem p4Q2MW_originalSignedScoreVariance_zero_forces_centeredPhysicalGI_zero
    (e : Link) (z : Cfg × Cfg) (p : Plaq)
    (hZero : ScoreVar e z = 0) :
    GI (Centered z p) e z = 0 := by
  have hBound :=
    p4Q2MU_originalPhysicalCenteredGI_sq_le_trueWilsonVariances
      H b hb e z p
  rw [hZero] at hBound
  have hNorm :
      (tN / Mass z * GI (Centered z p) e z)^2 ≤ 0 := by
    simpa using hBound
  have hProd : (tN / Mass z) * GI (Centered z p) e z = 0 := by
    nlinarith [sq_nonneg ((tN / Mass z) * GI (Centered z p) e z)]
  have hFactor :
      tN / Mass z ≠ 0 :=
    (div_pos (p4Q2LW_originalPhysicalTransferNorm_pos H b hb)
      (p4Q2MS_originalWilsonKernelMass_pos H b z)).ne'
  exact (mul_eq_zero.mp hProd).resolve_left hFactor

/-- A NONZERO actual original centered Gauss-law Wilson local physical
GI response requires strict POSITIVITY of the original signed
receiver score Wilson conditional variance. It does not establish
that any nonzero readout exists uniformly in H or at b>0. -/
theorem p4Q2MW_originalCenteredPhysicalGI_nonzero_requires_signedVariance_pos
    (e : Link) (z : Cfg × Cfg) (p : Plaq)
    (hGI : GI (Centered z p) e z ≠ 0) :
    0 < ScoreVar e z := by
  have hNonneg :=
    p4Q2MU_originalSignedScoreWilsonVariance_nonneg H b hb e z
  by_contra hNot
  have hZero : ScoreVar e z = 0 :=
    le_antisymm (le_of_not_gt hNot) hNonneg
  exact hGI
    (p4Q2MW_originalSignedScoreVariance_zero_forces_centeredPhysicalGI_zero
      H b hb e z p hZero)

end Frozen

/-- At the GENUINE original frozen beta=0 endpoint, both ACTUAL
interacting Wilson conditional posteriors coincide (JL). The
original JH Riesz representer, thus MQ's original signed local
profile and its continuous presentation, are identically zero
on the TRUE full SU(2) spatial configuration space. -/
theorem p4Q2MW_originalSignedReceiverScore_zero_at_frozen_zero
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2MU_originalSignedWilsonScoreContinuous H 0 (le_refl (0 : ℝ)) e z = 0 := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  ext A
  change p4Q2MQ_originalSignedLocalFiberProfile H 0
    (le_refl (0 : ℝ)) e z A = 0
  have hRatio :=
    p4Q2MQ_originalSignedRiesz_div_originalKernel_eq_localProfile
      H 0 (le_refl (0 : ℝ)) e z A
  rw [p4Q2JL_originalFiberRepresenter_zero H e z] at hRatio
  simpa using hRatio.symm

/-- EXACT original beta=0 NO-GO: the same genuinely normalized
Wilson-kernel conditional variance of the actual signed posterior
receiver score is ZERO for all finite H and all authentic contexts.
A positive plaquette variance alone cannot furnish GI coercivity. -/
theorem p4Q2MW_originalSignedScoreVariance_zero_at_frozen_zero
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2MU_originalSignedScoreWilsonConditionalVariance
      H 0 (le_refl (0 : ℝ)) e z = 0 := by
  have hScore :=
    p4Q2MW_originalSignedReceiverScore_zero_at_frozen_zero H e z
  rw [p4Q2MW_originalSignedScoreVariance_eq_actualKernelVariance
    H 0 (le_refl (0 : ℝ)) e z, hScore]
  unfold p4Q2MS_originalWilsonKernelConditionalVariance
    p4Q2MS_originalWilsonKernelConditionalMean
    p4Q2MR_originalWilsonKernelMoment
  simp

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MW_originalSignedScoreVariance_eq_actualKernelVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MW_originalSignedScoreVariance_pos_of_distinct
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MW_originalSignedScoreVariance_zero_forces_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MW_originalSignedScoreVariance_zero_forces_centeredPhysicalGI_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MW_originalCenteredPhysicalGI_nonzero_requires_signedVariance_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MW_originalSignedReceiverScore_zero_at_frozen_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MW_originalSignedScoreVariance_zero_at_frozen_zero
