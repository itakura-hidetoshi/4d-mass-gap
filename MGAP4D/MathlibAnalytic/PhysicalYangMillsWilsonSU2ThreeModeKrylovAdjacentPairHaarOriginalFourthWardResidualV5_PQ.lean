import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralFourthCoefficientV5_PP5
import Mathlib.Tactic

/-!
# P4-Q2-PQ — original Wilson fourth coefficient and Ward-normalized obstruction

PP5 gives the true Wilson literal three-boundary determinant as
beta^4 times the FULL original Haar action-moment coefficient plus
a fifth-order remainder. PM proves that the genuine mixed second
moment is affine in the first derivative.

The resulting fourth coefficient has a simpler, exact physical
obstruction: the failure of a single ORIGINAL third-order Haar
profile to be affine in the ORIGINAL first-order Wilson profile.

No assertion that this profile fails to be affine is inserted.
In particular, the fourth coefficient can still vanish for ALL
physical spatial configurations. No new posterior, alternate
spectral representation, rank axiom, sorry or admit is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalWilsonQuarticWardResidual
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H
local notation "C4" => p4Q2PP2_originalFourthCoefficient H

/-- The true first Wilson action-moment's original spatial Haar mean.
No posterior measure is substituted for this normalized reference Haar. -/
noncomputable def p4Q2PQ_originalFirstActionMean : ℝ :=
  ∫ X : Cfg, a X ∂haar

/-- The Ward-normalized FULL third-order physical profile.
The -3 * mean(a) * b term is essential: it cancels the exact
quadratic-jet contribution in the genuine fourth coefficient.
Both c and g are the complete original Wilson Haar moments. -/
noncomputable def p4Q2PQ_originalQuarticWardResidual (B : Cfg) : ℝ :=
  g B - c B - 3 * p4Q2PQ_originalFirstActionMean H * b B

local notation "R" => p4Q2PQ_originalQuarticWardResidual H

/-- EXACT original Wilson quartic coefficient as the determinant
of the true first action profile and ONE Ward-normalized third
moment profile. No rank or fourth-coefficient nonzero hypothesis. -/
theorem p4Q2PQ_originalFourthCoefficient_eq_residualMinor
    (A B C : Cfg) :
    C4 A B C =
      ((a B - a A) * (R C - R A) -
        (a C - a A) * (R B - R A)) / 6 := by
  have hB := p4Q2PM_originalMixedMoment_difference_proportional H A B
  have hC := p4Q2PM_originalMixedMoment_difference_proportional H A C
  unfold p4Q2PP2_originalFourthCoefficient
    p4Q2PQ_originalQuarticWardResidual
    p4Q2PQ_originalFirstActionMean
  rw [hB, hC]
  ring

/-- Denominator-free version for exact cancellation and interpolation
arguments; keeps all original Wilson action moments opaque. -/
theorem p4Q2PQ_originalFourthCoefficient_six_mul
    (A B C : Cfg) :
    6 * C4 A B C =
      (a B - a A) * (R C - R A) -
        (a C - a A) * (R B - R A) := by
  rw [p4Q2PQ_originalFourthCoefficient_eq_residualMinor H A B C]
  ring

/-- The genuine original first action moment is nonconstant,
deduced from the already constructed physical -I spatial Wilson
plaquette twist (JE/IY), not assumed. -/
theorem p4Q2PQ_originalFirstMoment_nonconstant :
    ∃ A B : Cfg, a A ≠ a B := by
  obtain ⟨A, B, hAB⟩ :=
    p4Q2JE_originalWilsonZeroDerivativeProfile_nonconstant H
  refine ⟨A, B, ?_⟩
  intro heq
  apply hAB
  calc
    p4Q2JE_originalWilsonHaarZeroDerivativeProfile H A =
        a A := (p4Q2PK_originalFirstMoment_eq_trueWilsonDerivative H A).symm
    _ = a B := heq
    _ = p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B :=
      p4Q2PK_originalFirstMoment_eq_trueWilsonDerivative H B

/-- If the residual remains affine in the genuine first moment,
the FULL fourth-order Wilson coefficient vanishes for every
physical three-configuration triple. This is a genuine possible
further Ward obstruction, not excluded by PP. -/
theorem p4Q2PQ_originalFourthCoefficient_zero_of_residual_affine
    (s t : ℝ) (hAffine : ∀ X : Cfg, R X = s * a X + t)
    (A B C : Cfg) :
    C4 A B C = 0 := by
  rw [p4Q2PQ_originalFourthCoefficient_eq_residualMinor H A B C]
  rw [hAffine A, hAffine B, hAffine C]
  ring

/-- At EVERY original finite spatial SU(2) volume, the FULL genuine
fourth coefficient vanishes on every triple IF AND ONLY IF the actual
third-order Haar residual is affine in the true first Wilson profile.
The forward implication uses the already PROVED physical nonconstant
first moment. No independently postulated rank is involved. -/
theorem p4Q2PQ_allFourthCoefficients_zero_iff_residual_affine :
    (∀ A B C : Cfg, C4 A B C = 0) ↔
      ∃ s t : ℝ, ∀ X : Cfg, R X = s * a X + t := by
  constructor
  · intro hZero
    obtain ⟨A, B, hAB⟩ := p4Q2PQ_originalFirstMoment_nonconstant H
    have hDenom : a B - a A ≠ 0 := sub_ne_zero.mpr hAB.symm
    let s : ℝ := (R B - R A) / (a B - a A)
    let t : ℝ := R A - s * a A
    refine ⟨s, t, ?_⟩
    intro X
    have hDet :
        (a B - a A) * (R X - R A) -
          (a X - a A) * (R B - R A) = 0 := by
      calc
        _ = 6 * C4 A B X :=
          (p4Q2PQ_originalFourthCoefficient_six_mul H A B X).symm
        _ = 0 := by rw [hZero A B X]; ring
    have hSlope : (a B - a A) * s = R B - R A := by
      dsimp [s]
      field_simp [hDenom]
    have hFactor :
        (a B - a A) * (R X - R A - s * (a X - a A)) = 0 := by
      calc
        _ = (a B - a A) * (R X - R A) -
              (a X - a A) * ((a B - a A) * s) := by ring
        _ = (a B - a A) * (R X - R A) -
              (a X - a A) * (R B - R A) := by rw [hSlope]
        _ = 0 := hDet
    have hLinear : R X - R A - s * (a X - a A) = 0 :=
      (mul_eq_zero.mp hFactor).resolve_left hDenom
    dsimp only [t]
    linear_combination hLinear
  · rintro ⟨s, t, hAffine⟩ A B C
    exact p4Q2PQ_originalFourthCoefficient_zero_of_residual_affine
      H s t hAffine A B C

/-- Equivalent nonvanishing obstruction without imposing existence:
a nonzero ORIGINAL physical quartic coefficient is precisely a
failure of the Ward-normalized original cubic Haar residual to
lie in the affine span of the original first Wilson action moment. -/
theorem p4Q2PQ_exists_nonzeroFourthCoefficient_iff_not_affine :
    (∃ A B C : Cfg, C4 A B C ≠ 0) ↔
      ¬ ∃ s t : ℝ, ∀ X : Cfg, R X = s * a X + t := by
  rw [← p4Q2PQ_allFourthCoefficients_zero_iff_residual_affine H]
  push Not
  rfl

end OriginalWilsonQuarticWardResidual
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ_originalFourthCoefficient_eq_residualMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ_originalFourthCoefficient_six_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ_originalFirstMoment_nonconstant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ_originalFourthCoefficient_zero_of_residual_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ_allFourthCoefficients_zero_iff_residual_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ_exists_nonzeroFourthCoefficient_iff_not_affine
