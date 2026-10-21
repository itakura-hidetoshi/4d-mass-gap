import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTemporalSU2CharacterScoreObstructionV5_NG
import Mathlib.Tactic

/-!
# P4-Q2-NH — original SU(2) fundamental 2x2 matrix-moment determinant

NG gave the exact temporal SU(2) character transform of the original
two-interacting-Wilson-posterior signed receiver.  NH expands that genuine
character into the two diagonal matrix coefficients of the *actual*
fundamental 2x2 SU(2) representation, and gives an exact scalar
2x2 determinant obstruction.

For y=z.right(e), with rho the SAME original right-spatial Wilson
factor times inverse Perron joint half-density times signed contrast
of the SAME TWO interacting Wilson posterior densities, write

  m(x,g) = Re[(x⁻¹g)₀₀ + (x⁻¹g)₁₁]/2,
  M(x)   = ∫ exp(b m(x,g)) rho(g) dHaar(g),
  E(x)   = exp(b m(x,y)),
  Delta(x) = M(x) E(1) - M(1) E(x).

No new posterior, source, detector, rank postulate or independent-Haar
replacement is introduced.  The ORIGINAL SU(2) right-spatial Wilson
factor, two Wilson posterior rows and Perron half-density remain intact.

NH proves Delta(x) = E(1) (M(x)-E(x) Psi(1)).
Because E(1)>0, the genuine Haar variance Q is strictly positive
IFF at least ONE actual SU(2) fundamental-matrix-moment determinant
Delta(x) is NONZERO.  At b>0, rho itself has both strictly positive
and strictly negative genuine values; that is NOT a proof that Delta
is nonzero.  Universal nonvanishing of Delta, GI covariance, H1-C3 and
the continuum mass gap remain OPEN.

All arguments use pinned Lean/mathlib. No sorry, new axiom or Dobrushin.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- Real normalized sum of the TWO actual diagonal coefficients of the
SU(2) fundamental two-dimensional unitary matrix x⁻¹g. -/
noncomputable def p4Q2NH_originalSU2FundamentalDiagonalCoefficient
    (x g : Gauge) : ℝ :=
  (((((x⁻¹ * g : Gauge) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
    ((((x⁻¹ * g : Gauge) : Matrix (Fin 2) (Fin 2) ℂ) 1 1))).re / 2

/-- The exact Wilson SU(2) temporal character is the sum of the TWO
fundamental matrix diagonal coefficients, not a formal character symbol. -/
theorem p4Q2NH_originalSU2Character_eq_fundamentalDiagonalCoefficient
    (x g : Gauge) :
    p4Q2NG_originalSU2TemporalCharacter x g =
      p4Q2NH_originalSU2FundamentalDiagonalCoefficient x g := by
  rw [p4Q2NG_originalSU2TemporalCharacter_eq_trace]
  simp only [p4Q2NH_originalSU2FundamentalDiagonalCoefficient,
    Matrix.trace_fin_two]

section OriginalFundamentalMatrixMoment
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "rho" => p4Q2NG_originalSpatialPerronSignedContrast H b hb
local notation "T" => p4Q2NG_originalTemporalSU2CharacterMoment H b hb
local notation "q" => p4Q2NC_originalSignedReceiverLinkScore H b hb
local notation "Q" => p4Q2NC_originalSignedReceiverLinkHaarVariance H b hb
include hb

/-- The ORIGINAL Wilson–Perron signed moment evaluated against
the two fundamental SU(2) diagonal matrix coefficients. -/
noncomputable def p4Q2NH_originalFundamentalDiagonalSignedMoment
    (e : Link) (z : Cfg × Cfg) (x : Gauge) : ℝ :=
  ∫ g : Gauge,
    Real.exp (b * p4Q2NH_originalSU2FundamentalDiagonalCoefficient x g) *
      rho e z g ∂mu

local notation "M" => p4Q2NH_originalFundamentalDiagonalSignedMoment H b hb

/-- The matrix-entry moment is EXACTLY NG's true original temporal
Wilson character moment; neither its coefficient nor Haar law changed. -/
theorem p4Q2NH_originalFundamentalDiagonalSignedMoment_eq_characterMoment
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    M e z x = T e z x := by
  unfold p4Q2NH_originalFundamentalDiagonalSignedMoment
    p4Q2NG_originalTemporalSU2CharacterMoment
  apply integral_congr_ae
  filter_upwards with g
  rw [p4Q2NH_originalSU2Character_eq_fundamentalDiagonalCoefficient x g]

/-- The true boundary temporal factor, expressed in the same actual
fundamental SU(2) 2x2 representation. -/
noncomputable def p4Q2NH_originalBoundaryDiagonalFactor
    (b : ℝ) (x y : Gauge) : ℝ :=
  Real.exp (b * p4Q2NH_originalSU2FundamentalDiagonalCoefficient x y)

local notation "E" => p4Q2NH_originalBoundaryDiagonalFactor b

theorem p4Q2NH_originalBoundaryDiagonalFactor_eq_character
    (x y : Gauge) :
    E x y = Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x y) := by
  simp only [p4Q2NH_originalBoundaryDiagonalFactor,
    p4Q2NH_originalSU2Character_eq_fundamentalDiagonalCoefficient]

theorem p4Q2NH_originalBoundaryDiagonalFactor_pos
    (x y : Gauge) : 0 < E x y :=
  Real.exp_pos _

/-- An explicit real 2x2 determinant of two rows of *genuine*
SU(2) fundamental-matrix-coefficient Wilson–Perron moments.
Its first column is M(x), M(1); its second E(x), E(1). -/
noncomputable def p4Q2NH_originalFundamentalMomentDeterminant
    (e : Link) (z : Cfg × Cfg) (x : Gauge) : ℝ :=
  M e z x * E 1 (z.2 e) -
    M e z 1 * E x (z.2 e)

local notation "Delta" => p4Q2NH_originalFundamentalMomentDeterminant H b hb

/-- The fundamental-matrix-moment determinant measures the exact
failure of NG's true character-moment proportionality. -/
theorem p4Q2NH_originalFundamentalMomentDeterminant_eq_signedScoreDefect
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    Delta e z x =
      Real.exp (b * p4Q2NG_originalSU2TemporalCharacter 1 (z.2 e)) *
        (T e z x -
          Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x (z.2 e)) *
            q e z 1) := by
  unfold p4Q2NH_originalFundamentalMomentDeterminant
  rw [p4Q2NH_originalFundamentalDiagonalSignedMoment_eq_characterMoment
        H b hb e z x,
      p4Q2NH_originalFundamentalDiagonalSignedMoment_eq_characterMoment
        H b hb e z 1,
      p4Q2NH_originalBoundaryDiagonalFactor_eq_character b 1 (z.2 e),
      p4Q2NH_originalBoundaryDiagonalFactor_eq_character b x (z.2 e),
      p4Q2NG_originalCharacterMoment_eq_exp_mul_signedScore
        H b hb e z 1]
  ring

/-- Equivalently, the determinant is a strictly positive temporal
matrix-factor multiple of the difference of the TWO authentic scores. -/
theorem p4Q2NH_originalFundamentalMomentDeterminant_eq_scoreDifference
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    Delta e z x =
      E 1 (z.2 e) * E x (z.2 e) * (q e z x - q e z 1) := by
  rw [p4Q2NH_originalFundamentalMomentDeterminant_eq_signedScoreDefect
    H b hb e z x]
  rw [← p4Q2NH_originalBoundaryDiagonalFactor_eq_character b 1 (z.2 e),
      ← p4Q2NH_originalBoundaryDiagonalFactor_eq_character b x (z.2 e),
      p4Q2NG_originalCharacterMoment_eq_exp_mul_signedScore H b hb e z x]
  ring

/-- The determinant obstruction vanishes at the normalization
source x=1; a useful nontrivial witness must probe other source links. -/
theorem p4Q2NH_originalFundamentalMomentDeterminant_one_zero
    (e : Link) (z : Cfg × Cfg) :
    Delta e z 1 = 0 := by
  unfold p4Q2NH_originalFundamentalMomentDeterminant
  ring

/-- For any true SU(2) source x, a NONZERO fundamental-matrix-moment
determinant is equivalent to violating the exact original character
proportionality relation.  No nonzero determinant is postulated. -/
theorem p4Q2NH_originalFundamentalMomentDeterminant_ne_zero_iff
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    Delta e z x ≠ 0 ↔
      T e z x ≠
        Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x (z.2 e)) *
          q e z 1 := by
  have hZero :
      Delta e z x = 0 ↔
        T e z x =
          Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x (z.2 e)) *
            q e z 1 := by
    rw [p4Q2NH_originalFundamentalMomentDeterminant_eq_signedScoreDefect
      H b hb e z x]
    constructor
    · intro h
      have hz :=
        (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
      exact sub_eq_zero.mp hz
    · intro h
      rw [h, sub_self, mul_zero]
  exact not_congr hZero

/-- NH's finite-dimensional necessary-and-sufficient obstruction:
the TRUE original Wilson signed receiver's Haar variance is positive
iff ONE concrete 2x2 determinant of real SU(2) fundamental matrix
coefficient moments is nonzero.  The existential is a mathematical
witness criterion, NOT an unproved positivity claim. -/
theorem p4Q2NH_originalSignedReceiverHaarVariance_pos_iff_matrixDetWitness
    (e : Link) (z : Cfg × Cfg) :
    0 < Q e z ↔ ∃ x : Gauge, Delta e z x ≠ 0 := by
  constructor
  · intro hPos
    obtain ⟨x, hx⟩ :=
      (p4Q2NG_originalSignedScoreHaarVariance_pos_iff_characterMoment_witness
        H b hb e z).mp hPos
    exact ⟨x,
      (p4Q2NH_originalFundamentalMomentDeterminant_ne_zero_iff
        H b hb e z x).2 hx⟩
  · rintro ⟨x, hx⟩
    apply (p4Q2NG_originalSignedScoreHaarVariance_pos_iff_characterMoment_witness
      H b hb e z).2
    exact ⟨x,
      (p4Q2NH_originalFundamentalMomentDeterminant_ne_zero_iff
        H b hb e z x).1 hx⟩

/-- True SU(2) signed posterior coefficient rho has both signs at
each b>0: the original right-spatial Boltzmann and inverse Perron
factors are strictly positive and cannot alter its sign.  This is
not a proof that the integrated determinant is nonzero. -/
theorem p4Q2NH_originalSpatialPerronSignedContrast_has_both_signs
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) :
    (∃ g : Gauge, 0 < rho e z g) ∧
      (∃ g : Gauge, rho e z g < 0) := by
  obtain ⟨⟨g,hg⟩, ⟨h,hh⟩⟩ :=
    p4Q2ND_originalPosteriorContrast_has_both_signs
      H b hb bpos z.2 e
  have hs (u : Gauge) :
      0 < p4Q2NG_originalRightSpatialWilsonFactor H b z.2 e u :=
    Real.exp_pos _
  have hp (u : Gauge) :
      0 < (continuousJointSqrtDensity H 2 (by norm_num) b hb
        (z.1, Function.update z.2 e u))⁻¹ := by
    exact inv_pos.mpr
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
        (z.1, Function.update z.2 e u))
  constructor
  · refine ⟨g, ?_⟩
    unfold p4Q2NG_originalSpatialPerronSignedContrast
    exact mul_pos (hs g) (mul_pos (hp g) hg)
  · refine ⟨h, ?_⟩
    unfold p4Q2NG_originalSpatialPerronSignedContrast
    exact mul_neg_of_pos_of_neg (hs h)
      (mul_neg_of_pos_of_neg (hp h) hh)

end OriginalFundamentalMatrixMoment
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalSU2Character_eq_fundamentalDiagonalCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalFundamentalDiagonalSignedMoment_eq_characterMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalBoundaryDiagonalFactor_eq_character
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalBoundaryDiagonalFactor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalFundamentalMomentDeterminant_eq_signedScoreDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalFundamentalMomentDeterminant_eq_scoreDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalFundamentalMomentDeterminant_one_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalFundamentalMomentDeterminant_ne_zero_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalSignedReceiverHaarVariance_pos_iff_matrixDetWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NH_originalSpatialPerronSignedContrast_has_both_signs
