import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRawTwoSlabLiteralKernelV5_PJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonUniformQuadraticRemainderV5_JF
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# P4-Q2-PK — first exact fine-coupling jets of the ORIGINAL Wilson two-slab kernel

We keep the original finite-volume SU(2) Gauss-law transfer, its genuine
spatial product-Haar measure, the full spatial Wilson plaquette action W
and the original temporal plaquette crossing action C.

The two-slab exponent contains (W(X)/2 + W(A) + W(B)/2), rather than a
halfweight on the intermediate configuration A. This is an exact identity
of the unchanged physical one-slab Boltzmann kernels.

The genuine Haar action moments below give a FORMAL order-two jet for
the one-slab and two-slab kernel integrals. Their three-boundary minor
has its naive order-two term identically cancelled. Its first POSSIBLE
term has order three and is a determinant of the actual one-slab action
mean against the genuinely Haar-integrated mixed original action moment.
No coefficient is assumed nonzero. The jets are not yet identified with
an order-three remainder theorem for the exact integrated two-slab kernel;
that analytic and harmonic-analysis bridge remains open.

No independent posterior, Dobrushin hypothesis, fabricated third-mode
witness, artificial spectral measure, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section TrueTwoSlabActionAndTaylorJets
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2

/-- The literal complete original Wilson action of two consecutive slabs.
The intermediate boundary is integrated only after both kernels are
multiplied; its spatial Wilson action consequently has full weight. -/
noncomputable def p4Q2PK_originalTwoSlabAction (X A B : Cfg) : ℝ :=
  S X A + S A B

/-- No independent posterior or reweighting: both half-actions on the
genuine intermediate SU(2) configuration add up to one FULL W(A). -/
theorem p4Q2PK_originalTwoSlabAction_split (X A B : Cfg) :
    p4Q2PK_originalTwoSlabAction H X A B =
      (1 / 2 : ℝ) * W X + W A + (1 / 2 : ℝ) * W B +
        Cross X A + Cross A B := by
  unfold p4Q2PK_originalTwoSlabAction
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  ring

/-- The genuine two consecutive original Wilson kernels, with the
precisely correct order of all physical boundary variables. -/
theorem p4Q2PK_originalTwoSlabKernel_product_eq_exp
    (beta : ℝ) (X A B : Cfg) :
    K beta A B * K beta X A =
      Real.exp (-(beta * p4Q2PK_originalTwoSlabAction H X A B)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    ← Real.exp_add]
  congr 1
  unfold p4Q2PK_originalTwoSlabAction
  ring

/-- The complete two-slab physical Wilson action is nonnegative.
This is the correct bounded finite-volume action for Taylor estimates. -/
theorem p4Q2PK_originalTwoSlabAction_nonneg (X A B : Cfg) :
    0 ≤ p4Q2PK_originalTwoSlabAction H X A B := by
  unfold p4Q2PK_originalTwoSlabAction
  exact add_nonneg
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by decide) X A)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by decide) A B)

/-- The first fine-coupling derivative of the ACTUAL two-slab Wilson
kernel product (before Haar integration), not a substitute model.
It uses exactly the full two-slab action above. -/
theorem p4Q2PK_originalTwoSlabKernel_hasDerivAt_zero
    (X A B : Cfg) :
    HasDerivAt (fun beta : ℝ => K beta A B * K beta X A)
      (-p4Q2PK_originalTwoSlabAction H X A B) 0 := by
  let q : ℝ := p4Q2PK_originalTwoSlabAction H X A B
  have hlin : HasDerivAt (fun beta : ℝ => beta * (-q)) (-q) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (-q)
  have hexp : HasDerivAt
      (fun beta : ℝ => Real.exp (-(beta * q))) (-q) 0 := by
    simpa only [mul_neg, zero_mul, neg_zero, Real.exp_zero, one_mul] using hlin.exp
  have hfun :
      (fun beta : ℝ => K beta A B * K beta X A) =
      (fun beta : ℝ => Real.exp (-(beta * q))) := by
    funext beta
    exact p4Q2PK_originalTwoSlabKernel_product_eq_exp H beta X A B
  rw [hfun]
  exact hexp

/-- Genuine Haar-integrated first one-slab Wilson action coefficient. -/
noncomputable def p4Q2PK_originalOneSlabFirstActionMoment (B : Cfg) : ℝ :=
  -(∫ X : Cfg, S X B ∂haar)

/-- Genuine Haar-integrated second one-slab action coefficient, BEFORE
division by 2 in the exponential Taylor series. -/
noncomputable def p4Q2PK_originalOneSlabSecondActionMoment (B : Cfg) : ℝ :=
  ∫ X : Cfg, (S X B) ^ 2 ∂haar

/-- The nontrivial mixed action moment that controls the first POSSIBLE
independent spatial variation of the actual two-step Taylor jet. -/
noncomputable def p4Q2PK_originalMixedTwoSlabActionMoment (B : Cfg) : ℝ :=
  -(∫ A : Cfg,
      S A B * p4Q2PK_originalOneSlabFirstActionMoment H A ∂haar)

/-- The first moment equals JE/JF's already PROVED authentic physical
one-slab strong-derivative spatial profile; there is no surrogate source. -/
theorem p4Q2PK_originalFirstMoment_eq_trueWilsonDerivative (B : Cfg) :
    p4Q2PK_originalOneSlabFirstActionMoment H B =
      p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B := by
  simpa only [p4Q2PK_originalOneSlabFirstActionMoment] using
    (p4Q2JF_originalWilsonZeroDerivativeProfile_eq_neg_actionHaarMean H B).symm

/-- Algebraic second-order Taylor jet using ACTUAL original one-slab
spatial SU(2) Haar moments, not a hypothetical independent function. -/
noncomputable def p4Q2PK_originalOneSlabFormalTaylor2
    (beta : ℝ) (B : Cfg) : ℝ :=
  1 + beta * p4Q2PK_originalOneSlabFirstActionMoment H B +
    beta ^ 2 / 2 * p4Q2PK_originalOneSlabSecondActionMoment H B

/-- Algebraic second-order Taylor jet prescribed by the double-Haar
original two-slab kernel. The mixed term has its unchanged original
temporal crossing interaction, and the other two second moments are
literal left-Haar integrals. Identification with derivatives of the
integrated physical two-slab function is reserved for the next stage. -/
noncomputable def p4Q2PK_originalTwoSlabFormalTaylor2
    (beta : ℝ) (B : Cfg) : ℝ :=
  let a := p4Q2PK_originalOneSlabFirstActionMoment H
  let b := p4Q2PK_originalOneSlabSecondActionMoment H
  let d := p4Q2PK_originalMixedTwoSlabActionMoment H
  1 + beta * (a B + ∫ A : Cfg, a A ∂haar) +
    beta ^ 2 / 2 *
      (b B + (∫ A : Cfg, b A ∂haar) + 2 * d B)

/-- Candidate cubic coefficient of the THREE-BOUNDARY Wilson fine
minor, expressed in terms of ACTUAL full one-slab action integrals. -/
noncomputable def p4Q2PK_originalLiteralCubicObstruction
    (A B C : Cfg) : ℝ :=
  let a := p4Q2PK_originalOneSlabFirstActionMoment H
  let d := p4Q2PK_originalMixedTwoSlabActionMoment H
  (a B - a A) * (d C - d A) -
    (a C - a A) * (d B - d A)

/-- The first two powers CANCEL exactly in the three-boundary
minor formed from the original action-moment formal jets. The first
POSSIBLE nonzero coefficient is cubic, and the quartic coefficient
is explicitly the second one-slab moment against the mixed moment.
Neither coefficient is asserted nonzero or sufficient for the
unexpanded original physical literal three-point determinant. -/
theorem p4Q2PK_originalWilsonFormalTaylorMinor_factor
    (beta : ℝ) (A B C : Cfg) :
    (p4Q2PK_originalOneSlabFormalTaylor2 H beta B -
        p4Q2PK_originalOneSlabFormalTaylor2 H beta A) *
      (p4Q2PK_originalTwoSlabFormalTaylor2 H beta C -
        p4Q2PK_originalTwoSlabFormalTaylor2 H beta A) -
    (p4Q2PK_originalOneSlabFormalTaylor2 H beta C -
        p4Q2PK_originalOneSlabFormalTaylor2 H beta A) *
      (p4Q2PK_originalTwoSlabFormalTaylor2 H beta B -
        p4Q2PK_originalTwoSlabFormalTaylor2 H beta A) =
    beta ^ 3 * p4Q2PK_originalLiteralCubicObstruction H A B C +
      beta ^ 4 / 2 *
      ((p4Q2PK_originalOneSlabSecondActionMoment H B -
          p4Q2PK_originalOneSlabSecondActionMoment H A) *
        (p4Q2PK_originalMixedTwoSlabActionMoment H C -
          p4Q2PK_originalMixedTwoSlabActionMoment H A) -
      (p4Q2PK_originalOneSlabSecondActionMoment H C -
          p4Q2PK_originalOneSlabSecondActionMoment H A) *
        (p4Q2PK_originalMixedTwoSlabActionMoment H B -
          p4Q2PK_originalMixedTwoSlabActionMoment H A)) := by
  unfold p4Q2PK_originalOneSlabFormalTaylor2
    p4Q2PK_originalTwoSlabFormalTaylor2
    p4Q2PK_originalLiteralCubicObstruction
  dsimp only
  ring

/-- If a subsequent physical Haar lemma proves that the mixed action
moment is affine in the true first variation, the cubic coefficient
is forced to vanish. We do NOT assume that relation for the real
Wilson kernel; this theorem identifies its exact obstruction. -/
theorem p4Q2PK_originalLiteralCubicObstruction_vanishes_of_affine
    (A B C : Cfg) (s c : ℝ)
    (ha : ∀ X : Cfg,
      p4Q2PK_originalMixedTwoSlabActionMoment H X =
        s * p4Q2PK_originalOneSlabFirstActionMoment H X + c) :
    p4Q2PK_originalLiteralCubicObstruction H A B C = 0 := by
  unfold p4Q2PK_originalLiteralCubicObstruction
  dsimp only
  rw [ha A, ha B, ha C]
  ring

end TrueTwoSlabActionAndTaylorJets
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabAction_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabKernel_product_eq_exp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabAction_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabKernel_hasDerivAt_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalFirstMoment_eq_trueWilsonDerivative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalWilsonFormalTaylorMinor_factor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalLiteralCubicObstruction_vanishes_of_affine
