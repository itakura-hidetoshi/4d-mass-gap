import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCubicTaylorRemainderV5_PP
import Mathlib.Tactic

/-!
# P4-Q2-PP2 — genuine Wilson Haar third moments and quartic determinant coefficient

Define the original one-slab and TWO-slab cubic action moments using
the same spatial Haar and complete SU(2) Wilson action as PK, PO and PJ.
The two-slab cubic moment is the original double Haar integral:
neither the full intermediate spatial Wilson action nor the temporal
crossing interaction is discarded.

The degree-three physical moment jets have a determinant whose first
possible nonzero coefficient after PM's genuine Ward cancellation
is of order four. Critically it contains a genuine third-jet cross
term in addition to PK's quadratic-jet fourth-order term.
This is an algebraic identity; the next analytic bridge must connect
the physical integrated exponential to these new cubic jets.
No nonzero coefficient or rank-three hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PP2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PP2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PP2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PP2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PP2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalThirdMomentsAndFourthCoefficient
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H

/-- The actual third Haar moment of the FULL original one-slab action,
including both spatial halfweights and temporal SU(2) crossings. -/
noncomputable def p4Q2PP2_originalOneSlabThirdActionMoment
    (B : Cfg) : ℝ :=
  -(∫ X : Cfg, (S X B) ^ 3 ∂haar)

/-- The original full two-slab action's third double-Haar moment.
The intermediate spatial Wilson energy is integrated with full weight. -/
noncomputable def p4Q2PP2_originalTwoSlabThirdActionMoment
    (B : Cfg) : ℝ :=
  -(∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 3 ∂haar ∂haar)

local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H

/-- Genuine-moment degree-three extension of PK's original one-slab jet. -/
noncomputable def p4Q2PP2_originalOneSlabFormalTaylor3
    (beta : ℝ) (B : Cfg) : ℝ :=
  p4Q2PK_originalOneSlabFormalTaylor2 H beta B +
    beta ^ 3 / 6 * c B

/-- Genuine-moment degree-three extension of PK's original two-slab jet. -/
noncomputable def p4Q2PP2_originalTwoSlabFormalTaylor3
    (beta : ℝ) (B : Cfg) : ℝ :=
  p4Q2PK_originalTwoSlabFormalTaylor2 H beta B +
    beta ^ 3 / 6 * g B

/-- The complete genuine-moment quartic coefficient; the last term
comes from linear-times-cubic multiplication and is absent from
PK's original quadratic-jet determinant. -/
noncomputable def p4Q2PP2_originalFourthCoefficient
    (A B C : Cfg) : ℝ :=
  ((b B - b A) * (d C - d A) -
    (b C - b A) * (d B - d A)) / 2 +
  ((a B - a A) * ((g C - g A) - (c C - c A)) -
    (a C - a A) * ((g B - g A) - (c B - c A))) / 6

/-- Fifth-order coefficient of the TWO genuine-moment cubic jets.
No assertion about the true analytic fifth coefficient is made. -/
noncomputable def p4Q2PP2_originalFifthJetCoefficient
    (A B C : Cfg) : ℝ :=
  ((b B - b A) * (g C - g A) -
    (b C - b A) * (g B - g A) +
    (c B - c A) * ((b C - b A) + 2 * (d C - d A)) -
    (c C - c A) * ((b B - b A) + 2 * (d B - d A))) / 12

/-- Sixth-order coefficient of the cubic jets' algebraic determinant. -/
noncomputable def p4Q2PP2_originalSixthJetCoefficient
    (A B C : Cfg) : ℝ :=
  ((c B - c A) * (g C - g A) -
    (c C - c A) * (g B - g A)) / 36

/-- Exact algebraic expansion before the ORIGINAL Ward identity.
Its degree-three factor is exactly PK's known cubic obstruction. -/
theorem p4Q2PP2_originalCubicJetMinor_fullExpansion
    (beta : ℝ) (A B C : Cfg) :
    (p4Q2PP2_originalOneSlabFormalTaylor3 H beta B -
        p4Q2PP2_originalOneSlabFormalTaylor3 H beta A) *
      (p4Q2PP2_originalTwoSlabFormalTaylor3 H beta C -
        p4Q2PP2_originalTwoSlabFormalTaylor3 H beta A) -
    (p4Q2PP2_originalOneSlabFormalTaylor3 H beta C -
        p4Q2PP2_originalOneSlabFormalTaylor3 H beta A) *
      (p4Q2PP2_originalTwoSlabFormalTaylor3 H beta B -
        p4Q2PP2_originalTwoSlabFormalTaylor3 H beta A) =
      beta ^ 3 * p4Q2PK_originalLiteralCubicObstruction H A B C +
      beta ^ 4 * p4Q2PP2_originalFourthCoefficient H A B C +
      beta ^ 5 * p4Q2PP2_originalFifthJetCoefficient H A B C +
      beta ^ 6 * p4Q2PP2_originalSixthJetCoefficient H A B C := by
  unfold p4Q2PP2_originalOneSlabFormalTaylor3
    p4Q2PP2_originalTwoSlabFormalTaylor3
    p4Q2PP2_originalFourthCoefficient
    p4Q2PP2_originalFifthJetCoefficient
    p4Q2PP2_originalSixthJetCoefficient
    p4Q2PK_originalOneSlabFormalTaylor2
    p4Q2PK_originalTwoSlabFormalTaylor2
    p4Q2PK_originalLiteralCubicObstruction
  dsimp only
  ring

/-- PM's actual SU(2) Ward cancellation eliminates the cubic term
of these genuine-moment jets; the first remaining POSSIBLE coefficient
is exactly the complete fourth coefficient defined above. -/
theorem p4Q2PP2_originalCubicJetMinor_afterWard
    (beta : ℝ) (A B C : Cfg) :
    (p4Q2PP2_originalOneSlabFormalTaylor3 H beta B -
        p4Q2PP2_originalOneSlabFormalTaylor3 H beta A) *
      (p4Q2PP2_originalTwoSlabFormalTaylor3 H beta C -
        p4Q2PP2_originalTwoSlabFormalTaylor3 H beta A) -
    (p4Q2PP2_originalOneSlabFormalTaylor3 H beta C -
        p4Q2PP2_originalOneSlabFormalTaylor3 H beta A) *
      (p4Q2PP2_originalTwoSlabFormalTaylor3 H beta B -
        p4Q2PP2_originalTwoSlabFormalTaylor3 H beta A) =
      beta ^ 4 * p4Q2PP2_originalFourthCoefficient H A B C +
      beta ^ 5 * p4Q2PP2_originalFifthJetCoefficient H A B C +
      beta ^ 6 * p4Q2PP2_originalSixthJetCoefficient H A B C := by
  rw [p4Q2PP2_originalCubicJetMinor_fullExpansion H beta A B C,
    p4Q2PM_originalLiteralCubicObstruction_zero H A B C]
  ring

end OriginalThirdMomentsAndFourthCoefficient
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP2_originalCubicJetMinor_fullExpansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP2_originalCubicJetMinor_afterWard
