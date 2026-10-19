import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoContextSpatialGIMinorNonzeroV5_LM
import Mathlib.Tactic

/-!
# P4-Q2-LN — explicit finite-volume coercivity of the TRUE physical GI two-source detector

For every finite original Wilson spatial lattice H and every b>0, LM supplies
two genuine interacting-posterior GI boundary contexts whose ORIGINAL
spatial Wilson 2×2 determinant is nonzero.

We use the exact physical Gauss-law sources U and W_H U (JU), and their
literal original signed two-interacting-Wilson-posterior GI response (GI).
JH identifies those responses with the original bounded Haar-L²
functionals. The 2×2 adjugate/Cauchy identity supplies an EXPLICIT strictly
positive finite-volume detector coercivity coefficient:

  κ = (original spatial GI minor)^2 / (sum of squares of all four
      TRUE original GI detector matrix entries).

For EVERY real coefficient pair (x,y), the sum of squares of the two
genuine GI responses on the physical source x U + y (W_H U) dominates
κ (x²+y²). This does not impose an artificial rank assumption: LM
proves the determinant witness. Nor is it a volume-uniform estimate:
the witnessing contexts and all four matrix entries may depend on H.
The next genuine obstruction is to control this κ uniformly in H.
No fake independent-Haar posterior, Dobrushin, sorry/admit/new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Elementary adjugate/Cauchy identity for a REAL 2×2 matrix, proved
without any external finite-dimensional rank or spectral assumption. -/
theorem p4Q2LN_twoRowDetFrobenius_bound
    (a q c d x y : ℝ) :
    (a * d - q * c)^2 * (x^2 + y^2) ≤
      (a^2 + q^2 + c^2 + d^2) *
        ((a * x + q * y)^2 + (c * x + d * y)^2) := by
  let X : ℝ := a * x + q * y
  let Y : ℝ := c * x + d * y
  have hxId :
      (d * X - q * Y)^2 + (q * X + d * Y)^2 =
        (d^2 + q^2) * (X^2 + Y^2) := by ring
  have hyId :
      (a * Y - c * X)^2 + (a * X + c * Y)^2 =
        (a^2 + c^2) * (X^2 + Y^2) := by ring
  have hx :
      (d * X - q * Y)^2 ≤ (d^2 + q^2) * (X^2 + Y^2) := by
    nlinarith [hxId, sq_nonneg (q * X + d * Y)]
  have hy :
      (a * Y - c * X)^2 ≤ (a^2 + c^2) * (X^2 + Y^2) := by
    nlinarith [hyId, sq_nonneg (a * X + c * Y)]
  calc
    (a * d - q * c)^2 * (x^2 + y^2) =
        (d * X - q * Y)^2 + (a * Y - c * X)^2 := by
          dsimp [X, Y]
          ring
    _ ≤ (d^2 + q^2) * (X^2 + Y^2) +
        (a^2 + c^2) * (X^2 + Y^2) := add_le_add hx hy
    _ = (a^2 + q^2 + c^2 + d^2) *
          ((a * x + q * y)^2 + (c * x + d * y)^2) := by
          dsimp [X, Y]
          ring

/-- The exact determinant-squared / Frobenius-squared lower bound:
it is strictly positive for each *proved* nonzero real determinant. -/
theorem p4Q2LN_twoRowFrobenius_coercive
    (a q c d : ℝ) (hdet : a * d - q * c ≠ 0) :
    0 < (a * d - q * c)^2 / (a^2 + q^2 + c^2 + d^2) ∧
      ∀ x y : ℝ,
        ((a * d - q * c)^2 / (a^2 + q^2 + c^2 + d^2)) *
            (x^2 + y^2) ≤
          (a * x + q * y)^2 + (c * x + d * y)^2 := by
  have htrial :
      (a * d - q * c)^2 ≤
        (a^2 + q^2 + c^2 + d^2) * (a^2 + c^2) := by
    convert p4Q2LN_twoRowDetFrobenius_bound a q c d 1 0 using 1 <;> ring
  have hden : 0 < a^2 + q^2 + c^2 + d^2 := by
    by_contra hn
    have hle : a^2 + q^2 + c^2 + d^2 ≤ 0 := le_of_not_gt hn
    have hprod : (a^2 + q^2 + c^2 + d^2) * (a^2 + c^2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (by positivity)
    have hpositive : 0 < (a * d - q * c)^2 := sq_pos_of_ne_zero hdet
    linarith
  constructor
  · exact div_pos (sq_pos_of_ne_zero hdet) hden
  · intro x y
    have hbound := p4Q2LN_twoRowDetFrobenius_bound a q c d x y
    calc
      ((a * d - q * c)^2 / (a^2 + q^2 + c^2 + d^2)) *
          (x^2 + y^2) =
        ((a * d - q * c)^2 * (x^2 + y^2)) /
          (a^2 + q^2 + c^2 + d^2) := by ring
      _ ≤ (a * x + q * y)^2 + (c * x + d * y)^2 :=
        (div_le_iff₀ hden).2 (by
          calc
            (a * d - q * c)^2 * (x^2 + y^2) ≤
                (a^2 + q^2 + c^2 + d^2) *
                  ((a * x + q * y)^2 + (c * x + d * y)^2) := hbound
            _ = ((a * x + q * y)^2 + (c * x + d * y)^2) *
                  (a^2 + q^2 + c^2 + d^2) := by ring)

end GroundStatePosteriorJoint

local instance p4Q2LN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "W" => p4Q2JU_originalSpatialWilsonPhysicalSource H
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "G" => p4Q2JH_originalGIResponseCLM H

/-- Literal original Gauss-law physical Hilbert source spanned by
the constant unit and the actual spatial Wilson multiplication source. -/
noncomputable def p4Q2LN_originalPhysicalTwoSource
    (x y : ℝ) : Phys := x • U + y • W

theorem p4Q2LN_originalPhysicalTwoSource_coe_eq
    (x y : ℝ) :
    ((p4Q2LN_originalPhysicalTwoSource H x y : Phys) : Lp ℝ 2 haar) =
      x • L (1 : C(Cfg, ℝ)) +
        y • L (p4Q2JI_actualSpatialWilsonContinuous H) := by
  change ((x • U + y • W : Phys) : Lp ℝ 2 haar) = _
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp,
    p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp]

/-- EXACT physical source response under the TWO true interacting
Wilson posterior laws: no replacement by independent Haar. -/
theorem p4Q2LN_originalPhysicalTwoSource_GI_eq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (x y : ℝ) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb (p4Q2LN_originalPhysicalTwoSource H x y) e z =
      x * G b hb e z (L (1 : C(Cfg, ℝ))) +
        y * G b hb e z (L (p4Q2JI_actualSpatialWilsonContinuous H)) := by
  let F : C(Cfg, ℝ) :=
    x • (1 : C(Cfg, ℝ)) + y • p4Q2JI_actualSpatialWilsonContinuous H
  have hF :
      L F =
        x • L (1 : C(Cfg, ℝ)) +
          y • L (p4Q2JI_actualSpatialWilsonContinuous H) := by
    dsimp [F]
    rw [map_add, map_smul, map_smul]
  have hCoe :
      ((p4Q2LN_originalPhysicalTwoSource H x y : Phys) : Lp ℝ 2 haar) =
        L F := by
    rw [p4Q2LN_originalPhysicalTwoSource_coe_eq, ← hF]
  have hRep :
      (fun A : Cfg =>
        ((p4Q2LN_originalPhysicalTwoSource H x y : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar]
          F := by
    rw [hCoe]
    exact F.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have h :=
    p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
      H b hb e z (p4Q2LN_originalPhysicalTwoSource H x y) F hRep
  rw [hCoe, hF, map_add, map_smul, map_smul] at h
  simpa only [smul_eq_mul] using h.symm

/-- Both ORIGINAL GI response channels of one real physical source. -/
noncomputable def p4Q2LN_originalPhysicalTwoSourceGIPair
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (x y : ℝ) : ℝ × ℝ :=
  (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb (p4Q2LN_originalPhysicalTwoSource H x y) e z,
   p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb (p4Q2LN_originalPhysicalTwoSource H x y) e' z')

theorem p4Q2LN_originalPhysicalTwoSourceGIPair_eq
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (x y : ℝ) :
    p4Q2LN_originalPhysicalTwoSourceGIPair H b hb e e' z z' x y =
      (x * G b hb e z (L (1 : C(Cfg, ℝ))) +
          y * G b hb e z (L (p4Q2JI_actualSpatialWilsonContinuous H)),
       x * G b hb e' z' (L (1 : C(Cfg, ℝ))) +
          y * G b hb e' z' (L (p4Q2JI_actualSpatialWilsonContinuous H))) := by
  unfold p4Q2LN_originalPhysicalTwoSourceGIPair
  rw [p4Q2LN_originalPhysicalTwoSource_GI_eq H b hb e z x y,
    p4Q2LN_originalPhysicalTwoSource_GI_eq H b hb e' z' x y]

/-- Explicit norm squared of the four ACTUAL original GI matrix entries. -/
noncomputable def p4Q2LN_originalGIFrobeniusSq
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) : ℝ :=
  (G b hb e z (L (1 : C(Cfg, ℝ))))^2 +
  (G b hb e z (L (p4Q2JI_actualSpatialWilsonContinuous H)))^2 +
  (G b hb e' z' (L (1 : C(Cfg, ℝ))))^2 +
  (G b hb e' z' (L (p4Q2JI_actualSpatialWilsonContinuous H)))^2

/-- Exact finite-H detector constant, with an authentic original Wilson
GI determinant numerator and true (not independently sampled) denominator. -/
noncomputable def p4Q2LN_originalGIQuantitativeCoefficient
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) : ℝ :=
  (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
    p4Q2LN_originalGIFrobeniusSq H b hb e e' z z'

/-- A NONZERO true Wilson two-context minor gives a strictly positive
EXPLICIT coercivity coefficient for the physical two-source detector.
This is for EVERY coefficient x,y and is stronger than rank-two alone. -/
theorem p4Q2LN_originalPhysicalTwoSourceGI_explicit_coercive
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg)
    (hminor : p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' ≠ 0) :
    0 < p4Q2LN_originalGIQuantitativeCoefficient H b hb e e' z z' ∧
      ∀ x y : ℝ,
        p4Q2LN_originalGIQuantitativeCoefficient H b hb e e' z z' *
            (x^2 + y^2) ≤
          (p4Q2LN_originalPhysicalTwoSourceGIPair H b hb e e' z z' x y).1^2 +
          (p4Q2LN_originalPhysicalTwoSourceGIPair H b hb e e' z z' x y).2^2 := by
  let a : ℝ := G b hb e z (L (1 : C(Cfg, ℝ)))
  let q : ℝ := G b hb e z (L (p4Q2JI_actualSpatialWilsonContinuous H))
  let c : ℝ := G b hb e' z' (L (1 : C(Cfg, ℝ)))
  let d : ℝ := G b hb e' z' (L (p4Q2JI_actualSpatialWilsonContinuous H))
  have hdet : a * d - q * c ≠ 0 := by
    change a * d - q * c ≠ 0 at hminor
    exact hminor
  have h := p4Q2LN_twoRowFrobenius_coercive a q c d hdet
  constructor
  · change 0 < (a * d - q * c)^2 / (a^2 + q^2 + c^2 + d^2)
    exact h.1
  · intro x y
    rw [p4Q2LN_originalPhysicalTwoSourceGIPair_eq]
    change ((a * d - q * c)^2 / (a^2 + q^2 + c^2 + d^2)) *
      (x^2 + y^2) ≤
        (x * a + y * q)^2 + (x * c + y * d)^2
    convert h.2 x y using 1 <;> ring

/-- LM makes quantitative finite-volume GI detector nondegeneracy
unconditional at every positive original Wilson coupling and all actual
links, with truly existing full boundary contexts. NO uniform-in-H floor. -/
theorem p4Q2LN_originalPhysicalTwoSourceGI_exists_coercive
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ κ : ℝ,
      0 < κ ∧
      ∀ x y : ℝ,
        κ * (x^2 + y^2) ≤
          (p4Q2LN_originalPhysicalTwoSourceGIPair
            H b hb.le e e' z z' x y).1^2 +
          (p4Q2LN_originalPhysicalTwoSourceGIPair
            H b hb.le e e' z z' x y).2^2 := by
  obtain ⟨z, z', hminor⟩ :=
    p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
      H b hb e e' left₀ right₀
  obtain ⟨hκ, hbound⟩ :=
    p4Q2LN_originalPhysicalTwoSourceGI_explicit_coercive
      H b hb.le e e' z z' hminor
  exact ⟨z, z',
    p4Q2LN_originalGIQuantitativeCoefficient H b hb.le e e' z z',
    hκ, hbound⟩

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LN_twoRowDetFrobenius_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LN_twoRowFrobenius_coercive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LN_originalPhysicalTwoSource_coe_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LN_originalPhysicalTwoSource_GI_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LN_originalPhysicalTwoSourceGIPair_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LN_originalPhysicalTwoSourceGI_explicit_coercive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LN_originalPhysicalTwoSourceGI_exists_coercive