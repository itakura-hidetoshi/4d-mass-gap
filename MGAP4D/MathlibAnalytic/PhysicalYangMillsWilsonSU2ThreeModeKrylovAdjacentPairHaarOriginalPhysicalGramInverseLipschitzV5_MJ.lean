import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalGramInverseV5_MI
import Mathlib.Tactic

/-!
# P4-Q2-MJ — true original Wilson physical Gram inverse is linear and stable

MI established constructive bijectivity of the REAL two-coordinate Gram
of the original physical SU(2) Wilson signed-posterior response at true
finite-H interacting-Wilson contexts. It also established a squared
inverse bound for each individual right-hand side (s,t).

MJ now packages the unique inverse into an explicit fixed-context
coefficient-reconstruction function on REAL dual observations, proves
the same TRUE Gram equations for every input, and proves that this
inverse is additive, homogeneous, and quantitatively stable under
arbitrary changes of the observation pair:

  Inv(s₁-s₂,t₁-t₂) = Inv(s₁,t₁)-Inv(s₂,t₂),
  k² ||Inv(s₁,t₁)-Inv(s₂,t₂)||²
     <= (s₁-s₂)²+(t₁-t₂)²,

where k = (Q_original/N_H)/(10 E_b²) > 0 for authentic finite-H
interacting-Wilson witness contexts. The Lipschitz bound is derived
from MI's ALREADY VERIFIED inverse stability and the UNIQUE
reconstruction from the SAME original physical response Gram, not
from a newly postulated detector, rank, or inverse operator.

The physical underlying original p-indexed Gauss-law source remains
x U + y W_{H,p} U and the Gram entries are unchanged original Wilson
spatial signed posterior expectation-gap squares. No artificial
physical source, independent Haar replacement or Dobrushin input.

This is a finite-volume inverse of the original SPATIAL Gram, not an
endpoint physical transfer inverse, not an H-uniform Lipschitz
constant, not H1-C3, and not a continuum mass-gap theorem.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "A" => p4Q2MG_originalPhysicalGramUU H b hb
local notation "B" => p4Q2MG_originalPhysicalGramUW H b hb
local notation "C" => p4Q2MG_originalPhysicalGramWW H b hb

/-- Explicit canonical coefficient recovery from the ORIGINAL physical
Wilson spatial two-source Gram, without changing the response law. -/
noncomputable def p4Q2MJ_originalPhysicalGramInverseCoefficients
    (e e' : Link) (z z' : Cfg × Cfg) (s t : ℝ) : ℝ × ℝ :=
  ⟨(C e e' z z' * s - B e e' z z' * t) /
      (A e e' z z' * C e e' z z' - (B e e' z z')^2),
    (A e e' z z' * t - B e e' z z' * s) /
      (A e e' z z' * C e e' z z' - (B e e' z z')^2)⟩

local notation "Inv" =>
  p4Q2MJ_originalPhysicalGramInverseCoefficients H b hb

/-- The explicit coefficients solve BOTH true original physical
Wilson Gram dual observation equations at genuine finite-H contexts. -/
theorem p4Q2MJ_originalPhysicalGramInverse_dual_exact
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (s t : ℝ) :
    A e e' z z' * (Inv e e' z z' s t).1 +
      B e e' z z' * (Inv e e' z z' s t).2 = s ∧
    B e e' z z' * (Inv e e' z z' s t).1 +
      C e e' z z' * (Inv e e' z z' s t).2 = t := by
  exact p4Q2MI_originalPhysicalGram_adjugate_inverse
    H b hb hpos hcount e e' z z' hQ s t

/-- Additivity of the explicit original physical Gram inverse.
This is an exact algebraic identity for the SAME original Gram,
so it does not require a new analytic assumption or fake receiver. -/
theorem p4Q2MJ_originalPhysicalGramInverse_add
    (e e' : Link) (z z' : Cfg × Cfg)
    (s₁ t₁ s₂ t₂ : ℝ) :
    Inv e e' z z' (s₁+s₂) (t₁+t₂) =
      ⟨(Inv e e' z z' s₁ t₁).1 +
          (Inv e e' z z' s₂ t₂).1,
        (Inv e e' z z' s₁ t₁).2 +
          (Inv e e' z z' s₂ t₂).2⟩ := by
  apply Prod.ext
  · dsimp [p4Q2MJ_originalPhysicalGramInverseCoefficients]
    ring
  · dsimp [p4Q2MJ_originalPhysicalGramInverseCoefficients]
    ring

/-- Real homogeneity of exactly the same original spatial Gram inverse. -/
theorem p4Q2MJ_originalPhysicalGramInverse_smul
    (e e' : Link) (z z' : Cfg × Cfg) (r s t : ℝ) :
    Inv e e' z z' (r*s) (r*t) =
      ⟨r*(Inv e e' z z' s t).1,
        r*(Inv e e' z z' s t).2⟩ := by
  apply Prod.ext
  · dsimp [p4Q2MJ_originalPhysicalGramInverseCoefficients]
    ring
  · dsimp [p4Q2MJ_originalPhysicalGramInverseCoefficients]
    ring

/-- Exact reconstruction of the DIFFERENCE of two arbitrary genuine
Wilson dual observation pairs by the difference of their original
physical Gram coefficients. -/
theorem p4Q2MJ_originalPhysicalGramInverse_sub
    (e e' : Link) (z z' : Cfg × Cfg)
    (s₁ t₁ s₂ t₂ : ℝ) :
    Inv e e' z z' (s₁-s₂) (t₁-t₂) =
      ⟨(Inv e e' z z' s₁ t₁).1 -
          (Inv e e' z z' s₂ t₂).1,
        (Inv e e' z z' s₁ t₁).2 -
          (Inv e e' z z' s₂ t₂).2⟩ := by
  apply Prod.ext
  · dsimp [p4Q2MJ_originalPhysicalGramInverseCoefficients]
    ring
  · dsimp [p4Q2MJ_originalPhysicalGramInverseCoefficients]
    ring

/-- MI's existing squared inverse stability now holds for this
EXPLICIT and UNIQUE original physical Wilson coefficient function,
not merely an unspecified existential coefficient witness. -/
theorem p4Q2MJ_originalPhysicalGramInverse_squaredStability
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (s t : ℝ) :
    ((Q e e' z z' / n) / (10 * E^2))^2 *
      ((Inv e e' z z' s t).1^2 +
        (Inv e e' z z' s t).2^2) ≤
      s^2+t^2 := by
  obtain ⟨q, ⟨hq₁, hq₂⟩, hStable⟩ :=
    p4Q2MI_originalPhysicalGram_inverse_squaredStability
      H b hb hpos hcount e e' z z' hQ s t
  obtain ⟨_, _, hUnique⟩ :=
    p4Q2MI_originalPhysicalGram_existsUnique_coefficients
      H b hb hpos hcount e e' z z' hQ s t
  have hInv :=
    p4Q2MJ_originalPhysicalGramInverse_dual_exact
      H b hb hpos hcount e e' z z' hQ s t
  have hEq : q = Inv e e' z z' s t :=
    (hUnique q ⟨hq₁, hq₂⟩).trans
      (hUnique (Inv e e' z z' s t) hInv).symm
  simpa only [hEq] using hStable

/-- FINITE-H Lipschitz stability of the genuine original interacting
Wilson physical coefficient recovery under changes in the TWO
spatial Gram dual observations. Uses NO new posterior or receiver. -/
theorem p4Q2MJ_originalPhysicalGramInverse_difference_squaredStability
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z')
    (s₁ t₁ s₂ t₂ : ℝ) :
    ((Q e e' z z' / n) / (10 * E^2))^2 *
      (((Inv e e' z z' s₁ t₁).1 -
          (Inv e e' z z' s₂ t₂).1)^2 +
        ((Inv e e' z z' s₁ t₁).2 -
          (Inv e e' z z' s₂ t₂).2)^2) ≤
      (s₁-s₂)^2 + (t₁-t₂)^2 := by
  have hStable :=
    p4Q2MJ_originalPhysicalGramInverse_squaredStability
      H b hb hpos hcount e e' z z' hQ (s₁-s₂) (t₁-t₂)
  rw [p4Q2MJ_originalPhysicalGramInverse_sub] at hStable
  exact hStable

/-- Genuine LY original interacting-Wilson witness contexts give
ONE fixed finite-H positive coefficient controlling EVERY PAIR
of real dual observations by the same original spatial inverse. -/
theorem p4Q2MJ_originalPhysicalGI_exists_allDataLipschitzInverse
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧ 0 < Q e e' z z' / n ∧
      ∀ s₁ t₁ s₂ t₂ : ℝ,
        ((Q e e' z z' / n) / (10 * E^2))^2 *
          (((Inv e e' z z' s₁ t₁).1 -
              (Inv e e' z z' s₂ t₂).1)^2 +
            ((Inv e e' z z' s₁ t₁).2 -
              (Inv e e' z z' s₂ t₂).2)^2) ≤
          (s₁-s₂)^2+(t₁-t₂)^2 := by
  obtain ⟨z, z', _, _, hn, hQ, _, _, _, _, _⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  refine ⟨z, z', hn, div_pos hQ hn, ?_⟩
  intro s₁ t₁ s₂ t₂
  exact p4Q2MJ_originalPhysicalGramInverse_difference_squaredStability
    H b hb hpos hn e e' z z' hQ s₁ t₁ s₂ t₂

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MJ_originalPhysicalGramInverse_dual_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MJ_originalPhysicalGramInverse_add
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MJ_originalPhysicalGramInverse_smul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MJ_originalPhysicalGramInverse_sub
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MJ_originalPhysicalGramInverse_squaredStability
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MJ_originalPhysicalGramInverse_difference_squaredStability
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MJ_originalPhysicalGI_exists_allDataLipschitzInverse
