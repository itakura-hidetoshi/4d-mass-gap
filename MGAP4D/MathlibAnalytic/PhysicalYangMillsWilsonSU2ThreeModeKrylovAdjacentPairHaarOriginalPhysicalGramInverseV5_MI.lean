import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalGramQuantitativeDeterminantV5_MH
import Mathlib.Tactic

/-!
# P4-Q2-MI — constructive inverse of the genuine physical Wilson Gram

MG/MH proved that the exact original interacting SU(2) Wilson
two-source spatial physical-response Gram has positive determinant
at genuine finite-volume contexts with positive original GI square
energy Q. MI uses that determinant to reconstruct the unique two
REAL physical-source coefficients (x,y) from arbitrary prescribed
Gram dual coordinates (s,t), WITHOUT inventing another response
operator, posterior, probability law, or physical source.

The two-source physical plane is exactly the original p-indexed
Gauss-law source x U + y W_{H,p} U, and the Gram coefficients A,B,C
are the spatial averages of the true signed interacting-Wilson
two-posterior physical gaps defined in MG. Thus the inverse is the
ordinary constructive adjugate of that same genuine Gram:

  D = A*C - B² > 0,
  x = (C*s - B*t)/D,    y = (A*t - B*s)/D,
  A*x+B*y = s,          B*x+C*y = t.

Moreover the already proved MF lower frame bound
  k(x²+y²) <= A*x²+2Bxy+C*y²
and the real two-dimensional Cauchy-Schwarz identity give
  k²(x²+y²) <= s²+t²,
where k = (Q/N)/(10 E_b²) > 0 at real LY witness contexts.

These statements are finite-H and about the physical spatial Gram
with plaquette-dependent original sources. They are not a global
endpoint inversion, not an H-uniform inverse bound, not H1-C3
closure, continuum Yang-Mills, or a positive mass gap.

No Dobrushin or independent Haar replacement. No artificial
detector/source/rank, new analytic hypothesis, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Pure real two-by-two inversion; the actual Gram entries are
supplied by previously verified original physical Wilson theorems. -/
private theorem p4Q2MI_realGram_existsUniqueCoefficients
    (a u c s t : ℝ) (hdet : a*c - u^2 ≠ 0) :
    ∃! q : ℝ × ℝ,
      a*q.1 + u*q.2 = s ∧
      u*q.1 + c*q.2 = t := by
  refine ⟨⟨(c*s-u*t)/(a*c-u^2), (a*t-u*s)/(a*c-u^2)⟩, ?_, ?_⟩
  · constructor
    · dsimp
      field_simp [hdet] <;> ring
    · dsimp
      field_simp [hdet] <;> ring
  · rintro ⟨x,y⟩ ⟨hs,ht⟩
    apply Prod.ext
    · apply (eq_div_iff hdet).2
      calc
        x*(a*c-u^2) = c*(a*x+u*y)-u*(u*x+c*y) := by ring
        _ = c*s-u*t := by rw [hs, ht]
    · apply (eq_div_iff hdet).2
      calc
        y*(a*c-u^2) = a*(u*x+c*y)-u*(a*x+u*y) := by ring
        _ = a*t-u*s := by rw [hs, ht]

/-- The elementary real-plane polarization/Cauchy-Schwarz identity:
the genuine Gram-dual coordinates cannot have less Euclidean
energy than the squared lower-frame constant times the source. -/
private theorem p4Q2MI_realFrame_inverseSqBound
    (k x y s t : ℝ) (hk : 0 < k)
    (hframe : k*(x^2+y^2) ≤ x*s+y*t) :
    k^2*(x^2+y^2) ≤ s^2+t^2 := by
  let S : ℝ := x^2+y^2
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  by_cases hZero : S = 0
  · dsimp [S] at hZero
    rw [hZero]
    simpa using (show (0 : ℝ) ≤ s^2+t^2 from by positivity)
  · have hPos : 0 < S := lt_of_le_of_ne hS (Ne.symm hZero)
    have hFrameS : k*S ≤ x*s+y*t := hframe
    have hDotNonneg : 0 ≤ x*s+y*t :=
      (mul_nonneg hk.le hS).trans hFrameS
    have hSquare : (k*S)^2 ≤ (x*s+y*t)^2 :=
      (sq_le_sq₀ (mul_nonneg hk.le hS) hDotNonneg).2 hFrameS
    have hCS : (x*s+y*t)^2 ≤ S*(s^2+t^2) := by
      dsimp [S]
      nlinarith [sq_nonneg (x*t-y*s)]
    have hBoth : S*(k^2*S) ≤ S*(s^2+t^2) := by
      calc
        S*(k^2*S) = (k*S)^2 := by ring
        _ ≤ (x*s+y*t)^2 := hSquare
        _ ≤ S*(s^2+t^2) := hCS
    exact (mul_le_mul_iff_of_pos_left hPos).mp hBoth

end GroundStatePosteriorJoint

local instance p4Q2MI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MI_borelSpace :
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

/-- Explicit inversion of the ORIGINAL true signed posterior
Gauss-law two-source spatial Gram, at genuine finite-H contexts
with positive Wilson GI determinant-square energy. -/
theorem p4Q2MI_originalPhysicalGram_adjugate_inverse
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (s t : ℝ) :
    A e e' z z' *
        ((C e e' z z' * s - B e e' z z' * t) /
          (A e e' z z' * C e e' z z' - (B e e' z z')^2)) +
      B e e' z z' *
        ((A e e' z z' * t - B e e' z z' * s) /
          (A e e' z z' * C e e' z z' - (B e e' z z')^2)) = s ∧
    B e e' z z' *
        ((C e e' z z' * s - B e e' z z' * t) /
          (A e e' z z' * C e e' z z' - (B e e' z z')^2)) +
      C e e' z z' *
        ((A e e' z z' * t - B e e' z z' * s) /
          (A e e' z z' * C e e' z z' - (B e e' z z')^2)) = t := by
  have hdet : A e e' z z' * C e e' z z' - (B e e' z z')^2 ≠ 0 :=
    ne_of_gt (p4Q2MG_originalPhysicalGram_det_pos
      H b hb hpos hcount e e' z z' hQ)
  constructor
  · field_simp [hdet] <;> ring
  · field_simp [hdet] <;> ring

/-- Every prescribed REAL dual-coordinate pair (s,t) uniquely
reconstructs its original physical Wilson spatial Gram source-plane
coefficients. Uniqueness comes only from the ALREADY PROVED genuine
physical Gram determinant, not an artificial rank assumption. -/
theorem p4Q2MI_originalPhysicalGram_existsUnique_coefficients
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (s t : ℝ) :
    ∃! q : ℝ × ℝ,
      A e e' z z' * q.1 + B e e' z z' * q.2 = s ∧
      B e e' z z' * q.1 + C e e' z z' * q.2 = t := by
  have hdet : A e e' z z' * C e e' z z' - (B e e' z z')^2 ≠ 0 :=
    ne_of_gt (p4Q2MG_originalPhysicalGram_det_pos
      H b hb hpos hcount e e' z z' hQ)
  exact p4Q2MI_realGram_existsUniqueCoefficients
    (A e e' z z') (B e e' z z') (C e e' z z')
    s t hdet

/-- Reconstructed genuine original Wilson physical coefficients are
quantitatively stable at finite H:
  k²*(x²+y²) ≤ s²+t², k=(Q/N)/(10E_b²).
The same exact original Gram as MG/MH is used, and the stability
constant is honestly H-dependent, not a mass-gap claim. -/
theorem p4Q2MI_originalPhysicalGram_inverse_squaredStability
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (s t : ℝ) :
    ∃ q : ℝ × ℝ,
      (A e e' z z' * q.1 + B e e' z z' * q.2 = s ∧
       B e e' z z' * q.1 + C e e' z z' * q.2 = t) ∧
      ((Q e e' z z' / n) / (10 * E^2))^2 *
        (q.1^2+q.2^2) ≤ s^2+t^2 := by
  obtain ⟨q, ⟨hs,ht⟩, _⟩ :=
    p4Q2MI_originalPhysicalGram_existsUnique_coefficients
      H b hb hpos hcount e e' z z' hQ s t
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hk : 0 < (Q e e' z z' / n) / (10 * E^2) :=
    div_pos (div_pos hQ hcount)
      (mul_pos (by norm_num) (sq_pos_of_pos hE))
  have hFrame :=
    p4Q2MG_originalPhysicalGram_ge_linearGIFloor
      H b hb hpos hcount e e' z z' q.1 q.2
  have hLinear :
      A e e' z z' * q.1^2 + 2 * B e e' z z' * q.1*q.2 +
        C e e' z z' * q.2^2 = q.1*s + q.2*t := by
    calc
      A e e' z z' * q.1^2 + 2 * B e e' z z' * q.1*q.2 +
          C e e' z z' * q.2^2 =
        q.1*(A e e' z z' * q.1 + B e e' z z' * q.2) +
        q.2*(B e e' z z' * q.1 + C e e' z z' * q.2) := by ring
      _ = q.1*s + q.2*t := by rw [hs,ht]
  have hDot :
      ((Q e e' z z' / n) / (10 * E^2)) * (q.1^2+q.2^2) ≤
        q.1*s + q.2*t :=
    hFrame.trans_eq hLinear
  exact ⟨q, ⟨hs,ht⟩,
    p4Q2MI_realFrame_inverseSqBound
      ((Q e e' z z' / n) / (10 * E^2))
      q.1 q.2 s t hk hDot⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MI_originalPhysicalGram_adjugate_inverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MI_originalPhysicalGram_existsUnique_coefficients
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MI_originalPhysicalGram_inverse_squaredStability
