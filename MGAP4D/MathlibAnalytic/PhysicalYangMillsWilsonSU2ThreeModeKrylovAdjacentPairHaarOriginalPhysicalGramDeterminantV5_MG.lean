import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLinearGIPhysicalGapV5_MF
import Mathlib.Tactic

/-!
# P4-Q2-MG — positive genuine Wilson physical-source Gram determinant

MF proved a LINEAR-in-original-GI-energy lower bound for the actual
spatial mean of the original physical Gauss-law two-source squared
posterior expectation gaps, using the true p-dependent sources
  x U + y W_{H,p} U.

Here we take the exact polarization of THOSE SAME original physical
signed two-posterior gap squares. For each true plaquette p, write
R_p(x,y) for the sum of its two original squared signed expectation
gaps, with the true interacting-Wilson boundary contexts held fixed.

Its true two-source Gram moments are
  A = (1/N) sum_p R_p(1,0),
  C = (1/N) sum_p R_p(0,1),
  B = (1/(2N)) sum_p [R_p(1,1)-R_p(1,0)-R_p(0,1)].
By linearity of the ALREADY PROVED original physical Gauss-law
sources (LO), not by an assumed external detector,
  (1/N) sum_p R_p(x,y) = A x^2 + 2 B xy + C y^2.

At positive original Wilson coupling and authentic contexts with
Q = sum_p DeltaBar_p^2 > 0 and N > 0, MF proves
  A x^2 + 2 B xy + C y^2 >= k (x^2+y^2),
  k = (Q/N)/(10 E_b^2) > 0,
for all REAL x,y. In particular A > 0 and AC-B^2 > 0:
the actual original physical two-source Gram is POSITIVE DEFINITE
at each finite H. One pair of authentic LY interacting-posterior
witness contexts suffices.

This does NOT prove a volume-uniform lower bound on k or AC-B^2;
does NOT identify the p-dependent spatial source family with one
single global endpoint source; and does NOT close H1-C3, continuum
Yang-Mills or the physical mass gap.

No independent Haar posterior, new measure/rank/source, Dobrushin
hypothesis, sorry/admit, or extra axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "R" =>
  p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare H b hb

/-- The first exact genuine Wilson physical-source Gram diagonal. -/
noncomputable def p4Q2MG_originalPhysicalGramUU
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  (∑ p : Plaq, R e e' z z' p 1 0) / n

/-- The original physical-source Gram off-diagonal, defined by
polarization of the ACTUAL signed-posterior gap squares. -/
noncomputable def p4Q2MG_originalPhysicalGramUW
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  ((∑ p : Plaq,
      (R e e' z z' p 1 1 - R e e' z z' p 1 0 -
        R e e' z z' p 0 1)) / n) / 2

/-- The second exact genuine Wilson physical-source Gram diagonal. -/
noncomputable def p4Q2MG_originalPhysicalGramWW
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  (∑ p : Plaq, R e e' z z' p 0 1) / n

local notation "A" => p4Q2MG_originalPhysicalGramUU H b hb
local notation "B" => p4Q2MG_originalPhysicalGramUW H b hb
local notation "C" => p4Q2MG_originalPhysicalGramWW H b hb

/-- Exactly quadratic dependence of the REAL original p-indexed
physical Gauss-law two-source squared posterior gap on x,y.
No new source: this uses LO's true physical GI linear response. -/
theorem p4Q2MG_originalPhysicalGapSquare_polarization
    (e e' : Link) (z z' : Cfg × Cfg)
    (p : Plaq) (x y : ℝ) :
    R e e' z z' p x y =
      R e e' z z' p 1 0 * x^2 +
      (R e e' z z' p 1 1 -
        R e e' z z' p 1 0 - R e e' z z' p 0 1) * (x*y) +
      R e e' z z' p 0 1 * y^2 := by
  unfold p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare
  simp only [p4Q2LO_originalPhysicalLocalTwoSource_GI_eq]
  ring

/-- The full true physical spatial gap square has EXACTLY the
symmetric 2-by-2 Gram quadratic polynomial of its original physical
two-source response: A*x² + 2B*xy + C*y². -/
theorem p4Q2MG_originalFullPhysicalGapAverage_eq_Gram
    (e e' : Link) (z z' : Cfg × Cfg) (x y : ℝ) :
    (∑ p : Plaq, R e e' z z' p x y) / n =
      A e e' z z' * x^2 +
      2 * B e e' z z' * x*y +
      C e e' z z' * y^2 := by
  classical
  have hSum :
      (∑ p : Plaq, R e e' z z' p x y) =
      ∑ p : Plaq,
        (R e e' z z' p 1 0 * x^2 +
        (R e e' z z' p 1 1 -
          R e e' z z' p 1 0 - R e e' z z' p 0 1) * (x*y) +
        R e e' z z' p 0 1 * y^2) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact p4Q2MG_originalPhysicalGapSquare_polarization
      H b hb e e' z z' p x y
  rw [hSum]
  simp only [Finset.sum_add_distrib, Finset.sum_mul]
  unfold p4Q2MG_originalPhysicalGramUU
    p4Q2MG_originalPhysicalGramUW
    p4Q2MG_originalPhysicalGramWW
  ring

/-- MF's LINEAR true GI density forces the original two-source
physical response Gram quadratic form to dominate an honest
strictly positive multiple of the Euclidean square on ℝ². -/
theorem p4Q2MG_originalPhysicalGram_ge_linearGIFloor
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (x y : ℝ) :
    ((Q e e' z z' / n) / (10 * E^2)) * (x^2+y^2) ≤
      A e e' z z' * x^2 +
      2 * B e e' z z' * x*y +
      C e e' z z' * y^2 := by
  calc
    ((Q e e' z z' / n) / (10 * E^2)) * (x^2+y^2) ≤
        (∑ p : Plaq, R e e' z z' p x y) / n :=
      p4Q2MF_originalFullPhysicalGapAverage_ge_linearGI
        H b hb hpos hcount e e' z z' x y
    _ = A e e' z z' * x^2 +
        2 * B e e' z z' * x*y +
        C e e' z z' * y^2 :=
      p4Q2MG_originalFullPhysicalGapAverage_eq_Gram
        H b hb e e' z z' x y

/-- Strictly positive Gram determinant of the ACTUAL original
interacting-Wilson spatial two-source physical posterior responses.
Follows algebraically from MF's positive lower frame bound, and is
not claimed uniformly positive in lattice volume H. -/
theorem p4Q2MG_originalPhysicalGram_det_pos
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') :
    0 < A e e' z z' * C e e' z z' -
      (B e e' z z')^2 := by
  let a : ℝ := A e e' z z'
  let d : ℝ := C e e' z z'
  let c : ℝ := B e e' z z'
  let k : ℝ := (Q e e' z z' / n) / (10 * E^2)
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hK : 0 < k := by
    dsimp [k]
    exact div_pos (div_pos hQ hcount)
      (mul_pos (by norm_num) (sq_pos_of_pos hE))
  have hFrame : ∀ x y : ℝ,
      k * (x^2+y^2) ≤ a*x^2 + 2*c*x*y + d*y^2 := by
    intro x y
    exact p4Q2MG_originalPhysicalGram_ge_linearGIFloor
      H b hb hpos hcount e e' z z' x y
  have ha : k ≤ a := by
    have h := hFrame 1 0
    nlinarith
  have haPos : 0 < a := lt_of_lt_of_le hK ha
  have hSquarePos : 0 < c^2 + a^2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos haPos)
  have hBound : k * (c^2 + a^2) ≤ a * (a*d - c^2) := by
    calc
      k * (c^2 + a^2) = k * (c^2 + (-a)^2) := by ring
      _ ≤ a*c^2 + 2*c*c*(-a) + d*(-a)^2 := hFrame c (-a)
      _ = a * (a*d - c^2) := by ring
  have hProd : 0 < a * (a*d - c^2) :=
    lt_of_lt_of_le (mul_pos hK hSquarePos) hBound
  have hDet : 0 < a*d - c^2 := by
    by_contra hNon
    have hNonpos : a*d - c^2 ≤ 0 := le_of_not_gt hNon
    have hProdNonpos : a*(a*d - c^2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos haPos.le hNonpos
    exact (not_le_of_gt hProd) hProdNonpos
  exact hDet

/-- LY's authentic genuine interacting-Wilson two-context witness
selects an explicitly positive-definite ORIGINAL full-spatial physical
Gauss-law two-source Gram, not a synthetic detector or rank axiom. -/
theorem p4Q2MG_originalPhysicalGI_exists_positiveGram
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧
      0 < Q e e' z z' / n ∧
      0 < A e e' z z' * C e e' z z' -
        (B e e' z z')^2 := by
  obtain ⟨z, z', _, _, hn, hQ, _, _, _, _, _⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  exact ⟨z, z', hn, div_pos hQ hn,
    p4Q2MG_originalPhysicalGram_det_pos H b hb hpos hn e e' z z' hQ⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MG_originalPhysicalGapSquare_polarization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MG_originalFullPhysicalGapAverage_eq_Gram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MG_originalPhysicalGram_ge_linearGIFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MG_originalPhysicalGram_det_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MG_originalPhysicalGI_exists_positiveGram
