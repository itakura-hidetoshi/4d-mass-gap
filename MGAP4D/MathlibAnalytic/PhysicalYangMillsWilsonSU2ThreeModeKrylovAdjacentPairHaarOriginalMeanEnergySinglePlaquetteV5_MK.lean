import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalGramInverseLipschitzV5_MJ
import Mathlib.Tactic

/-!
# P4-Q2-MK — one ACTUAL original Wilson plaquette attains the GI mean floor

The earlier MB/MC selected genuinely active original spatial Wilson
plaquettes using a HALF-mean-square threshold Q/(2N). MF improved
their spatially AVERAGED physical two-source response to a LINEAR
bound in the original compensated GI square-energy density Q/N.

MK proves the sharper spatial SELECTION result for a SINGLE actual
original SU(2) Wilson plaquette, without a synthetic detector or
independent Haar posterior. At any fixed finite H, positive b and
authentic interacting-Wilson boundary contexts with Q>0 and N>0,
the MAXIMUM of the actual local original compensated GI minor squares
over the finite original spatial plaquette carrier satisfies

    Q/N <= DeltaBar_p^2.

LY's already-verified real original-posterior source inequality then
gives a true SINGLE plaquette p with

    [ (Q/N)/(10 E_b^2) ] * (x^2+y^2)
      <= R_p(x,y)

for ALL REAL x,y simultaneously at the SAME genuine Wilson contexts.
Unlike MB's half-mean activity threshold there is no factor 1/2
loss. The original p-dependent Gauss-law source remains precisely
x U + y W_{H,p} U. The source is a genuine p-specific physical plane,
NOT one p-independent/global endpoint transfer source.

The witness may depend on H and the authentic contexts: no
H-uniform positive energy-density floor, H1-C3 strong-limit closure,
continuum Yang-Mills construction or mass gap is claimed. No new
physical assumption, Dobrushin, posterior substitution, sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MK_borelSpace :
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
local notation "d" => p4Q2LW_originalCompensatedLocalGIMinor H b hb
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "kappa" => p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb
local notation "R" =>
  p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare H b hb

/-- A REAL original plaquette attains at least the ACTUAL mean of
the original compensated GI determinant squares. This uses the
true original finite plaquette carrier, not a volume surrogate. -/
theorem p4Q2MK_originalGI_exists_meanEnergyPlaquette
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg) :
    ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      Q e e' z z' / n ≤ (d e e' z z' p)^2 := by
  classical
  have hCard : n = (Fintype.card Plaq : ℝ) := by
    exact_mod_cast p4Q2LQ_originalSpatialPlaquetteCount_eq_card H
  have hCardReal : 0 < (Fintype.card Plaq : ℝ) := by
    simpa only [hCard] using hcount
  have hCardNat : 0 < Fintype.card Plaq := by
    exact_mod_cast hCardReal
  have hCarrier : (Finset.univ : Finset Plaq).Nonempty :=
    Finset.card_pos.mp (by simpa only [Finset.card_univ] using hCardNat)
  obtain ⟨p, hp, hMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Plaq)
      (fun q => (d e e' z z' q)^2) hCarrier
  have hSumBound :
      Q e e' z z' ≤ n * (d e e' z z' p)^2 := by
    change (∑ q : Plaq, (d e e' z z' q)^2) ≤
      n * (d e e' z z' p)^2
    calc
      (∑ q : Plaq, (d e e' z z' q)^2) ≤
          (∑ q : Plaq, (d e e' z z' p)^2) :=
        Finset.sum_le_sum
          (fun q _ => hMax q (Finset.mem_univ q))
      _ = n * (d e e' z z' p)^2 := by
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ, hCard]
  have hpOriginal : p ∈
      periodicHypercubicEvenSpatialSlicePlaquetteList H := by
    change p ∈ (Finset.univ : Finset Plaq).toList
    simp
  refine ⟨p, hpOriginal, ?_⟩
  exact (div_le_iff₀ hcount).2 (by simpa [mul_comm] using hSumBound)

/-- At every actual positive-energy original interacting-Wilson
context, some SINGLE ORIGINAL spatial plaquette has a true local
physical Gauss-law two-source coefficient at least the FULL
original compensated GI energy density divided by 10 E_b².
The same original source is coercive for ALL real x,y. -/
theorem p4Q2MK_originalPhysicalGI_exists_meanCoercivePlaquette
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') :
    ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < kappa e e' z z' p ∧
      (Q e e' z z' / n) / (10 * E^2) ≤
        kappa e e' z z' p ∧
      ∀ x y : ℝ,
        kappa e e' z z' p * (x^2+y^2) ≤
          R e e' z z' p x y := by
  obtain ⟨p, hp, hAvg⟩ :=
    p4Q2MK_originalGI_exists_meanEnergyPlaquette
      H b hb hcount e e' z z'
  have hAvgPos : 0 < Q e e' z z' / n :=
    div_pos hQ hcount
  have hCompSqPos : 0 < (d e e' z z' p)^2 :=
    lt_of_lt_of_le hAvgPos hAvg
  have hd : d e e' z z' p ≠ 0 :=
    (sq_pos_iff).mp hCompSqPos
  have hOriginal :
      p4Q2LO_originalLocalPlaquetteGIMinor
        H b hb e e' z z' p ≠ 0 := by
    intro hz
    apply hd
    rw [p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original,
      hz, mul_zero]
  obtain ⟨hKappaPos, hPhysical⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hOriginal
  have hE : 0 < E :=
    p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hDen : 0 < 10 * E^2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hE)
  have hScaled :
      (Q e e' z z' / n) / (10 * E^2) ≤
        (d e e' z z' p)^2 / (10 * E^2) :=
    (div_le_div_iff_of_pos_right hDen).2 hAvg
  have hFloor :=
    p4Q2LY_originalPhysicalLocalGI_ge_compensatedLocal_sq_floor
      H b hb hpos e e' z z' p hOriginal
  exact ⟨p, hp, hKappaPos, hScaled.trans hFloor, hPhysical⟩

/-- The selected genuine original plaquette ALONE (not a spatial
sum) carries a physical squared-posterior-gap lower bound with
the FULL original spatial GI energy density Q/N. -/
theorem p4Q2MK_originalPhysicalGI_exists_singlePlaquetteLinearFloor
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') :
    ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      ∀ x y : ℝ,
        ((Q e e' z z' / n) / (10 * E^2)) *
          (x^2+y^2) ≤ R e e' z z' p x y := by
  obtain ⟨p, hp, _, hFloor, hPhysical⟩ :=
    p4Q2MK_originalPhysicalGI_exists_meanCoercivePlaquette
      H b hb hpos hcount e e' z z' hQ
  refine ⟨p, hp, ?_⟩
  intro x y
  have hS : 0 ≤ x^2+y^2 := by positivity
  calc
    ((Q e e' z z' / n) / (10 * E^2)) * (x^2+y^2) ≤
        kappa e e' z z' p * (x^2+y^2) :=
      mul_le_mul_of_nonneg_right hFloor hS
    _ ≤ R e e' z z' p x y := hPhysical x y

/-- At LY's authentic positive original interacting-Wilson
contexts, ONE actual spatial plaquette and one genuine original
p-specific Gauss-law physical source plane obey the full Q/N linear
coercivity estimate simultaneously for ALL source coefficients.
The witness and Q/N may still depend on finite H. -/
theorem p4Q2MK_originalPhysicalGI_exists_authenticMeanPlaquette
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧
      0 < Q e e' z z' / n ∧
      ∃ p : Plaq,
        p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
        ∀ x y : ℝ,
          ((Q e e' z z' / n) / (10 * E^2)) *
            (x^2+y^2) ≤ R e e' z z' p x y := by
  obtain ⟨z, z', _, _, hn, hQ, _, _, _, _, _⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  obtain ⟨p, hp, hPhysical⟩ :=
    p4Q2MK_originalPhysicalGI_exists_singlePlaquetteLinearFloor
      H b hb hpos hn e e' z z' hQ
  exact ⟨z, z', hn, div_pos hQ hn, p, hp, hPhysical⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MK_originalGI_exists_meanEnergyPlaquette
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MK_originalPhysicalGI_exists_meanCoercivePlaquette
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MK_originalPhysicalGI_exists_singlePlaquetteLinearFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MK_originalPhysicalGI_exists_authenticMeanPlaquette
