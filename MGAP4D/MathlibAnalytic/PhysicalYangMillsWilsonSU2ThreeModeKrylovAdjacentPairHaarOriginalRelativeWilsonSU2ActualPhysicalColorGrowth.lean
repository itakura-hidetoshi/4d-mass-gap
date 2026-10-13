import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2PhysicalColorCardinalityUpper
import Mathlib.Tactic

/-!
# P4-Q2-ER: Genuine physical six-color link cardinality grows with the lattice

The original spatial slice has period 2*(H+1). Given ANY actual spatial
six-color class c, start from a certified original physical link of that
color group and move its base by 2*k units in its SAME original spatial direction,
where k ranges over Fin (H+1). These original periodic base vertices have
unchanged checkerboard parity, and distinct k give distinct ZMod coordinates.

Thus Fin (H+1) injects into the ACTUAL spatial six-color physical link
carrier, giving H+1 <= L_c(H). This is a genuine geometry theorem,
not an artificial nonnegative-link-weight spike or a substituted Haar law.

Together with EQ's genuine gauge-invariant SU(2) original Wilson witness,
any original AW-versus-interacting-D12 relative comparison coefficient
satisfies κ * (H+1) <= 12. A positive H-UNIFORM relative AW >= κ D12
bound, valid for all original Wilson SU(2) witnesses of this shape, is
therefore impossible. This statement is specifically about the relative
comparison of TWO different forms; it does NOT rule out an absolute gap
for either form, a continuum Yang-Mills theory, or a continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- Move a genuine time-zero spatial vertex by an EVEN displacement
in a genuine non-temporal spatial direction, preserving the primary slice. -/
private def p4Q2ER_evenTranslateSpatialVertex
    (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu : PeriodicHypercubicEvenSpatialDirection) (k : ℕ) :
    PeriodicHypercubicEvenSpatialSliceVertex H :=
  ⟨fun i => v.1 i +
      if i = mu.1 then
        ((2 * k : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))
      else 0,
    by
      simpa [periodicHypercubicEvenOnPrimaryReflectionPlane,
        Ne.symm mu.2] using v.2⟩

/-- The ACTUAL checkerboard parity is unchanged by a double-unit spatial
translation; use the existing canonical mod-2 ring homomorphism. -/
private theorem p4Q2ER_evenTranslateSpatialVertex_parity
    (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu : PeriodicHypercubicEvenSpatialDirection) (k : ℕ) :
    periodicHypercubicEvenCheckerboardParity H
        (p4Q2ER_evenTranslateSpatialVertex H v mu k).1 =
      periodicHypercubicEvenCheckerboardParity H v.1 := by
  unfold periodicHypercubicEvenCheckerboardParity
    periodicHypercubicEvenCoordinateParity
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = mu.1
  · subst i
    simp only [p4Q2ER_evenTranslateSpatialVertex]
    rw [map_add]
    have hTwo :
        periodicHypercubicEvenParityHom H
          ((2 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) = 0 := by
      rw [map_natCast]
      norm_num
    have heven :
        periodicHypercubicEvenParityHom H
          ((2 * k : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) = 0 := by
      rw [Nat.cast_mul, map_mul, hTwo, zero_mul]
    simpa only [ite_true, heven, add_zero]
  · change periodicHypercubicEvenParityHom H
        (v.1 i + (if i = mu.1 then
          ((2 * k : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) else 0)) =
        periodicHypercubicEvenParityHom H (v.1 i)
    simp [hi]

/-- Choose an EXISTING actual physical spatial link from every nonempty
original Wilson spatial six-color class, without a synthetic link carrier. -/
private noncomputable def p4Q2ER_colorBase (H : ℕ) (c : Fin 6) :
    p4Q2BA_ColorLinks H c :=
  Classical.choice (p4Q2BA_colorLinks_nonempty H c)

/-- An actual link of color c obtained by even translation of the
selected original color-c base link. -/
private noncomputable def p4Q2ER_evenColorEmbedding
    (H : ℕ) (c : Fin 6) (k : Fin (H + 1)) :
    p4Q2BA_ColorLinks H c := by
  let base := p4Q2ER_colorBase H c
  refine ⟨(p4Q2ER_evenTranslateSpatialVertex H base.1.1 base.1.2 k.1,
    base.1.2), ?_⟩
  change
    (base.1.2,
      periodicHypercubicEvenCheckerboardParity H
        (p4Q2ER_evenTranslateSpatialVertex H base.1.1 base.1.2 k.1).1) =
      periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c
  rw [p4Q2ER_evenTranslateSpatialVertex_parity]
  exact base.2

/-- EVEN original periodic translation is injective for the first H+1
half-period positions: the residues 2*k, k < H+1, never wrap around
the true side length 2*(H+1). -/
theorem p4Q2ER_evenColorEmbedding_injective (H : ℕ) (c : Fin 6) :
    Function.Injective (p4Q2ER_evenColorEmbedding H c) := by
  intro k l h
  let base := p4Q2ER_colorBase H c
  have hCoord := congrArg
    (fun z : p4Q2BA_ColorLinks H c => z.1.1.1 base.1.2.1) h
  have hCast :
      ((2 * k.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) =
      ((2 * l.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) := by
    dsimp [p4Q2ER_evenColorEmbedding, p4Q2ER_evenTranslateSpatialVertex] at hCoord
    dsimp only [base] at hCoord
    simp only [eq_self_iff_true, ite_true] at hCoord
    exact add_left_cancel hCoord
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    change 2 * (H + 1) ≠ 0
    omega⟩
  have hk : 2 * k.1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hl : 2 * l.1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hVal := congrArg ZMod.val hCast
  rw [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hl] at hVal
  apply Fin.ext
  omega

/-- The actual physical color-link count grows at least linearly with the
original lattice half-size for EVERY one of the six original spatial colors. -/
theorem p4Q2ER_actualColorLinkCard_ge_halfSide (H : ℕ) (c : Fin 6) :
    H + 1 ≤ Fintype.card (p4Q2BA_ColorLinks H c) := by
  have h :=
    Fintype.card_le_of_injective (p4Q2ER_evenColorEmbedding H c)
      (p4Q2ER_evenColorEmbedding_injective H c)
  simpa using h

/-- In particular, the selected color of EVERY actual physical SU(2)
spatial link e obeys the same half-side cardinality growth. -/
theorem p4Q2ER_selectedPhysicalColorLinkCard_ge_halfSide
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    H + 1 ≤ p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e := by
  exact p4Q2ER_actualColorLinkCard_ge_halfSide H
    (periodicHypercubicEvenGroundStateSpatialColorEquivFin
      (periodicHypercubicEvenSpatialSliceLinkColor H e))

/-- The EQ physical gauge-invariant Wilson witness forces a finite-H
relative comparison coefficient κ to satisfy κ*(H+1) <= 12. Unlike
EA's arbitrary nonnegative link weights, this uses the ACTUAL Wilson
ground-state joint L² physical gauge-invariant SU(2) class and the true
positive original Wilson conditional twelve-color D12 energy. -/
theorem p4Q2ER_SU2_relativeCoefficient_mul_halfSide_le_twelve
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hLower :
      κ * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H 2 (Nat.zero_lt_succ 1) beta hbeta
          (p4Q2EE_SU2_physicalWilsonJointL2 H beta hbeta e) ≤
      p4Q2BX_originalFullJointQuadratic H 2 (Nat.zero_lt_succ 1) beta hbeta
        (p4Q2EE_SU2_physicalWilsonJointL2 H beta hbeta e)) :
    κ * (H + 1 : ℝ) ≤ 12 := by
  have hκBound :=
    p4Q2EQ_SU2_anyRelativeCoefficient_le_twelve_div_selectedColorCard
      H beta hbeta e κ hLower
  have hCard :=
    p4Q2ER_selectedPhysicalColorLinkCard_ge_halfSide H e
  have hCardReal :
      (H + 1 : ℝ) ≤
        (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ) := by
    exact_mod_cast hCard
  have hCardPos :
      0 < (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ) := by
    exact_mod_cast p4Q2EQ_SU2_selectedPhysicalColorLinkCard_pos H e
  have hBig :
      κ * (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ) ≤ 12 :=
    (le_div_iff₀ hCardPos).mp hκBound
  exact (mul_le_mul_of_nonneg_left hCardReal hκ).trans hBig

/-- NO positive coefficient can satisfy AW >= κ*D12 on ALL spatial
volumes even when restricted to the same concrete gauge-invariant SU(2)
relative-link Wilson witness at beta=0. This is strictly a failure of an
H-uniform RELATIVE comparison of two distinct energy forms. -/
theorem p4Q2ER_SU2_no_positive_uniformRelativeAWD12Coefficient :
    ¬ ∃ κ : ℝ, 0 < κ ∧
      ∀ (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H),
        κ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
            H 2 (Nat.zero_lt_succ 1) 0 (le_refl 0)
              (p4Q2EE_SU2_physicalWilsonJointL2 H 0 (le_refl 0) e) ≤
          p4Q2BX_originalFullJointQuadratic
            H 2 (Nat.zero_lt_succ 1) 0 (le_refl 0)
              (p4Q2EE_SU2_physicalWilsonJointL2 H 0 (le_refl 0) e) := by
  rintro ⟨κ, hκ, hUniform⟩
  obtain ⟨H, hH⟩ := exists_nat_gt (12 / κ)
  let e : PeriodicHypercubicEvenSpatialSliceLink H :=
    (p4Q2ER_colorBase H (0 : Fin 6)).1
  have hκBound :=
    p4Q2ER_SU2_relativeCoefficient_mul_halfSide_le_twelve
      H 0 (le_refl 0) e κ hκ.le (hUniform H e)
  have hStrict : 12 < κ * (H : ℝ) := by
    nlinarith [(div_lt_iff₀ hκ).mp hH]
  nlinarith

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2ER_evenColorEmbedding_injective
#print axioms MGAP4D.MathlibAnalytic.p4Q2ER_actualColorLinkCard_ge_halfSide
#print axioms MGAP4D.MathlibAnalytic.p4Q2ER_selectedPhysicalColorLinkCard_ge_halfSide
#print axioms MGAP4D.MathlibAnalytic.p4Q2ER_SU2_relativeCoefficient_mul_halfSide_le_twelve
#print axioms MGAP4D.MathlibAnalytic.p4Q2ER_SU2_no_positive_uniformRelativeAWD12Coefficient
