import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsHilbertEquivalence
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalRandomScanEigenvalueBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

theorem finite_oriented_singleLinkHeatBathProjection_add
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection target (f + g) =
      L.singleLinkHeatBathProjection target f +
        L.singleLinkHeatBathProjection target g := by
  funext A
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  simp only [Pi.add_apply]
  ring

theorem finite_oriented_singleLinkHeatBathProjection_smul
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (c : ℝ)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection target (c • f) =
      c • L.singleLinkHeatBathProjection target f := by
  funext A
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _hh
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem finite_oriented_randomScanHeatBathSweep_add
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.randomScanHeatBathSweep (f + g) =
      L.randomScanHeatBathSweep f + L.randomScanHeatBathSweep g := by
  funext A
  unfold FiniteOrientedLatticeWilsonSystem.randomScanHeatBathSweep
  simp_rw [finite_oriented_singleLinkHeatBathProjection_add, Pi.add_apply]
  rw [Finset.sum_add_distrib]
  ring

theorem finite_oriented_randomScanHeatBathSweep_smul
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ)
    (f : L.Configuration → ℝ) :
    L.randomScanHeatBathSweep (c • f) =
      c • L.randomScanHeatBathSweep f := by
  funext A
  unfold FiniteOrientedLatticeWilsonSystem.randomScanHeatBathSweep
  simp_rw [finite_oriented_singleLinkHeatBathProjection_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

noncomputable def FiniteOrientedLatticeWilsonSystem.randomScanHeatBathSweepLinearMap
    (L : FiniteOrientedLatticeWilsonSystem) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) where
  toFun := L.randomScanHeatBathSweep
  map_add' := finite_oriented_randomScanHeatBathSweep_add L
  map_smul' := finite_oriented_randomScanHeatBathSweep_smul L

noncomputable def FiniteOrientedLatticeWilsonSystem.gibbsRandomScanLinearMap
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.GibbsHilbertSpace →ₗ[ℝ] L.GibbsHilbertSpace :=
  L.gibbsHilbertEmbedLinearMap.comp
    (L.randomScanHeatBathSweepLinearMap.comp
      L.gibbsHilbertObserveLinearMap)

theorem finite_oriented_gibbsRandomScanLinearMap_embed
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsRandomScanLinearMap (L.gibbsHilbertEmbedLinearMap f) =
      L.gibbsHilbertEmbedLinearMap (L.randomScanHeatBathSweep f) := by
  simp [FiniteOrientedLatticeWilsonSystem.gibbsRandomScanLinearMap,
    FiniteOrientedLatticeWilsonSystem.randomScanHeatBathSweepLinearMap,
    finite_oriented_gibbsHilbert_observe_embed]

theorem finite_oriented_gibbsRandomScanLinearMap_isSymmetric
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.gibbsRandomScanLinearMap.IsSymmetric := by
  intro x y
  let f := L.gibbsHilbertObserveLinearMap x
  let g := L.gibbsHilbertObserveLinearMap y
  have hx : L.gibbsHilbertEmbedLinearMap f = x :=
    finite_oriented_gibbsHilbert_embed_observe L x
  have hy : L.gibbsHilbertEmbedLinearMap g = y :=
    finite_oriented_gibbsHilbert_embed_observe L y
  calc
    inner ℝ (L.gibbsRandomScanLinearMap x) y =
        inner ℝ (L.gibbsHilbertEmbedLinearMap (L.randomScanHeatBathSweep f))
          (L.gibbsHilbertEmbedLinearMap g) := by
      rw [← hx, finite_oriented_gibbsRandomScanLinearMap_embed, ← hy]
    _ = L.gibbsPairingReal (L.randomScanHeatBathSweep f) g :=
      finite_oriented_gibbsHilbert_inner_embed L _ _
    _ = L.gibbsPairingReal f (L.randomScanHeatBathSweep g) :=
      finite_oriented_randomScanHeatBathSweep_gibbsPairing_symm L f g
    _ = inner ℝ (L.gibbsHilbertEmbedLinearMap f)
        (L.gibbsHilbertEmbedLinearMap (L.randomScanHeatBathSweep g)) :=
      (finite_oriented_gibbsHilbert_inner_embed L _ _).symm
    _ = inner ℝ x (L.gibbsRandomScanLinearMap y) := by
      rw [hx, ← hy, finite_oriented_gibbsRandomScanLinearMap_embed]

theorem finite_oriented_randomScanHeatBathSweep_one
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.randomScanHeatBathSweep (fun _ : L.Configuration => (1 : ℝ)) =
      fun _ : L.Configuration => (1 : ℝ) := by
  funext A
  have hCard : (Fintype.card L.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  unfold FiniteOrientedLatticeWilsonSystem.randomScanHeatBathSweep
  have hFix (target : L.Edge) :
      L.singleLinkHeatBathProjection target
          (fun _ : L.Configuration => (1 : ℝ)) =
        fun _ : L.Configuration => (1 : ℝ) := by
    apply finite_oriented_singleLinkHeatBathProjection_fixes
    intro B C hAgree
    rfl
  simp_rw [hFix]
  simpa [hCard]

theorem finite_oriented_gibbsRandomScanLinearMap_vacuum
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.gibbsRandomScanLinearMap L.gibbsHilbertVacuum =
      L.gibbsHilbertVacuum := by
  rw [FiniteOrientedLatticeWilsonSystem.gibbsHilbertVacuum,
    finite_oriented_gibbsRandomScanLinearMap_embed,
    finite_oriented_randomScanHeatBathSweep_one L hEdge]

end
end MathlibAnalytic
end MGAP4D
