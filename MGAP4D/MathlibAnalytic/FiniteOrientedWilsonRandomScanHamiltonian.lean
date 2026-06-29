import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathPairingSymmetry
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinRandomScanScale

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

theorem finite_oriented_gibbsPairingReal_add_left
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal (f + g) h =
      L.gibbsPairingReal f h + L.gibbsPairingReal g h := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.add_apply]
  ring

theorem finite_oriented_gibbsPairingReal_add_right
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal f (g + h) =
      L.gibbsPairingReal f g + L.gibbsPairingReal f h := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.add_apply]
  ring

theorem finite_oriented_gibbsPairingReal_sub_left
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal (f - g) h =
      L.gibbsPairingReal f h - L.gibbsPairingReal g h := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.sub_apply]
  ring

theorem finite_oriented_gibbsPairingReal_sub_right
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal f (g - h) =
      L.gibbsPairingReal f g - L.gibbsPairingReal f h := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.sub_apply]
  ring

theorem finite_oriented_gibbsPairingReal_const_mul_left
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (fun A => c * f A) g =
      c * L.gibbsPairingReal f g := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

theorem finite_oriented_gibbsPairingReal_const_mul_right
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f (fun A => c * g A) =
      c * L.gibbsPairingReal f g := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

theorem finite_oriented_gibbsPairingReal_finset_sum_left
    (L : FiniteOrientedLatticeWilsonSystem)
    {ι : Type*}
    (s : Finset ι)
    (F : ι → L.Configuration → ℝ)
    (g : L.Configuration → ℝ) :
    L.gibbsPairingReal (s.sum F) g =
      s.sum (fun i => L.gibbsPairingReal (F i) g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FiniteOrientedLatticeWilsonSystem.gibbsPairingReal]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,
        finite_oriented_gibbsPairingReal_add_left,
        ih,
        Finset.sum_insert ha]

theorem finite_oriented_gibbsPairingReal_finset_sum_right
    (L : FiniteOrientedLatticeWilsonSystem)
    {ι : Type*}
    (s : Finset ι)
    (f : L.Configuration → ℝ)
    (G : ι → L.Configuration → ℝ) :
    L.gibbsPairingReal f (s.sum G) =
      s.sum (fun i => L.gibbsPairingReal f (G i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FiniteOrientedLatticeWilsonSystem.gibbsPairingReal]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,
        finite_oriented_gibbsPairingReal_add_right,
        ih,
        Finset.sum_insert ha]

/-- Exact random-scan heat-bath sweep on orientation-correct observables. -/
def FiniteOrientedLatticeWilsonSystem.randomScanHeatBathSweep
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : L.Configuration → ℝ := by
  classical
  exact fun A =>
    (Fintype.card L.Edge : ℝ)⁻¹ *
      ∑ target : L.Edge, L.singleLinkHeatBathProjection target f A

@[simp] theorem finite_oriented_randomScanHeatBathSweep_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) :
    L.randomScanHeatBathSweep f A =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge,
          L.singleLinkHeatBathProjection target f A := by
  rfl

/-- The orientation-correct random-scan sweep is symmetric for the finite
Gibbs pairing. -/
theorem finite_oriented_randomScanHeatBathSweep_gibbsPairing_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.randomScanHeatBathSweep f) g =
      L.gibbsPairingReal f (L.randomScanHeatBathSweep g) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.randomScanHeatBathSweep
  rw [finite_oriented_gibbsPairingReal_const_mul_left,
    finite_oriented_gibbsPairingReal_const_mul_right]
  have hSumF :
      (fun A : L.Configuration =>
        ∑ target : L.Edge,
          L.singleLinkHeatBathProjection target f A) =
        ∑ target : L.Edge,
          L.singleLinkHeatBathProjection target f := by
    funext A
    simp
  have hSumG :
      (fun A : L.Configuration =>
        ∑ target : L.Edge,
          L.singleLinkHeatBathProjection target g A) =
        ∑ target : L.Edge,
          L.singleLinkHeatBathProjection target g := by
    funext A
    simp
  rw [hSumF, hSumG,
    finite_oriented_gibbsPairingReal_finset_sum_left,
    finite_oriented_gibbsPairingReal_finset_sum_right]
  apply congrArg (fun x : ℝ => (Fintype.card L.Edge : ℝ)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro target _hTarget
  exact finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
    L target f g

/-- Local orientation-correct heat-bath fluctuation `Q_e = I - P_e`. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuation
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f : L.Configuration → ℝ) : L.Configuration → ℝ :=
  f - L.singleLinkHeatBathProjection target f

/-- Observable orientation-correct heat-bath Hamiltonian `sum_e (I - P_e)`. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathHamiltonianObservable
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : L.Configuration → ℝ := by
  classical
  exact ∑ target : L.Edge, L.singleLinkHeatBathFluctuation target f

/-- Every local orientation-correct fluctuation is Gibbs-pairing symmetric. -/
theorem finite_oriented_singleLinkHeatBathFluctuation_gibbsPairing_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.singleLinkHeatBathFluctuation target f) g =
      L.gibbsPairingReal f (L.singleLinkHeatBathFluctuation target g) := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuation
  rw [finite_oriented_gibbsPairingReal_sub_left,
    finite_oriented_gibbsPairingReal_sub_right,
    finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm]

/-- The orientation-correct observable heat-bath Hamiltonian is symmetric for
the finite Gibbs pairing. -/
theorem finite_oriented_singleLinkHeatBathHamiltonianObservable_gibbsPairing_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.singleLinkHeatBathHamiltonianObservable f) g =
      L.gibbsPairingReal f (L.singleLinkHeatBathHamiltonianObservable g) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathHamiltonianObservable
  rw [finite_oriented_gibbsPairingReal_finset_sum_left,
    finite_oriented_gibbsPairingReal_finset_sum_right]
  apply Finset.sum_congr rfl
  intro target _hTarget
  exact finite_oriented_singleLinkHeatBathFluctuation_gibbsPairing_symm
    L target f g

/-- Exact operator relation between the unnormalized oriented heat-bath
Hamiltonian and the normalized random-scan sweep. -/
theorem finite_oriented_singleLinkHeatBathHamiltonianObservable_eq_card_mul_one_sub_randomScan
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathHamiltonianObservable f =
      fun A => (Fintype.card L.Edge : ℝ) *
        (f A - L.randomScanHeatBathSweep f A) := by
  classical
  funext A
  have hCard : (Fintype.card L.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathHamiltonianObservable
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuation
    FiniteOrientedLatticeWilsonSystem.randomScanHeatBathSweep
  simp only [Finset.sum_apply, Pi.sub_apply]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp [hCard]
  simp [Finset.card_univ, mul_comm]

end
end MathlibAnalytic
end MGAP4D
