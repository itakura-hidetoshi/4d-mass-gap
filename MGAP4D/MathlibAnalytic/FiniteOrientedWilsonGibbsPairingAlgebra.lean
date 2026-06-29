import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathPythagorean

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Native Gibbs pairing is compatible with subtraction in the first slot. -/
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

/-- Native Gibbs pairing is compatible with subtraction in the second slot. -/
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

/-- Native Gibbs pairing commutes with a finite sum in the first slot. -/
theorem finite_oriented_gibbsPairingReal_finset_sum_left
    (L : FiniteOrientedLatticeWilsonSystem)
    {iota : Type*}
    (s : Finset iota)
    (F : iota → L.Configuration → ℝ)
    (g : L.Configuration → ℝ) :
    L.gibbsPairingReal (s.sum F) g =
      s.sum (fun i => L.gibbsPairingReal (F i) g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [FiniteOrientedLatticeWilsonSystem.gibbsPairingReal]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,
        finite_oriented_gibbsPairingReal_add_left,
        ih,
        Finset.sum_insert ha]

/-- Native Gibbs pairing commutes with a finite sum in the second slot. -/
theorem finite_oriented_gibbsPairingReal_finset_sum_right
    (L : FiniteOrientedLatticeWilsonSystem)
    {iota : Type*}
    (s : Finset iota)
    (f : L.Configuration → ℝ)
    (G : iota → L.Configuration → ℝ) :
    L.gibbsPairingReal f (s.sum G) =
      s.sum (fun i => L.gibbsPairingReal f (G i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [FiniteOrientedLatticeWilsonSystem.gibbsPairingReal]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,
        finite_oriented_gibbsPairingReal_add_right,
        ih,
        Finset.sum_insert ha]

end

end MathlibAnalytic
end MGAP4D
