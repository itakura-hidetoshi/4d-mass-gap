import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- In a periodic box of side at least two, the residue class of one is
nonzero. -/
theorem periodicHypercubic_zmod_one_ne_zero
    (n : ℕ) (hn : 2 ≤ n) :
    (1 : ZMod n) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  have hlt : 1 < n := by omega
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
  omega

/-- In a periodic box of side at least three, the residue class of two is
nonzero. -/
theorem periodicHypercubic_zmod_two_ne_zero
    (n : ℕ) (hn : 3 ≤ n) :
    (2 : ZMod n) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  have hlt : 2 < n := by omega
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
  omega

/-- For side length at least three, positive and negative unit displacements
are distinct. -/
theorem periodicHypercubic_zmod_one_ne_neg_one
    (n : ℕ) (hn : 3 ≤ n) :
    (1 : ZMod n) ≠ -1 := by
  intro h
  apply periodicHypercubic_zmod_two_ne_zero n hn
  calc
    (2 : ZMod n) = 1 + 1 := by norm_num
    _ = 1 + (-1) := congrArg (fun z : ZMod n => (1 : ZMod n) + z) h
    _ = 0 := by simp

/-- Coordinate unit vectors distinguish the four lattice axes once the side
length is at least two. -/
theorem periodicHypercubicUnit_injective
    (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (periodicHypercubicUnit n) := by
  intro mu nu hUnit
  by_contra hne
  have hcoord := congrFun hUnit mu
  have hOne := periodicHypercubic_zmod_one_ne_zero n hn
  simp [periodicHypercubicUnit, hne, hOne] at hcoord

/-- A positive unit translation is never the identity for side length at least
two. -/
theorem periodicHypercubicShift_ne_self
    (n : ℕ) (hn : 2 ≤ n)
    (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicShift n x mu ≠ x := by
  intro h
  have hcoord := congrFun h mu
  have hOne := periodicHypercubic_zmod_one_ne_zero n hn
  simp [periodicHypercubicShift, periodicHypercubicUnit, hOne] at hcoord

/-- A negative unit translation is never the identity for side length at least
two. -/
theorem periodicHypercubicUnshift_ne_self
    (n : ℕ) (hn : 2 ≤ n)
    (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicUnshift n x mu ≠ x := by
  intro h
  have hcoord := congrFun h mu
  have hOne := periodicHypercubic_zmod_one_ne_zero n hn
  simp [periodicHypercubicUnshift, periodicHypercubicUnit, hOne] at hcoord

/-- Positive translations of a fixed vertex recover their axis uniquely. -/
theorem periodicHypercubicShift_axis_injective
    (n : ℕ) (hn : 2 ≤ n)
    (x : PeriodicHypercubicVertex n) :
    Function.Injective (periodicHypercubicShift n x) := by
  intro mu nu h
  apply periodicHypercubicUnit_injective n hn
  unfold periodicHypercubicShift at h
  exact add_left_cancel h

/-- Negative translations of a fixed vertex recover their axis uniquely. -/
theorem periodicHypercubicUnshift_axis_injective
    (n : ℕ) (hn : 2 ≤ n)
    (x : PeriodicHypercubicVertex n) :
    Function.Injective (periodicHypercubicUnshift n x) := by
  intro mu nu h
  have hneg :
      -periodicHypercubicUnit n mu =
        -periodicHypercubicUnit n nu := by
    unfold periodicHypercubicUnshift at h
    simpa [sub_eq_add_neg] using add_left_cancel h
  exact periodicHypercubicUnit_injective n hn (neg_injective hneg)

/-- For side length at least three, no positive unit translate of a vertex is
a negative unit translate, even in a different coordinate direction. -/
theorem periodicHypercubicShift_ne_unshift
    (n : ℕ) (hn : 3 ≤ n)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis) :
    periodicHypercubicShift n x mu ≠
      periodicHypercubicUnshift n x nu := by
  intro h
  have hUnits :
      periodicHypercubicUnit n mu =
        -periodicHypercubicUnit n nu := by
    unfold periodicHypercubicShift periodicHypercubicUnshift at h
    simpa [sub_eq_add_neg] using add_left_cancel h
  by_cases hmn : mu = nu
  · subst nu
    have hcoord := congrFun hUnits mu
    exact periodicHypercubic_zmod_one_ne_neg_one n hn (by
      simpa [periodicHypercubicUnit] using hcoord)
  · have hcoord := congrFun hUnits mu
    have hOne := periodicHypercubic_zmod_one_ne_zero n (by omega)
    exact hOne (by
      simpa [periodicHypercubicUnit, hmn] using hcoord)

end

end MathlibAnalytic
end MGAP4D
