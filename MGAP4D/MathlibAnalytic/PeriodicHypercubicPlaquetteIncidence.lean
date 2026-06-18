import MGAP4D.MathlibAnalytic.PeriodicHypercubicSignedGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Periodic translation by one negative lattice unit. -/
def periodicHypercubicUnshift
    (n : ℕ) (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) : PeriodicHypercubicVertex n :=
  x - periodicHypercubicUnit n mu

@[simp] theorem periodicHypercubicShift_unshift
    (n : ℕ) (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicShift n (periodicHypercubicUnshift n x mu) mu = x := by
  unfold periodicHypercubicShift periodicHypercubicUnshift
  abel

@[simp] theorem periodicHypercubicUnshift_shift
    (n : ℕ) (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicUnshift n (periodicHypercubicShift n x mu) mu = x := by
  unfold periodicHypercubicShift periodicHypercubicUnshift
  abel

/-- The three axes transverse to a fixed four-dimensional axis. -/
abbrev PeriodicHypercubicOtherAxis (mu : PeriodicHypercubicAxis) : Type :=
  {nu : PeriodicHypercubicAxis // nu ≠ mu}

/-- There are exactly three transverse axes. -/
theorem periodicHypercubicOtherAxis_card
    (mu : PeriodicHypercubicAxis) :
    Fintype.card (PeriodicHypercubicOtherAxis mu) = 3 := by
  fin_cases mu <;> native_decide

/-- Canonically sort two distinct directions into a coordinate-plane label. -/
def periodicHypercubicAxisPairOfNe
    (mu nu : PeriodicHypercubicAxis) (hne : nu ≠ mu) :
    PeriodicHypercubicAxisPair := by
  by_cases hlt : mu < nu
  · exact ⟨(mu, nu), hlt⟩
  · exact ⟨(nu, mu), lt_of_le_of_ne (le_of_not_gt hlt) hne⟩

/-- One of the two plaquettes in the `mu`-`nu` plane incident to a link. -/
def periodicHypercubicIncidentPlaquette
    (n : ℕ) (e : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis e.2) (otherSide : Bool) :
    PeriodicHypercubicPlaquette n :=
  (if otherSide then periodicHypercubicUnshift n e.1 nu.1 else e.1,
    periodicHypercubicAxisPairOfNe e.2 nu.1 nu.2)

/-- The finite canonical family indexed by three transverse axes and two sides. -/
noncomputable def periodicHypercubicIncidentPlaquettes
    (n : ℕ) [NeZero n] (e : PeriodicHypercubicEdge n) :
    Finset (PeriodicHypercubicPlaquette n) := by
  classical
  exact Finset.univ.image fun data : PeriodicHypercubicOtherAxis e.2 × Bool =>
    periodicHypercubicIncidentPlaquette n e data.1 data.2

/-- At most `2 * (4 - 1) = 6` canonical coordinate plaquettes meet a link,
uniformly in the periodic volume. -/
theorem periodicHypercubicIncidentPlaquettes_card_le_six
    (n : ℕ) [NeZero n] (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicIncidentPlaquettes n e).card ≤ 6 := by
  classical
  unfold periodicHypercubicIncidentPlaquettes
  calc
    (Finset.univ.image fun data : PeriodicHypercubicOtherAxis e.2 × Bool =>
      periodicHypercubicIncidentPlaquette n e data.1 data.2).card ≤
        (Finset.univ : Finset (PeriodicHypercubicOtherAxis e.2 × Bool)).card :=
      Finset.card_image_le
    _ = Fintype.card (PeriodicHypercubicOtherAxis e.2 × Bool) := Finset.card_univ
    _ = 6 := by
      rw [Fintype.card_prod, periodicHypercubicOtherAxis_card]
      native_decide

end

end MathlibAnalytic
end MGAP4D
