import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingWilsonBoltzmannProduct

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- In the canonical ordered axis pair of a plaquette, the second axis can
never be the Euclidean-time axis `0`. -/
theorem periodicHypercubicPlaquetteSecondAxis_ne_zero
    {n : ℕ}
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteSecondAxis p ≠ 0 := by
  intro hzero
  have hlt : periodicHypercubicPlaquetteFirstAxis p <
      periodicHypercubicPlaquetteSecondAxis p := p.2.2
  rw [hzero] at hlt
  exact (Fin.not_lt_zero _) hlt

/-- Because coordinate-plane labels are ordered, a plaquette contains the time
direction exactly when its first axis is `0`. -/
theorem periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenPlaquetteHasTimeDirection p ↔
      periodicHypercubicPlaquetteFirstAxis p = 0 := by
  unfold periodicHypercubicEvenPlaquetteHasTimeDirection
  constructor
  · rintro (hfirst | hsecond)
    · exact hfirst
    · exact
        (periodicHypercubicPlaquetteSecondAxis_ne_zero p hsecond).elim
  · intro hfirst
    exact Or.inl hfirst

/-- Every temporal crossing plaquette has time as its first axis. -/
theorem periodicHypercubicEvenTemporalCrossingPlaquette_firstAxis_zero
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenTemporalCrossingPlaquette p) :
    periodicHypercubicPlaquetteFirstAxis p = 0 :=
  (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1 hp.2

/-- The second axis of a temporal crossing plaquette is spatial. -/
theorem periodicHypercubicEvenTemporalCrossingPlaquette_secondAxis_ne_zero
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (_hp : periodicHypercubicEvenTemporalCrossingPlaquette p) :
    periodicHypercubicPlaquetteSecondAxis p ≠ 0 :=
  periodicHypercubicPlaquetteSecondAxis_ne_zero p

/-- The first shifted corner of a time-containing plaquette is one time step
after its base. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenPlaquetteCorner10 p 0 = p.1 0 + 1 := by
  have hfirst :=
    (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1
      htime
  simp [periodicHypercubicEvenPlaquetteCorner10,
    periodicHypercubicShift_apply, hfirst]

/-- The spatially shifted corner of a time-containing plaquette has the same
time coordinate as its base. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteCorner01_time_of_hasTimeDirection
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (_htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenPlaquetteCorner01 p 0 = p.1 0 := by
  have hsecond := periodicHypercubicPlaquetteSecondAxis_ne_zero p
  have hzeroSecond : (0 : PeriodicHypercubicAxis) ≠
      periodicHypercubicPlaquetteSecondAxis p := Ne.symm hsecond
  simp [periodicHypercubicEvenPlaquetteCorner01,
    periodicHypercubicShift_apply, hzeroSecond]

/-- The doubly shifted corner of a time-containing plaquette is one time step
after its base. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteCorner11_time_of_hasTimeDirection
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenPlaquetteCorner11 p 0 = p.1 0 + 1 := by
  have hfirst :=
    (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1
      htime
  have hsecond := periodicHypercubicPlaquetteSecondAxis_ne_zero p
  have hzeroSecond : (0 : PeriodicHypercubicAxis) ≠
      periodicHypercubicPlaquetteSecondAxis p := Ne.symm hsecond
  simp [periodicHypercubicEvenPlaquetteCorner11,
    periodicHypercubicEvenPlaquetteCorner10,
    periodicHypercubicShift_apply, hfirst, hzeroSecond]

/-- Every vertex of a temporal crossing plaquette lies on one of the two
adjacent time slices determined by the base time. -/
theorem periodicHypercubicEvenTemporalCrossingPlaquette_vertex_time_eq_base_or_next
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenTemporalCrossingPlaquette p)
    (v : PeriodicHypercubicEvenVertex H)
    (hv : v ∈ periodicHypercubicEvenPlaquetteVertices p) :
    v 0 = p.1 0 ∨ v 0 = p.1 0 + 1 := by
  have htime : periodicHypercubicEvenPlaquetteHasTimeDirection p := hp.2
  simp [periodicHypercubicEvenPlaquetteVertices] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr
      (periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
        p htime)
  · exact Or.inr
      (periodicHypercubicEvenPlaquetteCorner11_time_of_hasTimeDirection
        p htime)
  · exact Or.inl
      (periodicHypercubicEvenPlaquetteCorner01_time_of_hasTimeDirection
        p htime)

end

end MathlibAnalytic
end MGAP4D
