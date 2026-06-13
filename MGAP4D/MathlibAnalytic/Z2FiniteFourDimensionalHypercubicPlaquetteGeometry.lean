import MGAP4D.MathlibAnalytic.Z2FiniteFourDimensionalWilsonTimeReflectionGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The time increment of a positive unit step in a four-dimensional lattice
direction.  Direction `0` is Euclidean time; directions `1,2,3` are spatial. -/
def fourDimensionalTimeStep (μ : Fin 4) : ℤ :=
  if μ = 0 then 1 else 0

/-- Time coordinates of the four ordered corners of a positively oriented
hypercubic plaquette with base time `t` and directions `μ,ν`. -/
def hypercubicPlaquetteTimes (t : ℤ) (μ ν : Fin 4) : List ℤ :=
  [t,
    t + fourDimensionalTimeStep μ,
    t + fourDimensionalTimeStep μ + fourDimensionalTimeStep ν,
    t + fourDimensionalTimeStep ν]

/-- Classification of a finite time support relative to the reflection plane
`t = 0`. -/
def reflectionTimeSupportSide (times : List ℤ) : ReflectionPlaquetteSide := by
  classical
  exact
    if ∀ t ∈ times, 0 < t then
      .positive
    else if ∀ t ∈ times, t < 0 then
      .negative
    else
      .crossing

/-- Hypercubic plaquette classification generated from its base time and two
lattice directions. -/
def hypercubicPlaquetteSide
    (t : ℤ) (μ ν : Fin 4) : ReflectionPlaquetteSide :=
  reflectionTimeSupportSide (hypercubicPlaquetteTimes t μ ν)

@[simp]
theorem fourDimensionalTimeStep_zero :
    fourDimensionalTimeStep (0 : Fin 4) = 1 := by
  simp [fourDimensionalTimeStep]

@[simp]
theorem fourDimensionalTimeStep_of_ne_zero
    {μ : Fin 4} (hμ : μ ≠ 0) :
    fourDimensionalTimeStep μ = 0 := by
  simp [fourDimensionalTimeStep, hμ]

/-- A spatial plaquette has constant time on all four corners. -/
theorem hypercubicPlaquetteTimes_of_spatial
    (t : ℤ) {μ ν : Fin 4}
    (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    hypercubicPlaquetteTimes t μ ν = [t, t, t, t] := by
  simp [hypercubicPlaquetteTimes, fourDimensionalTimeStep, hμ, hν]

/-- A time-space plaquette with time direction first occupies the two adjacent
time slices `t` and `t+1`. -/
theorem hypercubicPlaquetteTimes_time_first
    (t : ℤ) {ν : Fin 4} (hν : ν ≠ 0) :
    hypercubicPlaquetteTimes t 0 ν = [t, t + 1, t + 1, t] := by
  simp [hypercubicPlaquetteTimes, fourDimensionalTimeStep, hν]

/-- A time-space plaquette with time direction second occupies the same two
adjacent time slices. -/
theorem hypercubicPlaquetteTimes_time_second
    (t : ℤ) {μ : Fin 4} (hμ : μ ≠ 0) :
    hypercubicPlaquetteTimes t μ 0 = [t, t, t + 1, t + 1] := by
  simp [hypercubicPlaquetteTimes, fourDimensionalTimeStep, hμ]

/-- A spatial plaquette at strictly positive time lies on the positive side. -/
theorem hypercubicPlaquetteSide_spatial_positive
    {t : ℤ} {μ ν : Fin 4}
    (ht : 0 < t) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    hypercubicPlaquetteSide t μ ν = .positive := by
  rw [hypercubicPlaquetteSide,
    hypercubicPlaquetteTimes_of_spatial t hμ hν]
  simp [reflectionTimeSupportSide, ht]

/-- A spatial plaquette at strictly negative time lies on the negative side. -/
theorem hypercubicPlaquetteSide_spatial_negative
    {t : ℤ} {μ ν : Fin 4}
    (ht : t < 0) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    hypercubicPlaquetteSide t μ ν = .negative := by
  rw [hypercubicPlaquetteSide,
    hypercubicPlaquetteTimes_of_spatial t hμ hν]
  simp [reflectionTimeSupportSide, ht, not_lt_of_ge ht.le]

/-- A time-space plaquette based at time `-1` crosses the reflection plane. -/
theorem hypercubicPlaquetteSide_time_first_neg_one
    {ν : Fin 4} (hν : ν ≠ 0) :
    hypercubicPlaquetteSide (-1) 0 ν = .crossing := by
  rw [hypercubicPlaquetteSide,
    hypercubicPlaquetteTimes_time_first (-1) hν]
  norm_num [reflectionTimeSupportSide]

/-- The same crossing result with the time direction listed second. -/
theorem hypercubicPlaquetteSide_time_second_neg_one
    {μ : Fin 4} (hμ : μ ≠ 0) :
    hypercubicPlaquetteSide (-1) μ 0 = .crossing := by
  rw [hypercubicPlaquetteSide,
    hypercubicPlaquetteTimes_time_second (-1) hμ]
  norm_num [reflectionTimeSupportSide]

/-- A time-space plaquette based at the reflection slice also belongs to the
crossing sector under the strict positive/negative convention. -/
theorem hypercubicPlaquetteSide_time_first_zero
    {ν : Fin 4} (hν : ν ≠ 0) :
    hypercubicPlaquetteSide 0 0 ν = .crossing := by
  rw [hypercubicPlaquetteSide,
    hypercubicPlaquetteTimes_time_first 0 hν]
  norm_num [reflectionTimeSupportSide]

/-- The same reflection-slice result with time direction second. -/
theorem hypercubicPlaquetteSide_time_second_zero
    {μ : Fin 4} (hμ : μ ≠ 0) :
    hypercubicPlaquetteSide 0 μ 0 = .crossing := by
  rw [hypercubicPlaquetteSide,
    hypercubicPlaquetteTimes_time_second 0 hμ]
  norm_num [reflectionTimeSupportSide]

/-- Hypercubic coordinate data attached to every plaquette of an existing
finite Wilson system.  The field `plaquette_time_support` is the concrete
coordinate calculation connecting the abstract vertex support to the standard
four-corner hypercubic pattern. -/
structure FiniteFourDimensionalHypercubicPlaquetteGeometry
    (L : FiniteLatticeWilsonSystem) where
  geometry : FiniteFourDimensionalWilsonGeometry L
  baseTime : L.Plaquette → ℤ
  firstDirection : L.Plaquette → Fin 4
  secondDirection : L.Plaquette → Fin 4
  directions_ne : ∀ p, firstDirection p ≠ secondDirection p
  plaquette_time_support :
    ∀ p,
      (geometry.plaquetteVertices p).map geometry.timeCoordinate =
        hypercubicPlaquetteTimes
          (baseTime p) (firstDirection p) (secondDirection p)

/-- The abstract vertex-support classifier agrees with the explicit hypercubic
base-time/direction classifier. -/
theorem FiniteFourDimensionalHypercubicPlaquetteGeometry.plaquetteSide_eq
    {L : FiniteLatticeWilsonSystem}
    (H : FiniteFourDimensionalHypercubicPlaquetteGeometry L)
    (p : L.Plaquette) :
    H.geometry.plaquetteSide p =
      hypercubicPlaquetteSide
        (H.baseTime p) (H.firstDirection p) (H.secondDirection p) := by
  classical
  have hPositive :
      (∀ v ∈ H.geometry.plaquetteVertices p,
          0 < H.geometry.timeCoordinate v) ↔
        ∀ t ∈ hypercubicPlaquetteTimes
          (H.baseTime p) (H.firstDirection p) (H.secondDirection p),
          0 < t := by
    rw [← H.plaquette_time_support p]
    simp
  have hNegative :
      (∀ v ∈ H.geometry.plaquetteVertices p,
          H.geometry.timeCoordinate v < 0) ↔
        ∀ t ∈ hypercubicPlaquetteTimes
          (H.baseTime p) (H.firstDirection p) (H.secondDirection p),
          t < 0 := by
    rw [← H.plaquette_time_support p]
    simp
  unfold FiniteFourDimensionalWilsonGeometry.plaquetteSide
    hypercubicPlaquetteSide reflectionTimeSupportSide
  rw [hPositive, hNegative]

end

end MathlibAnalytic
end MGAP4D
