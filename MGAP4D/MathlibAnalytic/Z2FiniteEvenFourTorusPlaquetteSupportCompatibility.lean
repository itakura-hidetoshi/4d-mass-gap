import MGAP4D.MathlibAnalytic.Z2FiniteInvolutivePlaquetteGeometricSidePartition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Time reflection commutes with a spatial unit step. -/
@[simp]
theorem finiteEvenFourTorusTimeReflection_step_spatial
    (H : ℕ) (v : FiniteEvenFourTorusVertex H)
    {μ : Fin 4} (hμ : μ ≠ 0) :
    finiteEvenFourTorusTimeReflection H
        (finiteFourTorusStep (2 * H + 1) v μ) =
      finiteFourTorusStep (2 * H + 1)
        (finiteEvenFourTorusTimeReflection H v) μ := by
  have h0μ : (0 : Fin 4) ≠ μ := Ne.symm hμ
  funext i
  by_cases hi : i = 0
  · subst i
    simp [finiteEvenFourTorusTimeReflection,
      finiteFourTorusStep, finiteFourTorusUnitStep, h0μ]
  · simp [finiteEvenFourTorusTimeReflection,
      finiteFourTorusStep, finiteFourTorusUnitStep, hi]

/-- Time reflection turns a positive time step into subtraction of the time
unit vector. -/
@[simp]
theorem finiteEvenFourTorusTimeReflection_step_time
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteEvenFourTorusTimeReflection H
        (finiteFourTorusStep (2 * H + 1) v 0) =
      finiteEvenFourTorusTimeReflection H v -
        finiteFourTorusUnitStep (2 * H + 1) 0 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [finiteEvenFourTorusTimeReflection,
      finiteFourTorusStep, finiteFourTorusUnitStep]
    ring
  · simp [finiteEvenFourTorusTimeReflection,
      finiteFourTorusStep, finiteFourTorusUnitStep, hi]

/-- A backward time shift followed by a positive time step cancels. -/
@[simp]
theorem finiteFourTorusStep_sub_timeStep_cancel
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteFourTorusStep (2 * H + 1)
        (v - finiteFourTorusUnitStep (2 * H + 1) 0) 0 = v := by
  simpa [finiteFourTorusStep] using
    sub_add_cancel v (finiteFourTorusUnitStep (2 * H + 1) 0)

/-- A positive time step followed by subtraction of the time unit vector
cancels. -/
@[simp]
theorem finiteFourTorusStep_time_sub_timeStep_cancel
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteFourTorusStep (2 * H + 1) v 0 -
        finiteFourTorusUnitStep (2 * H + 1) 0 = v := by
  simpa [finiteFourTorusStep] using
    add_sub_cancel_right v (finiteFourTorusUnitStep (2 * H + 1) 0)

/-- Unit translations in distinct or equal directions commute. -/
theorem finiteFourTorusStep_comm
    (N : ℕ) (v : FiniteFourTorusVertex N) (μ ν : Fin 4) :
    finiteFourTorusStep N (finiteFourTorusStep N v μ) ν =
      finiteFourTorusStep N (finiteFourTorusStep N v ν) μ := by
  simp [finiteFourTorusStep, add_comm, add_left_comm]

/-- Spatial translation commutes with subtracting the time unit vector. -/
theorem finiteFourTorusStep_sub_timeStep
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) (μ : Fin 4) :
    finiteFourTorusStep (2 * H + 1)
        (v - finiteFourTorusUnitStep (2 * H + 1) 0) μ =
      finiteFourTorusStep (2 * H + 1) v μ -
        finiteFourTorusUnitStep (2 * H + 1) 0 := by
  unfold finiteFourTorusStep
  abel

/-- The reflected concrete plaquette has exactly the time-reflected vertex
support of the original plaquette, up to ordering. -/
theorem finiteEvenFourTorusPlaquetteReflection_vertices_mem_iff
    (H : ℕ) (p : FiniteEvenFourTorusPlaquette H)
    (v : FiniteEvenFourTorusVertex H) :
    v ∈ finiteFourTorusPlaquetteVertices
        (finiteEvenFourTorusPlaquetteReflection H p) ↔
      v ∈ finiteEvenFourTorusPlaquetteReflectedVertices p := by
  classical
  rcases p with ⟨base, ⟨⟨μ, ν⟩, hμν⟩⟩
  by_cases hμ : μ = 0
  · subst μ
    have hν : ν ≠ 0 := by
      intro hν0
      apply hμν
      simpa [hν0]
    simp [finiteFourTorusPlaquetteVertices,
      finiteFourTorusPlaquetteCorner00,
      finiteFourTorusPlaquetteCorner10,
      finiteFourTorusPlaquetteCorner11,
      finiteFourTorusPlaquetteCorner01,
      finiteFourTorusPlaquetteBase,
      finiteFourTorusPlaquetteFirstDirection,
      finiteFourTorusPlaquetteSecondDirection,
      finiteEvenFourTorusPlaquetteReflectedVertices,
      finiteEvenFourTorusReflectVertexSupport,
      finiteEvenFourTorusPlaquetteReflection,
      finiteEvenFourTorusReflectedPlaquetteBase,
      finiteEvenFourTorusPlaquetteHasTimeDirection,
      hν,
      finiteEvenFourTorusTimeReflection_step_spatial,
      finiteEvenFourTorusTimeReflection_step_time,
      finiteFourTorusStep_sub_timeStep_cancel,
      finiteFourTorusStep_time_sub_timeStep_cancel,
      finiteFourTorusStep_sub_timeStep,
      finiteFourTorusStep_comm,
      or_assoc, or_left_comm, or_comm]
  · by_cases hν : ν = 0
    · subst ν
      simp [finiteFourTorusPlaquetteVertices,
        finiteFourTorusPlaquetteCorner00,
        finiteFourTorusPlaquetteCorner10,
        finiteFourTorusPlaquetteCorner11,
        finiteFourTorusPlaquetteCorner01,
        finiteFourTorusPlaquetteBase,
        finiteFourTorusPlaquetteFirstDirection,
        finiteFourTorusPlaquetteSecondDirection,
        finiteEvenFourTorusPlaquetteReflectedVertices,
        finiteEvenFourTorusReflectVertexSupport,
        finiteEvenFourTorusPlaquetteReflection,
        finiteEvenFourTorusReflectedPlaquetteBase,
        finiteEvenFourTorusPlaquetteHasTimeDirection,
        hμ,
        finiteEvenFourTorusTimeReflection_step_spatial,
        finiteEvenFourTorusTimeReflection_step_time,
        finiteFourTorusStep_sub_timeStep_cancel,
        finiteFourTorusStep_time_sub_timeStep_cancel,
        finiteFourTorusStep_sub_timeStep,
        finiteFourTorusStep_comm,
        or_assoc, or_left_comm, or_comm]
    · simp [finiteFourTorusPlaquetteVertices,
        finiteFourTorusPlaquetteCorner00,
        finiteFourTorusPlaquetteCorner10,
        finiteFourTorusPlaquetteCorner11,
        finiteFourTorusPlaquetteCorner01,
        finiteFourTorusPlaquetteBase,
        finiteFourTorusPlaquetteFirstDirection,
        finiteFourTorusPlaquetteSecondDirection,
        finiteEvenFourTorusPlaquetteReflectedVertices,
        finiteEvenFourTorusReflectVertexSupport,
        finiteEvenFourTorusPlaquetteReflection,
        finiteEvenFourTorusReflectedPlaquetteBase,
        finiteEvenFourTorusPlaquetteHasTimeDirection,
        hμ, hν,
        finiteEvenFourTorusTimeReflection_step_spatial,
        finiteFourTorusStep_comm,
        or_assoc, or_left_comm, or_comm]

/-- The concrete support compatibility certificate is theorem-generated;
fixed reflection orbits are handled internally by the geometric classifier. -/
def finiteEvenFourTorusPlaquetteSupportReflectionCompatibility
    (H : ℕ) :
    FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H :=
  { vertices_reflection_mem :=
      finiteEvenFourTorusPlaquetteReflection_vertices_mem_iff H }

/-- Fully concrete geometric plaquette side partition on the even four-torus. -/
def finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition
    (H : ℕ) :
    FiniteInvolutivePlaquetteGeometricSidePartition
      (FiniteEvenFourTorusPlaquette H) :=
  finiteEvenFourTorusGeometricPlaquetteSidePartition H
    (finiteEvenFourTorusPlaquetteSupportReflectionCompatibility H)

/-- The concrete geometric side classifier exchanges positive and negative
plaquettes and preserves crossing plaquettes under reflection. -/
@[simp]
theorem finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition_side_reflection
    (H : ℕ) (p : FiniteEvenFourTorusPlaquette H) :
    (finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition H).side
        (finiteEvenFourTorusPlaquetteReflection H p) =
      match
        (finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition H).side p with
      | .positive => .negative
      | .crossing => .crossing
      | .negative => .positive := by
  exact
    FiniteInvolutivePlaquetteGeometricSidePartition.side_reflection
      (finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition H) p

end

end MathlibAnalytic
end MGAP4D
