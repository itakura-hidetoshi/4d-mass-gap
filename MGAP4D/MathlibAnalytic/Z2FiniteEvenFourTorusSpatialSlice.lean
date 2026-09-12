import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricTimeTranslation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Vertices of the canonical time-zero spatial slice of the even four-torus. -/
abbrev FiniteEvenFourTorusSpatialVertex (H : ℕ) : Type :=
  {v : FiniteEvenFourTorusVertex H // v 0 = 0}

/-- The three non-time directions of the four-dimensional torus. -/
abbrev FiniteEvenFourTorusSpatialDirection : Type :=
  {μ : Fin 4 // μ ≠ 0}

/-- A positively oriented spatial link on the canonical time-zero slice. -/
abbrev FiniteEvenFourTorusSpatialLink (H : ℕ) : Type :=
  FiniteEvenFourTorusSpatialVertex H × FiniteEvenFourTorusSpatialDirection

/-- A spatial slice gauge configuration. -/
abbrev FiniteEvenFourTorusZ2SliceConfiguration (H : ℕ) : Type :=
  FiniteEvenFourTorusSpatialLink H → Z2Gauge

/-- Spatial unit translation preserves the time-zero slice. -/
def finiteEvenFourTorusSpatialVertexStep
    (H : ℕ)
    (v : FiniteEvenFourTorusSpatialVertex H)
    (μ : FiniteEvenFourTorusSpatialDirection) :
    FiniteEvenFourTorusSpatialVertex H :=
  ⟨finiteFourTorusStep (2 * H + 1) v.1 μ.1, by
    have h0μ : (0 : Fin 4) ≠ μ.1 := Ne.symm μ.2
    simp [finiteFourTorusStep, finiteFourTorusUnitStep, v.2, h0μ]⟩

@[simp] theorem finiteEvenFourTorusSpatialVertexStep_coe
    (H : ℕ)
    (v : FiniteEvenFourTorusSpatialVertex H)
    (μ : FiniteEvenFourTorusSpatialDirection) :
    (finiteEvenFourTorusSpatialVertexStep H v μ).1 =
      finiteFourTorusStep (2 * H + 1) v.1 μ.1 :=
  rfl

/-- The actual four-torus directed edge represented by one spatial link. -/
def finiteEvenFourTorusSpatialLinkEdge
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    FiniteEvenFourTorusEdge H :=
  (e.1.1, (finiteEvenFourTorusSpatialVertexStep H e.1 e.2).1)

/-- Ordered pairs of distinct spatial directions. -/
abbrev FiniteEvenFourTorusSpatialDirectionPair : Type :=
  {d : FiniteEvenFourTorusSpatialDirection ×
      FiniteEvenFourTorusSpatialDirection // d.1 ≠ d.2}

/-- Spatial plaquettes on the canonical time-zero slice. -/
abbrev FiniteEvenFourTorusSpatialPlaquette (H : ℕ) : Type :=
  FiniteEvenFourTorusSpatialVertex H ×
    FiniteEvenFourTorusSpatialDirectionPair

/-- The actual four-torus plaquette represented by a spatial slice plaquette. -/
def finiteEvenFourTorusSpatialPlaquetteEmbedding
    (H : ℕ)
    (p : FiniteEvenFourTorusSpatialPlaquette H) :
    FiniteFourTorusPlaquette (2 * H + 1) :=
  (p.1.1, ⟨(p.2.1.1.1, p.2.1.2.1), by
    intro h
    apply p.2.2
    apply Subtype.ext
    exact h⟩)

/-- Four-link Wilson holonomy of a spatial slice plaquette. -/
def finiteEvenFourTorusZ2SpatialPlaquetteHolonomy
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (p : FiniteEvenFourTorusSpatialPlaquette H) : Z2Gauge :=
  let v := p.1
  let μ := p.2.1.1
  let ν := p.2.1.2
  A (v, μ) *
    A (finiteEvenFourTorusSpatialVertexStep H v μ, ν) *
    (A (finiteEvenFourTorusSpatialVertexStep H v ν, μ))⁻¹ *
    (A (v, ν))⁻¹

/-- Spatial Wilson energy on one time slice. -/
def finiteEvenFourTorusZ2SpatialWilsonAction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  ∑ p : FiniteEvenFourTorusSpatialPlaquette H,
    if finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p = 1 then
      energyIdentity
    else
      energyNontrivial

/-- Half of the spatial Wilson Boltzmann amplitude assigned to each end of a
symmetric one-slab transfer kernel. -/
def finiteEvenFourTorusZ2SpatialHalfWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  Real.exp
    (-(β / 2) *
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A)

/-- Spatial half-weights are strictly positive. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeight_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2SpatialHalfWeight
      H β energyIdentity energyNontrivial A :=
  Real.exp_pos _

/-- The one-step geometric time translation identifies the canonical spatial
slice with the next slice at time one. -/
def finiteEvenFourTorusSpatialLinkTimeTranslation
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    FiniteEvenFourTorusEdge H :=
  finiteEvenFourTorusEdgeTimeTranslationEquiv H
    (finiteEvenFourTorusSpatialLinkEdge H e)

end

end MathlibAnalytic
end MGAP4D
