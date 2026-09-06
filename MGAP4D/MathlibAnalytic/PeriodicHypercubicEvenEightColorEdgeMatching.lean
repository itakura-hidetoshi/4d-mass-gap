import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTimeReflection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The fixed color set used to split positive links on an even periodic
four-dimensional lattice.  A color records the coordinate direction and the
parity of the source coordinate in that direction.  Hence there are exactly
`4 * 2 = 8` colors, independently of the lattice size. -/
abbrev PeriodicHypercubicEvenEdgeColor : Type :=
  PeriodicHypercubicAxis × ZMod 2

/-- Reduction of an even-torus coordinate modulo two.  The map is well defined
because `2` divides the even side length `2(H+1)`. -/
def periodicHypercubicEvenParityHom (H : ℕ) :
    ZMod (PeriodicHypercubicEvenSideLength H) →+* ZMod 2 :=
  ZMod.castHom (by simp [PeriodicHypercubicEvenSideLength]) (ZMod 2)

/-- Parity of one coordinate of an even periodic vertex. -/
def periodicHypercubicEvenCoordinateParity
    (H : ℕ) (x : PeriodicHypercubicEvenVertex H)
    (mu : PeriodicHypercubicAxis) : ZMod 2 :=
  periodicHypercubicEvenParityHom H (x mu)

/-- The canonical fixed eight-color assignment for positive physical links. -/
def periodicHypercubicEvenEdgeColor
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    PeriodicHypercubicEvenEdgeColor :=
  (e.2, periodicHypercubicEvenCoordinateParity H e.1 e.2)

@[simp]
theorem periodicHypercubicEvenEdgeColor_axis
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicEvenEdgeColor H e).1 = e.2 :=
  rfl

@[simp]
theorem periodicHypercubicEvenEdgeColor_parity
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicEvenEdgeColor H e).2 =
      periodicHypercubicEvenCoordinateParity H e.1 e.2 :=
  rfl

/-- The color set has fixed cardinality eight, with no volume dependence. -/
theorem periodicHypercubicEvenEdgeColor_card :
    Fintype.card PeriodicHypercubicEvenEdgeColor = 8 := by
  simp [PeriodicHypercubicEvenEdgeColor]

/-- A positive unit shift flips the parity of the shifted coordinate. -/
@[simp]
theorem periodicHypercubicEvenCoordinateParity_shift_same
    (H : ℕ) (x : PeriodicHypercubicEvenVertex H)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicEvenCoordinateParity H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) x mu) mu =
      periodicHypercubicEvenCoordinateParity H x mu + 1 := by
  simp [periodicHypercubicEvenCoordinateParity,
    periodicHypercubicEvenParityHom,
    periodicHypercubicShift_apply]

/-- In particular, a positive unit shift never preserves the parity of the
shifted coordinate. -/
theorem periodicHypercubicEvenCoordinateParity_shift_ne
    (H : ℕ) (x : PeriodicHypercubicEvenVertex H)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicEvenCoordinateParity H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) x mu) mu ≠
      periodicHypercubicEvenCoordinateParity H x mu := by
  rw [periodicHypercubicEvenCoordinateParity_shift_same]
  intro h
  have h10 : (1 : ZMod 2) = 0 := by
    calc
      1 =
          (periodicHypercubicEvenCoordinateParity H x mu + 1) -
            periodicHypercubicEvenCoordinateParity H x mu := by abel
      _ = periodicHypercubicEvenCoordinateParity H x mu -
            periodicHypercubicEvenCoordinateParity H x mu := by rw [h]
      _ = 0 := sub_self _
  exact one_ne_zero h10

/-- Incidence of a vertex with a positive physical link, forgetting traversal
orientation. -/
def periodicHypercubicEvenEdgeIncidentAt
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H)
    (v : PeriodicHypercubicEvenVertex H) : Prop :=
  periodicHypercubicEdgeSource (PeriodicHypercubicEvenSideLength H) e = v ∨
    periodicHypercubicEdgeTarget (PeriodicHypercubicEvenSideLength H) e = v

/-- Same-colored links have the same coordinate direction. -/
theorem periodicHypercubicEvenEdge_direction_eq_of_color_eq
    (H : ℕ) {e f : PeriodicHypercubicEvenEdge H}
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f) :
    e.2 = f.2 :=
  congrArg Prod.fst hColor

/-- Same-colored links have the same source-coordinate parity in their common
direction. -/
theorem periodicHypercubicEvenEdge_parity_eq_of_color_eq
    (H : ℕ) {e f : PeriodicHypercubicEvenEdge H}
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f) :
    periodicHypercubicEvenCoordinateParity H e.1 e.2 =
      periodicHypercubicEvenCoordinateParity H f.1 f.2 :=
  congrArg Prod.snd hColor

/-- Two same-colored links cannot have the source of one equal to the target of
the other.  This is the parity obstruction that makes each color class a
matching. -/
theorem periodicHypercubicEvenEdge_source_ne_target_of_color_eq
    (H : ℕ) {e f : PeriodicHypercubicEvenEdge H}
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f) :
    periodicHypercubicEdgeSource (PeriodicHypercubicEvenSideLength H) e ≠
      periodicHypercubicEdgeTarget (PeriodicHypercubicEvenSideLength H) f := by
  have hdir : e.2 = f.2 :=
    periodicHypercubicEvenEdge_direction_eq_of_color_eq H hColor
  have hparity :
      periodicHypercubicEvenCoordinateParity H e.1 e.2 =
        periodicHypercubicEvenCoordinateParity H f.1 f.2 :=
    periodicHypercubicEvenEdge_parity_eq_of_color_eq H hColor
  intro hst
  have hx :
      e.1 = periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) f.1 e.2 := by
    simpa [periodicHypercubicEdgeSource, periodicHypercubicEdgeTarget, hdir] using hst
  have hcross := congrArg
    (fun x : PeriodicHypercubicEvenVertex H =>
      periodicHypercubicEvenCoordinateParity H x e.2) hx
  have hsame :
      periodicHypercubicEvenCoordinateParity H e.1 e.2 =
        periodicHypercubicEvenCoordinateParity H f.1 e.2 := by
    simpa [hdir] using hparity
  have hbaseShift :
      periodicHypercubicEvenCoordinateParity H f.1 e.2 =
        periodicHypercubicEvenCoordinateParity H
          (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) f.1 e.2) e.2 :=
    hsame.symm.trans hcross
  exact
    (periodicHypercubicEvenCoordinateParity_shift_ne H f.1 e.2)
      hbaseShift.symm

/-- If same-colored links have the same source, then they are the same physical
link. -/
theorem periodicHypercubicEvenEdge_eq_of_color_eq_of_source_eq
    (H : ℕ) {e f : PeriodicHypercubicEvenEdge H}
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f)
    (hSource :
      periodicHypercubicEdgeSource (PeriodicHypercubicEvenSideLength H) e =
        periodicHypercubicEdgeSource (PeriodicHypercubicEvenSideLength H) f) :
    e = f := by
  have hdir : e.2 = f.2 :=
    periodicHypercubicEvenEdge_direction_eq_of_color_eq H hColor
  have hbase : e.1 = f.1 := by
    simpa [periodicHypercubicEdgeSource] using hSource
  exact Prod.ext hbase hdir

/-- If same-colored links have the same target, then they are the same physical
link. -/
theorem periodicHypercubicEvenEdge_eq_of_color_eq_of_target_eq
    (H : ℕ) {e f : PeriodicHypercubicEvenEdge H}
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f)
    (hTarget :
      periodicHypercubicEdgeTarget (PeriodicHypercubicEvenSideLength H) e =
        periodicHypercubicEdgeTarget (PeriodicHypercubicEvenSideLength H) f) :
    e = f := by
  have hdir : e.2 = f.2 :=
    periodicHypercubicEvenEdge_direction_eq_of_color_eq H hColor
  have hshift :
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) e.1 e.2 =
        periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) f.1 e.2 := by
    simpa [periodicHypercubicEdgeTarget, hdir] using hTarget
  have hunshift := congrArg
    (fun x : PeriodicHypercubicEvenVertex H =>
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H) x e.2)
    hshift
  have hbase : e.1 = f.1 := by
    simpa using hunshift
  exact Prod.ext hbase hdir

/-- Each fixed color class is a matching: two links of the same color incident
at one vertex must be the same link.  This is the finite-volume geometric input
needed for a parallel block update with a number of colors bounded uniformly by
`8`, rather than a random scan over all links. -/
theorem periodicHypercubicEvenEdge_sameColor_incident_unique
    (H : ℕ) {e f : PeriodicHypercubicEvenEdge H}
    {v : PeriodicHypercubicEvenVertex H}
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f)
    (he : periodicHypercubicEvenEdgeIncidentAt H e v)
    (hf : periodicHypercubicEvenEdgeIncidentAt H f v) :
    e = f := by
  rcases he with heSource | heTarget
  · rcases hf with hfSource | hfTarget
    · apply periodicHypercubicEvenEdge_eq_of_color_eq_of_source_eq H hColor
      exact heSource.trans hfSource.symm
    · exact False.elim
        ((periodicHypercubicEvenEdge_source_ne_target_of_color_eq H hColor)
          (heSource.trans hfTarget.symm))
  · rcases hf with hfSource | hfTarget
    · exact False.elim
        ((periodicHypercubicEvenEdge_source_ne_target_of_color_eq H hColor.symm)
          (hfSource.trans heTarget.symm))
    · apply periodicHypercubicEvenEdge_eq_of_color_eq_of_target_eq H hColor
      exact heTarget.trans hfTarget.symm

end

end MathlibAnalytic
end MGAP4D
