import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTimeReflection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The fixed color set used to split positive links on an even periodic
four-dimensional lattice.  A color records the coordinate direction and the
checkerboard parity of the source vertex.  Hence there are exactly `4 * 2 = 8`
colors, independently of the lattice size. -/
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

/-- A unit shift changes exactly the selected coordinate parity. -/
@[simp]
theorem periodicHypercubicEvenCoordinateParity_shift
    (H : ℕ) (x : PeriodicHypercubicEvenVertex H)
    (mu i : PeriodicHypercubicAxis) :
    periodicHypercubicEvenCoordinateParity H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) x mu) i =
      periodicHypercubicEvenCoordinateParity H x i +
        if i = mu then 1 else 0 := by
  simp [periodicHypercubicEvenCoordinateParity,
    periodicHypercubicEvenParityHom,
    periodicHypercubicShift_apply]

/-- Checkerboard parity of a periodic vertex: the sum modulo two of all four
coordinate parities. -/
def periodicHypercubicEvenCheckerboardParity
    (H : ℕ) (x : PeriodicHypercubicEvenVertex H) : ZMod 2 :=
  ∑ i : PeriodicHypercubicAxis,
    periodicHypercubicEvenCoordinateParity H x i

/-- Every positive unit shift flips checkerboard parity, regardless of the
coordinate direction.  This is the stronger parity fact needed to separate not
only incident links but also opposite parallel links in one plaquette. -/
@[simp]
theorem periodicHypercubicEvenCheckerboardParity_shift
    (H : ℕ) (x : PeriodicHypercubicEvenVertex H)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicEvenCheckerboardParity H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) x mu) =
      periodicHypercubicEvenCheckerboardParity H x + 1 := by
  unfold periodicHypercubicEvenCheckerboardParity
  simp_rw [periodicHypercubicEvenCoordinateParity_shift]
  rw [Finset.sum_add_distrib]
  simp

/-- A positive unit shift never preserves checkerboard parity. -/
theorem periodicHypercubicEvenCheckerboardParity_shift_ne
    (H : ℕ) (x : PeriodicHypercubicEvenVertex H)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicEvenCheckerboardParity H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) x mu) ≠
      periodicHypercubicEvenCheckerboardParity H x := by
  rw [periodicHypercubicEvenCheckerboardParity_shift]
  intro h
  have h10 : (1 : ZMod 2) = 0 := by
    calc
      1 =
          (periodicHypercubicEvenCheckerboardParity H x + 1) -
            periodicHypercubicEvenCheckerboardParity H x := by abel
      _ = periodicHypercubicEvenCheckerboardParity H x -
            periodicHypercubicEvenCheckerboardParity H x := by rw [h]
      _ = 0 := sub_self _
  exact one_ne_zero h10

/-- The canonical fixed eight-color assignment for positive physical links.
The checkerboard parity, rather than only the parity in the link direction, is
what makes same-colored links conflict-free for local plaquette interactions. -/
def periodicHypercubicEvenEdgeColor
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    PeriodicHypercubicEvenEdgeColor :=
  (e.2, periodicHypercubicEvenCheckerboardParity H e.1)

@[simp]
theorem periodicHypercubicEvenEdgeColor_axis
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicEvenEdgeColor H e).1 = e.2 :=
  rfl

@[simp]
theorem periodicHypercubicEvenEdgeColor_parity
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicEvenEdgeColor H e).2 =
      periodicHypercubicEvenCheckerboardParity H e.1 :=
  rfl

/-- The color set has fixed cardinality eight, with no volume dependence. -/
theorem periodicHypercubicEvenEdgeColor_card :
    Fintype.card PeriodicHypercubicEvenEdgeColor = 8 := by
  simp [PeriodicHypercubicEvenEdgeColor]

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

/-- Same-colored links have the same source checkerboard parity. -/
theorem periodicHypercubicEvenEdge_parity_eq_of_color_eq
    (H : ℕ) {e f : PeriodicHypercubicEvenEdge H}
    (hColor : periodicHypercubicEvenEdgeColor H e =
      periodicHypercubicEvenEdgeColor H f) :
    periodicHypercubicEvenCheckerboardParity H e.1 =
      periodicHypercubicEvenCheckerboardParity H f.1 :=
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
      periodicHypercubicEvenCheckerboardParity H e.1 =
        periodicHypercubicEvenCheckerboardParity H f.1 :=
    periodicHypercubicEvenEdge_parity_eq_of_color_eq H hColor
  intro hst
  have hx :
      e.1 = periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) f.1 e.2 := by
    simpa [periodicHypercubicEdgeSource, periodicHypercubicEdgeTarget, hdir] using hst
  have hcross := congrArg
    (periodicHypercubicEvenCheckerboardParity H) hx
  have hbaseShift :
      periodicHypercubicEvenCheckerboardParity H f.1 =
        periodicHypercubicEvenCheckerboardParity H
          (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) f.1 e.2) :=
    hparity.symm.trans hcross
  exact
    (periodicHypercubicEvenCheckerboardParity_shift_ne H f.1 e.2)
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
at one vertex must be the same link. -/
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

/-- The four physical links in every coordinate plaquette receive four distinct
colors.  Therefore a fixed color class contains at most one link from each
Wilson plaquette, which is the local conflict-freeness needed before proving
commutation/factorization of same-color heat-bath updates. -/
theorem periodicHypercubicEvenPlaquette_boundaryEdgeColor_injective
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    Function.Injective
      (fun k : Fin 4 =>
        periodicHypercubicEvenEdgeColor H
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge) := by
  have haxes :
      periodicHypercubicPlaquetteFirstAxis p ≠
        periodicHypercubicPlaquetteSecondAxis p :=
    periodicHypercubicPlaquette_axes_ne p
  have haxes' :
      periodicHypercubicPlaquetteSecondAxis p ≠
        periodicHypercubicPlaquetteFirstAxis p :=
    haxes.symm
  have hshiftFirst :=
    periodicHypercubicEvenCheckerboardParity_shift_ne H p.1
      (periodicHypercubicPlaquetteFirstAxis p)
  have hshiftSecond :=
    periodicHypercubicEvenCheckerboardParity_shift_ne H p.1
      (periodicHypercubicPlaquetteSecondAxis p)
  have hshiftFirst' := hshiftFirst.symm
  have hshiftSecond' := hshiftSecond.symm
  intro k l hkl
  fin_cases k <;> fin_cases l <;>
    simp_all [periodicHypercubicEvenEdgeColor]

end

end MathlibAnalytic
end MGAP4D
