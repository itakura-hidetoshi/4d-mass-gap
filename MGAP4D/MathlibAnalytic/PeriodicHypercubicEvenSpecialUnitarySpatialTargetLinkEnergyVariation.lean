import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- An intrinsic spatial-slice plaquette touches a spatial link when the link is
one of the plaquette's four boundary links. -/
def periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Prop :=
  target = (p.1, p.2.1.1) ∨
    target = (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1, p.2.1.2) ∨
    target = (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2, p.2.1.1) ∨
    target = (p.1, p.2.1.2)

/-- RED specification: updating one spatial target link changes the spatial
Wilson action only through plaquettes whose intrinsic boundary contains that
link. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_update_sub_eq_targetTouching
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (Function.update A target g) -
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A =
    ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      if periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target then
        specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update A target g) p) -
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)
      else 0 := by
  classical
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
    periodicHypercubicEvenSpatialSlicePlaquetteList,
    periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink]

end

end MathlibAnalytic
end MGAP4D
