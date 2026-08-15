import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Topology

noncomputable section

/-- On the canonical projective continuum carrier, restriction to any finite
set of Euclidean points is a continuous map for the product topology.  Thus a
finite cylinder readback does not require an additional global continuity
hypothesis once the physical carrier is chosen to be the projective Pi-space. -/
theorem euclidean_yang_mills_projective_finiteRestriction_continuous
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    [∀ x, TopologicalSpace (F.fieldValue x)]
    (J : Finset EuclideanFourSpace) :
    Continuous (fun A : F.Configuration => J.restrict A) := by
  fun_prop

/-- The finite restriction as a canonical Mathlib continuous map. -/
noncomputable def euclideanYangMillsProjectiveFiniteRestrictionContinuousMap
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    [∀ x, TopologicalSpace (F.fieldValue x)]
    (J : Finset EuclideanFourSpace) :
    C(F.Configuration, (∀ x : J, F.fieldValue x)) :=
  ⟨fun A => J.restrict A,
    euclidean_yang_mills_projective_finiteRestriction_continuous F J⟩

/-- Any continuous decoder of finitely many projective coordinates therefore
produces a continuous continuum cylinder coordinate by composition.  This is
the reusable topology layer needed by the actual Wilson positive-half readback:
only the finite decoder remains model-specific. -/
theorem euclidean_yang_mills_projective_finiteCylinderCoordinate_continuous
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    [∀ x, TopologicalSpace (F.fieldValue x)]
    (J : Finset EuclideanFourSpace)
    {Y : Type}
    [TopologicalSpace Y]
    (decode : (∀ x : J, F.fieldValue x) → Y)
    (hdecode : Continuous decode) :
    Continuous (fun A : F.Configuration => decode (J.restrict A)) := by
  exact hdecode.comp
    (euclidean_yang_mills_projective_finiteRestriction_continuous F J)

end

end MathlibAnalytic
end MGAP4D
