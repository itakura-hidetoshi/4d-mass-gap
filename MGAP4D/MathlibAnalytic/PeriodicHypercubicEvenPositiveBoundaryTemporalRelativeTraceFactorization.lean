import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalExactEdgePattern
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceCyclic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Boundary leg selected by a positive-boundary temporal plaquette.  On the
primary side (`base time = 0`) the fixed incidence is step `3`; on the
antipodal-adjacent positive side it is step `1`.  The inverse is chosen so
that the cyclically rotated plaquette trace is a relative-trace kernel
`tr_norm(g⁻¹ h)`. -/
def periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg
    {H N : ℕ}
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  if (p.1 0).val = 0 then
    (periodicHypercubicStepValue A
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p 3))⁻¹
  else
    (periodicHypercubicStepValue A
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p 1))⁻¹

/-- The complementary cyclic three-edge path of a positive-boundary temporal
plaquette.  Once the exact edge pattern is known, these are precisely the
three positive-half incidences. -/
def periodicHypercubicEvenPositiveBoundaryTemporalOpenPath
    {H N : ℕ}
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  if (p.1 0).val = 0 then
    periodicHypercubicStepValue A
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 0) *
      periodicHypercubicStepValue A
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 1) *
      periodicHypercubicStepValue A
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 2)
  else
    periodicHypercubicStepValue A
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 2) *
      periodicHypercubicStepValue A
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 3) *
      periodicHypercubicStepValue A
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 0)

/-- Exact one-plaquette relative-trace factorization.  For `H > 0`, the exact
edge-pattern theorem identifies the first argument as the unique fixed
boundary leg and the second argument as the cyclic product of the three
positive-half incidences.

Thus every positive-boundary temporal Wilson trace is literally the same
`SU(N)` normalized relative-trace kernel already used by the tensor/Fock
feature construction. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporal_normalizedTrace_eq_relativeKernel
    {H N : ℕ}
    (hH : 0 < H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    normalizedSpecialUnitaryRealTrace N
        (periodicHypercubicPlaquetteHolonomy A p) =
      specialUnitaryNormalizedTraceRelativeKernel N
        (periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg A p)
        (periodicHypercubicEvenPositiveBoundaryTemporalOpenPath A p) := by
  rcases hp.2 with hbase0 | hbaseH
  · have hcycle := normalizedSpecialUnitaryRealTrace_mul_cycle
      (N := N)
      (periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 0) *
        periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 1) *
        periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 2))
      (periodicHypercubicStepValue A
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 3))
    simpa [periodicHypercubicPlaquetteHolonomy,
      specialUnitaryNormalizedTraceRelativeKernel,
      periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg,
      periodicHypercubicEvenPositiveBoundaryTemporalOpenPath,
      hbase0, mul_assoc] using hcycle
  · have hbaseNe : (p.1 0).val ≠ 0 := by
      omega
    have hcycle := normalizedSpecialUnitaryRealTrace_mul_cycle
      (N := N)
      (periodicHypercubicStepValue A
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 0))
      (periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 1) *
        periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 2) *
        periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 3))
    simpa [periodicHypercubicPlaquetteHolonomy,
      specialUnitaryNormalizedTraceRelativeKernel,
      periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg,
      periodicHypercubicEvenPositiveBoundaryTemporalOpenPath,
      hbaseNe, mul_assoc] using hcycle

/-- The geometric meaning of the factorization: in the nondegenerate case the
chosen boundary-leg incidence is exactly the unique fixed incidence, while all
three incidences entering the open path are positive. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporal_relativeTraceFactorization_edge_receipt
    {H : ℕ}
    (hH : 0 < H)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    ∃! k : Fin 4,
      (periodicHypercubicEvenEdgeOrbitPartition H).side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
        ReflectionEdgeSide.fixed :=
  periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_existsUnique_fixed_step
    hH p hp

end

end MathlibAnalytic
end MGAP4D
