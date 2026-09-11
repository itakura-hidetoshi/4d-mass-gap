import MGAP4D.MathlibAnalytic.FiniteProductKernelCouplingVariation
import MGAP4D.MathlibAnalytic.FiniteProductDoobParallelVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteKernelGroundStateDoobData

variable {ι G : Type}
  [DecidableEq ι]
  [Fintype ι]
  [Fintype G]
  [Nonempty G]

/-- The generic finite-product kernel observable map specialized to the Doob
kernel is exactly the ordinary-observable Doob map. -/
theorem doobObservableLinearMap_eq_finiteProductKernelObservableLinearMap
    (D : FiniteKernelGroundStateDoobData (ι → G)) :
    D.doobObservableLinearMap =
      finiteProductKernelObservableLinearMap D.doobKernel := by
  ext f A
  rfl

end FiniteKernelGroundStateDoobData

/-- Coordinate-coupling data for a ground-state Doob kernel automatically
produces the direct parallel Doob variation certificate consumed by the
weighted spectral package. -/
noncomputable def
    FiniteProductKernelCouplingVariationData.toDoobParallelVariationCertificate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductKernelCouplingVariationData D.doobKernel) :
    FiniteProductDoobParallelVariationCertificate D :=
  { variationData := by
      rw [D.doobObservableLinearMap_eq_finiteProductKernelObservableLinearMap]
      exact C.toParallelVariationMatrixData }

/-- The coupling coefficient is retained exactly by the conversion to the
parallel Doob variation certificate. -/
@[simp] theorem
    FiniteProductKernelCouplingVariationData.toDoobParallelVariationCertificate_coefficient
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductKernelCouplingVariationData D.doobKernel) :
    (C.toDoobParallelVariationCertificate D).variationData.coefficient =
      C.coefficient := by
  rfl

/-- The strict coupling column-sum bound is therefore the strict parallel Doob
variation rate bound. -/
theorem finiteProductDoob_parallel_rate_lt_one_of_coupling
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductKernelCouplingVariationData D.doobKernel) :
    (C.toDoobParallelVariationCertificate D).variationData.coefficient < 1 := by
  simpa using C.coefficient_lt_one

end

end MathlibAnalytic
end MGAP4D
