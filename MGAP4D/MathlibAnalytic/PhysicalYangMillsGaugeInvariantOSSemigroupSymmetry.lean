import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableStrongContinuity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianSelfAdjoint
import Mathlib.Tactic
import Mathlib.Topology.Sequences

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PhysicalSemigroup

/-- Every completed Euclidean-time operator is symmetric for the physical real
inner product. -/
def IsInnerSymmetric (T : P.PhysicalSemigroup) : Prop :=
  ∀ t psi phi,
    inner ℝ (T.operator t psi) phi =
      inner ℝ psi (T.operator t phi)

end PhysicalSemigroup

namespace PositiveTimeObservableContractionSemigroup

/-- The remaining observable-side Osterwalder--Schrader exchange identity.

It states that positive Euclidean-time translation can be moved from the first
to the second entry of the reflected OS form.  In a concrete reconstruction this
is the point where reflection and time translation must be exchanged. -/
def ReflectionTimeTranslationExchange
    (T : P.PositiveTimeObservableContractionSemigroup) : Prop :=
  ∀ t F G,
    D.osBilinForm P.omega
        (P.toPositiveTime (T.carrierTranslation t F))
        (P.toPositiveTime G) =
      D.osBilinForm P.omega
        (P.toPositiveTime F)
        (P.toPositiveTime (T.carrierTranslation t G))

/-- The observable-side reflection/time-translation exchange identity is exactly
symmetry of carrier translation for the OS inner product. -/
theorem ReflectionTimeTranslationExchange.carrierTranslation_inner_eq
    {T : P.PositiveTimeObservableContractionSemigroup}
    (hT : T.ReflectionTimeTranslationExchange)
    (t : NNReal) (F G : P.Carrier) :
    inner ℝ (T.carrierTranslation t F) G =
      inner ℝ F (T.carrierTranslation t G) := by
  rw [P.inner_eq_osBilinForm, P.inner_eq_osBilinForm]
  exact hT t F G

/-- Symmetry on represented observable states extends uniquely to the completed
physical Hilbert space by density and continuity. -/
theorem ReflectionTimeTranslationExchange.toPhysicalSemigroup_isInnerSymmetric
    {T : P.PositiveTimeObservableContractionSemigroup}
    (hT : T.ReflectionTimeTranslationExchange) :
    T.toPhysicalSemigroup.IsInnerSymmetric := by
  intro t psi phi
  refine P.physicalStateLinearMap_denseRange.induction_on₂ ?_ ?_ psi phi
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F G
    change
      inner ℝ
          (T.toCarrierSemigroup.physicalOperator t (P.physicalState F))
          (P.physicalState G) =
        inner ℝ
          (P.physicalState F)
          (T.toCarrierSemigroup.physicalOperator t (P.physicalState G))
    rw [T.toCarrierSemigroup.physicalOperator_on_physicalState,
      T.toCarrierSemigroup.physicalOperator_on_physicalState,
      P.inner_physicalState_physicalState,
      P.inner_physicalState_physicalState]
    exact hT.carrierTranslation_inner_eq t F G

/-- The canonical strongly continuous completion retains the inner-product
symmetry obtained from the observable OS exchange identity. -/
theorem ReflectionTimeTranslationExchange.toStronglyContinuousPhysicalSemigroup_isInnerSymmetric
    {T : P.PositiveTimeObservableContractionSemigroup}
    (hT : T.ReflectionTimeTranslationExchange)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    (T.toStronglyContinuousPhysicalSemigroup hContinuous).toPhysicalSemigroup.IsInnerSymmetric := by
  simpa only [StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup_toPhysicalSemigroup]
    using hT.toPhysicalSemigroup_isInnerSymmetric

end PositiveTimeObservableContractionSemigroup

namespace StronglyContinuousPhysicalSemigroup

/-- Symmetry of the completed semigroup passes to every positive-time right
difference quotient. -/
theorem rightDifferenceQuotient_inner_eq_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi phi : P.PhysicalHilbert) :
    inner ℝ (T.rightDifferenceQuotient psi t) phi =
      inner ℝ psi (T.rightDifferenceQuotient phi t) := by
  simp only [rightDifferenceQuotient, inner_smul_left, inner_sub_left,
    inner_smul_right, inner_sub_right, RingHom.id_apply]
  rw [hSymmetric t psi phi]

/-- The right infinitesimal generator of a symmetric Euclidean contraction
semigroup is formally symmetric on its canonical right-generator domain.

Its sign is nonpositive, but it is symmetric rather than skew-symmetric. -/
theorem rightGeneratorLinearPMap_isFormalAdjoint_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.rightGeneratorLinearPMap.IsFormalAdjoint
      T.rightGeneratorLinearPMap := by
  intro psi phi
  change
    inner ℝ (T.rightGenerator psi) (phi : P.PhysicalHilbert) =
      inner ℝ (psi : P.PhysicalHilbert) (T.rightGenerator phi)
  have hpsi := T.rightGenerator_hasRightGeneratorValue psi
  have hphi := T.rightGenerator_hasRightGeneratorValue phi
  unfold HasRightGeneratorValue at hpsi hphi
  have hleft :
      Tendsto
        (fun t : NNReal =>
          inner ℝ (T.rightDifferenceQuotient (psi : P.PhysicalHilbert) t)
            (phi : P.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0))
        (nhds (inner ℝ (T.rightGenerator psi) (phi : P.PhysicalHilbert))) :=
    hpsi.inner tendsto_const_nhds
  have hright :
      Tendsto
        (fun t : NNReal =>
          inner ℝ (psi : P.PhysicalHilbert)
            (T.rightDifferenceQuotient (phi : P.PhysicalHilbert) t))
        (nhdsWithin 0 (Ioi 0))
        (nhds (inner ℝ (psi : P.PhysicalHilbert) (T.rightGenerator phi))) :=
    tendsto_const_nhds.inner hphi
  have hfunctions :
      (fun t : NNReal =>
        inner ℝ (T.rightDifferenceQuotient (psi : P.PhysicalHilbert) t)
          (phi : P.PhysicalHilbert)) =
      fun t : NNReal =>
        inner ℝ (psi : P.PhysicalHilbert)
          (T.rightDifferenceQuotient (phi : P.PhysicalHilbert) t) := by
    funext t
    exact T.rightDifferenceQuotient_inner_eq_of_innerSymmetric
      hSymmetric t psi phi
  rw [hfunctions] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The canonical right Hamiltonian is formally symmetric on its dense domain. -/
theorem rightHamiltonianLinearPMap_isFormalAdjoint_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.rightHamiltonianLinearPMap.IsFormalAdjoint
      T.rightHamiltonianLinearPMap := by
  intro psi phi
  simpa only [rightHamiltonianLinearPMap_apply, rightHamiltonian_apply,
    inner_neg_left, inner_neg_right] using
    T.rightGeneratorLinearPMap_isFormalAdjoint_of_innerSymmetric hSymmetric psi phi

/-- Formal symmetry is preserved by the canonical graph closure of a closable
partially defined operator on a real Hilbert space. -/
private theorem linearPMap_closure_isFormalAdjoint_of_isFormalAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H)
    (hClosable : LinearPMap.IsClosable A)
    (hSymmetric : A.IsFormalAdjoint A) :
    A.closure.IsFormalAdjoint A.closure := by
  intro x y
  have hxGraph : ((x : H), A.closure x) ∈ A.graph.topologicalClosure := by
    rw [hClosable.graph_closure_eq_closure_graph]
    exact A.closure.mem_graph x
  have hyGraph : ((y : H), A.closure y) ∈ A.graph.topologicalClosure := by
    rw [hClosable.graph_closure_eq_closure_graph]
    exact A.closure.mem_graph y
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hxGraph hyGraph
  rcases hxGraph with ⟨u, huGraph, hu⟩
  rcases hyGraph with ⟨v, hvGraph, hv⟩
  choose xu hxuBase hxuValue using fun n =>
    (LinearPMap.mem_graph_iff A).1 (huGraph n)
  choose yv hyvBase hyvValue using fun n =>
    (LinearPMap.mem_graph_iff A).1 (hvGraph n)
  have huFst : Tendsto (fun n => (u n).1) atTop (nhds (x : H)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto ((x : H), A.closure x)).comp hu
  have huSnd : Tendsto (fun n => (u n).2) atTop (nhds (A.closure x)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto ((x : H), A.closure x)).comp hu
  have hvFst : Tendsto (fun n => (v n).1) atTop (nhds (y : H)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto ((y : H), A.closure y)).comp hv
  have hvSnd : Tendsto (fun n => (v n).2) atTop (nhds (A.closure y)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto ((y : H), A.closure y)).comp hv
  have hxuBaseFunction :
      (fun n => (u n).1) = fun n => ((xu n : A.domain) : H) :=
    funext fun n => (hxuBase n).symm
  have hxuValueFunction :
      (fun n => (u n).2) = fun n => A (xu n) :=
    funext fun n => (hxuValue n).symm
  have hyvBaseFunction :
      (fun n => (v n).1) = fun n => ((yv n : A.domain) : H) :=
    funext fun n => (hyvBase n).symm
  have hyvValueFunction :
      (fun n => (v n).2) = fun n => A (yv n) :=
    funext fun n => (hyvValue n).symm
  rw [hxuBaseFunction] at huFst
  rw [hxuValueFunction] at huSnd
  rw [hyvBaseFunction] at hvFst
  rw [hyvValueFunction] at hvSnd
  have hleft :
      Tendsto
        (fun n => inner ℝ (A (xu n)) ((yv n : A.domain) : H))
        atTop
        (nhds (inner ℝ (A.closure x) (y : H))) :=
    huSnd.inner hvFst
  have hright :
      Tendsto
        (fun n => inner ℝ ((xu n : A.domain) : H) (A (yv n)))
        atTop
        (nhds (inner ℝ (x : H) (A.closure y))) :=
    huFst.inner hvSnd
  have hfunctions :
      (fun n => inner ℝ (A (xu n)) ((yv n : A.domain) : H)) =
        fun n => inner ℝ ((xu n : A.domain) : H) (A (yv n)) := by
    funext n
    exact hSymmetric (xu n) (yv n)
  rw [hfunctions] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The graph-closed right Hamiltonian is formally symmetric whenever the
completed Euclidean semigroup is inner-product symmetric. -/
theorem closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.closedRightHamiltonian.IsFormalAdjoint
      T.closedRightHamiltonian := by
  simpa only [closedRightHamiltonian] using
    linearPMap_closure_isFormalAdjoint_of_isFormalAdjoint
      T.rightHamiltonianLinearPMap
      T.rightHamiltonianLinearPMap_isClosable
      (T.rightHamiltonianLinearPMap_isFormalAdjoint_of_innerSymmetric hSymmetric)

/-- A symmetric completed Euclidean contraction semigroup therefore has a
self-adjoint nonnegative closed right Hamiltonian.  Positive-shift surjectivity
is supplied by the finite-time Laplace resolvent layer. -/
theorem closedRightHamiltonian_isSelfAdjoint_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    IsSelfAdjoint T.closedRightHamiltonian :=
  T.closedRightHamiltonian_isSelfAdjoint_of_isFormalAdjoint
    (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hSymmetric)

end StronglyContinuousPhysicalSemigroup

namespace PositiveTimeObservableContractionSemigroup

/-- The complete conditional OS reconstruction bridge: observable
reflection/time-translation exchange plus observable-state strong continuity
implies self-adjointness of the graph-closed physical Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint_of_reflectionTimeTranslationExchange
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hExchange : T.ReflectionTimeTranslationExchange)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (T.toStronglyContinuousPhysicalSemigroup hContinuous).closedRightHamiltonian := by
  apply StronglyContinuousPhysicalSemigroup.closedRightHamiltonian_isSelfAdjoint_of_innerSymmetric
  exact hExchange.toStronglyContinuousPhysicalSemigroup_isInnerSymmetric hContinuous

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
