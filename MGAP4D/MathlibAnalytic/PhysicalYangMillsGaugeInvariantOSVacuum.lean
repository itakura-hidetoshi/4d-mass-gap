import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSHilbertCompletion

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

protected def Carrier.one (P : D.OSPreHilbertData) : P.Carrier where
  observable := 1
  gaugeInvariant :=
    (physicalYangMillsGaugeInvariantObservableSubalgebra S).one_mem
  positiveTime := by
    change (1 : physicalYangMillsGaugeInvariantObservableSubalgebra S) ∈
      D.positiveTimeSubalgebra
    exact D.positiveTimeSubalgebra.one_mem

def vacuumObservable (P : D.OSPreHilbertData) : P.Carrier :=
  Carrier.one P

@[simp] theorem inner_physicalState_physicalState
    (P : D.OSPreHilbertData) (F G : P.Carrier) :
    inner ℝ (P.physicalState F) (P.physicalState G) = inner ℝ F G := by
  change inner ℝ
      ((P.osClass F : UniformSpace.Completion P.Separated))
      ((P.osClass G : UniformSpace.Completion P.Separated)) = inner ℝ F G
  rw [UniformSpace.Completion.inner_coe]
  change inner ℝ (SeparationQuotient.mk F) (SeparationQuotient.mk G) =
    inner ℝ F G
  exact SeparationQuotient.inner_mk_mk F G

@[simp] theorem norm_physicalState
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    ‖P.physicalState F‖ = ‖F‖ := by
  have hsq : ‖P.physicalState F‖ ^ 2 = ‖F‖ ^ 2 := by
    calc
      ‖P.physicalState F‖ ^ 2 =
          inner ℝ (P.physicalState F) (P.physicalState F) := by
            symm
            exact real_inner_self_eq_norm_sq _
      _ = inner ℝ F F := P.inner_physicalState_physicalState F F
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
  nlinarith [norm_nonneg (P.physicalState F), norm_nonneg F]

theorem inner_vacuumObservable_self_eq_state_one
    (P : D.OSPreHilbertData) :
    inner ℝ P.vacuumObservable P.vacuumObservable = P.omega 1 := by
  rw [P.inner_eq_osBilinForm, D.osBilinForm_apply]
  change P.omega
      (D.reflection
          (1 : physicalYangMillsGaugeInvariantObservableSubalgebra S) * 1) =
    P.omega 1
  simp

def vacuum (P : D.OSPreHilbertData) : P.PhysicalHilbert :=
  P.physicalState P.vacuumObservable

def IsNormalized (P : D.OSPreHilbertData) : Prop :=
  P.omega 1 = 1

@[simp] theorem norm_vacuum
    (P : D.OSPreHilbertData) (hP : P.IsNormalized) :
    ‖P.vacuum‖ = 1 := by
  have hinner : inner ℝ P.vacuum P.vacuum = 1 := by
    change inner ℝ
        (P.physicalState P.vacuumObservable)
        (P.physicalState P.vacuumObservable) = 1
    rw [P.inner_physicalState_physicalState,
      P.inner_vacuumObservable_self_eq_state_one]
    exact hP
  have hsq : ‖P.vacuum‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hinner
  nlinarith [norm_nonneg P.vacuum]

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
