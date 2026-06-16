import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

theorem finite_sum_rewrite
    {A M : Type*} [Fintype A] [AddCommMonoid M]
    {u v : A -> M} (h : u = v) :
    Finset.univ.sum u = Finset.univ.sum v :=
  congrArg (fun w : A -> M => Finset.univ.sum w) h

end MathlibAnalytic
end MGAP4D
