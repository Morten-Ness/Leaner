import Mathlib

variable (C : Type*) [Category* C]

variable {C} [Preadditive C]

theorem acyclic_op {K : CochainComplex C ℤ} (hK : K.Acyclic) :
   ((CochainComplex.opEquivalence C).functor.obj (op K)).Acyclic := fun n ↦ CochainComplex.exactAt_op (hK (-n)) n

