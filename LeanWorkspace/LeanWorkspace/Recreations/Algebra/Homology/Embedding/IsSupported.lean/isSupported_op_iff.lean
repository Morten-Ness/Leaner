import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

theorem isSupported_op_iff :
    K.op.IsSupported e.op ↔ K.IsSupported e := ⟨fun _ ↦ ⟨fun i' hi' ↦ (K.HomologicalComplex.exactAt_of_isSupported op e.op i' hi').unop⟩,
    fun _ ↦ ⟨fun i' hi' ↦ (K.exactAt_of_isSupported e i' hi').op⟩⟩

