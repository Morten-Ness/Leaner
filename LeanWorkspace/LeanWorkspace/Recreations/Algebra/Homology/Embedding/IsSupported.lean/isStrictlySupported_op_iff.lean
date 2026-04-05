import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

theorem isStrictlySupported_op_iff :
    K.op.IsStrictlySupported e.op ↔ K.IsStrictlySupported e := ⟨(fun _ ↦ ⟨fun i' hi' ↦ (K.HomologicalComplex.isZero_X_of_isStrictlySupported op e.op i' hi').unop⟩),
    (fun _ ↦ ⟨fun i' hi' ↦ (K.isZero_X_of_isStrictlySupported e i' hi').op⟩)⟩

