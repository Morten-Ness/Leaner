import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

theorem isStrictlySupportedOutside_op_iff :
    K.op.IsStrictlySupportedOutside e.op ↔ K.IsStrictlySupportedOutside e := ⟨fun h ↦ ⟨fun i ↦ (h.isZero i).unop⟩, fun h ↦ ⟨fun i ↦ (h.isZero i).op⟩⟩

