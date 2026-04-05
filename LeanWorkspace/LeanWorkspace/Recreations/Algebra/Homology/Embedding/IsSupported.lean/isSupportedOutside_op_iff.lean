import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

theorem isSupportedOutside_op_iff :
    K.op.IsSupportedOutside e.op ↔ K.IsSupportedOutside e := ⟨fun h ↦ ⟨fun i ↦ (h.exactAt i).unop⟩, fun h ↦ ⟨fun i ↦ (h.exactAt i).op⟩⟩

