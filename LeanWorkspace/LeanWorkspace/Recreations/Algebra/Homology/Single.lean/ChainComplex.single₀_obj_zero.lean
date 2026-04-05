import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem single₀_obj_zero (A : V) :
    ((single₀ V).obj A).X 0 = A := rfl

