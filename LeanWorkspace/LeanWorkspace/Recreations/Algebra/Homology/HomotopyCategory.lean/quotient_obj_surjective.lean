import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

theorem quotient_obj_surjective (X : HomotopyCategory V c) :
    ∃ (K : HomologicalComplex V c), (HomotopyCategory.quotient _ _).obj K = X := ⟨_, rfl⟩

-- Not `@[simp]` because it hinders the automatic application of the more useful `quotient_map_out`

