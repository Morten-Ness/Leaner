import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

theorem quotient_map_eq_zero_iff {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (HomotopyCategory.quotient V c).map f = 0 ↔ Nonempty (Homotopy f 0) := ⟨fun h ↦ ⟨HomotopyCategory.homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using HomotopyCategory.eq_of_homotopy _ _ h⟩

