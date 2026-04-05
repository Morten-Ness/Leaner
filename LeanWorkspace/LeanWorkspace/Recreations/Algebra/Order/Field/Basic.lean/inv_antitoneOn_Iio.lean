import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem inv_antitoneOn_Iio :
    AntitoneOn (fun x : α ↦ x⁻¹) (Set.Iio 0) := by
  convert sub_inv_antitoneOn_Iio (α := α)
  exact (sub_zero _).symm

