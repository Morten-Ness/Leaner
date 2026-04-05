import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem inv_antitoneOn_Ioi :
    AntitoneOn (fun x : α ↦ x⁻¹) (Set.Ioi 0) := by
  convert sub_inv_antitoneOn_Ioi (α := α)
  exact (sub_zero _).symm

