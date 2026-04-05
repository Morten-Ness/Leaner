import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem inv_antitoneOn_Icc_left (hb : b < 0) :
    AntitoneOn (fun x : α ↦ x⁻¹) (Set.Icc a b) := by
  convert sub_inv_antitoneOn_Icc_left hb
  exact (sub_zero _).symm

