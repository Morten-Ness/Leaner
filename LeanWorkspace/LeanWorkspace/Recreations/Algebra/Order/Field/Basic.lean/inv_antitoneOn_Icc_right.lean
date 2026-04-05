import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem inv_antitoneOn_Icc_right (ha : 0 < a) :
    AntitoneOn (fun x : α ↦ x⁻¹) (Set.Icc a b) := by
  convert sub_inv_antitoneOn_Icc_right ha
  exact (sub_zero _).symm

