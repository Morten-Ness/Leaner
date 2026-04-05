import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem sub_inv_antitoneOn_Iio :
    AntitoneOn (fun x ↦ (x - c)⁻¹) (Set.Iio c) := antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab ↦
    inv_le_inv_of_neg (sub_neg.mpr hb) (sub_neg.mpr ha) |>.mpr <| sub_le_sub (le_of_lt hab) le_rfl

