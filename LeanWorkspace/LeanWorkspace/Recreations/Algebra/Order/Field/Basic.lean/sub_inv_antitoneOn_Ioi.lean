import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem sub_inv_antitoneOn_Ioi :
    AntitoneOn (fun x ↦ (x - c)⁻¹) (Set.Ioi c) := antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab ↦
    inv_le_inv₀ (sub_pos.mpr hb) (sub_pos.mpr ha) |>.mpr <| sub_le_sub (le_of_lt hab) le_rfl

