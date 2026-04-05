import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem sub_inv_antitoneOn_Icc_left (ha : b < c) :
    AntitoneOn (fun x ↦ (x - c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact sub_inv_antitoneOn_Iio.mono <| (Set.Icc_subset_Iio_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

