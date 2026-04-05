import Mathlib

variable {ι α β : Type*}

variable [AddCommMonoid α] [LinearOrder α] [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]
  [PosSMulReflectLE α β] [FloorDiv α β] [CeilDiv α β] {a : α} {b : β}

theorem floorDiv_le_ceilDiv : b ⌊/⌋ a ≤ b ⌈/⌉ a := by
  obtain ha | ha := le_or_gt a 0
  · simp [ha]
  · exact le_of_smul_le_smul_left ((smul_floorDiv_le ha).trans <| le_smul_ceilDiv ha) ha

