import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [CommGroup α] [MulLeftMono α]

theorem m_Birkhoff_inequalities (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)|ₘ ⊔ |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ := sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)

