import Mathlib

variable {α : Type u} {β : Type v}

variable [Group α]

theorem isConj_iff {a b : α} : IsConj a b ↔ ∃ c : α, c * a * c⁻¹ = b := ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_cancel c, inv_mul_cancel c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

