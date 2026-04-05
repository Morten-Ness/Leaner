import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem univ_mul (ht : t.Nonempty) : (univ : Set α) * t = univ := let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, trivial, a, ha, inv_mul_cancel_right ..⟩

