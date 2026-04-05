import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem mul_univ (hs : s.Nonempty) : s * (univ : Set α) = univ := let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ * b, trivial, mul_inv_cancel_left ..⟩

