import Mathlib

variable {A M G α β γ : Type*}

theorem sumCongr_inv {α β : Type*} (e : Equiv.Perm α) (f : Equiv.Perm β) :
    (sumCongr e f)⁻¹ = sumCongr e⁻¹ f⁻¹ := rfl

