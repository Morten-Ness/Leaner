import Mathlib

section

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

variable [AddCommMonoid M]

theorem sum_translate [Fintype G] (a : G) (f : G → M) : ∑ b, τ a f b = ∑ b, f b := Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

end

section

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_comm (a b : G) (f : G → α) : τ a (τ b f) = τ b (τ a f) := by
  rw [← translate_add, translate_add']

-- We make `simp` push the `τ` outside

end

section

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_eq_domAddActMk_vadd (a : G) (f : G → α) : τ a f = DomAddAct.mk (-a) +ᵥ f := by
  ext; simp [DomAddAct.vadd_apply, sub_eq_neg_add]

end
