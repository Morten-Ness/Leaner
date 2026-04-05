import Mathlib

section

variable {A M G α β γ : Type*}

theorem sigmaCongrRightHom_injective {α : Type*} {β : α → Type*} :
    Function.Injective (Equiv.Perm.sigmaCongrRightHom β) := by
  intro x y h
  ext a b
  simpa using Equiv.congr_fun h ⟨a, b⟩

end

section

variable {A M G α β γ : Type*}

theorem subtypeCongrHom_injective (p : α → Prop) [DecidablePred p] :
    Function.Injective (Equiv.Perm.subtypeCongrHom p) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i

end

section

variable {A M G α β γ : Type*}

theorem sumCongrHom_injective {α β : Type*} : Function.Injective (Equiv.Perm.sumCongrHom α β) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
  · simpa using Equiv.congr_fun h (Sum.inr i)

end

section

variable {A M G α β γ : Type*}

theorem zpow_apply_comm {α : Type*} (σ : Equiv.Perm α) (m n : ℤ) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, zpow_mul_comm]

end
