import Mathlib

section

variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

theorem of_injective {f : F} (hf : Function.Injective f) [NeZero a] : NeZero (f a) := ⟨by rw [← ZeroHomClass.map_zero f]; exact hf.ne NeZero.out⟩

end

section

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem one_apply_eq_one_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [Nontrivial N₀]
    {x : M₀} :
    (1 : M₀ →*₀ N₀) x = 1 ↔ x ≠ 0 := by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [MonoidWithZeroHom.one_apply_of_ne_zero]

end

section

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem one_apply_eq_zero_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [Nontrivial N₀]
    {x : M₀} :
    (1 : M₀ →*₀ N₀) x = 0 ↔ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [MonoidWithZeroHom.one_apply_of_ne_zero]

end
