import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_const_div_Ico : (fun x => a / x) '' Ico b c = Ioc (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

