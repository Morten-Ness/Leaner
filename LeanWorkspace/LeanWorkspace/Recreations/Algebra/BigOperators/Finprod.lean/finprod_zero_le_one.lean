import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_zero_le_one {M α : Type*} [CommMonoidWithZero M] [PartialOrder M]
    [ZeroLEOneClass M] [PosMulMono M] :
    ∏ᶠ _ : α, (0 : M) ≤ 1 := by
  rw [← finprod_one (α := α)]
  by_cases H : (fun _ : α ↦ (0 : M)).HasFiniteMulSupport
  · exact finprod_le_finprod H (fun _ ↦ le_rfl) (by fun_prop) fun _ ↦ zero_le_one
  · rw [finprod_of_not_hasFiniteMulSupport H]
    exact finprod_one.symm.le

