import Mathlib

variable {G M A B α β : Type*}

variable [Monoid α] [MulAction α β]

theorem smul_bijective {m : α} (hm : IsUnit m) :
    Function.Bijective (fun (a : β) ↦ m • a) := by
  lift m to αˣ using hm
  exact MulAction.bijective m

