FAIL
import Mathlib

variable {G M A B α β : Type*}

variable [Monoid α] [MulAction α β]

theorem smul_bijective {m : α} (hm : IsUnit m) :
    Function.Bijective (fun (a : β) ↦ m • a) := by
  rcases hm with ⟨u, rfl⟩
  constructor
  · intro a b h
    have h' := congrArg (fun x => ↑u⁻¹ • x) h
    simpa only [smul_smul, Units.val_inv_eq_inv_val, Units.inv_mul, one_smul] using h'
  · intro b
    refine ⟨↑u⁻¹ • b, ?_⟩
    simpa only [smul_smul, Units.val_inv_eq_inv_val, Units.mul_inv, one_smul] using rfl
