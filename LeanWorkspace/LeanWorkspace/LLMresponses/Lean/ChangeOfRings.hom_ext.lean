FAIL
import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem hom_ext {M : ModuleCat R} {N : ModuleCat S}
    {α β : (ModuleCat.extendScalars f).obj M ⟶ N}
    (h : ∀ (m : M), α ((1 : S) ⊗ₜ m) = β ((1 : S) ⊗ₜ m)) : α = β := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
      simpa using h 0
  | tmul s m =>
      calc
        α (s ⊗ₜ m) = α (s • ((1 : S) ⊗ₜ m)) := by
          rw [← TensorProduct.smul_tmul', one_mul]
        _ = s • α ((1 : S) ⊗ₜ m) := by
          rw [map_smul]
        _ = s • β ((1 : S) ⊗ₜ m) := by rw [h m]
        _ = β (s • ((1 : S) ⊗ₜ m)) := by rw [map_smul]
        _ = β (s ⊗ₜ m) := by
          rw [← TensorProduct.smul_tmul', one_mul]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
