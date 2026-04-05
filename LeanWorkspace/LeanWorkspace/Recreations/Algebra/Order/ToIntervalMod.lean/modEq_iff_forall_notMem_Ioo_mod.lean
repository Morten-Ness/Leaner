import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem modEq_iff_forall_notMem_Ioo_mod :
    a ≡ b [PMOD p] ↔ ∀ z : ℤ, b - z • p ∉ Set.Ioo a (a + p) := (AddCommGroup.tfae_modEq hp a b).out 0 1

