FAIL
import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {F : Type*}

variable [FunLike F A B] [AlgHomClass F R A B]

theorem ext_on_codisjoint {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T)
    (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) : φ = ψ := by
  apply DFunLike.ext
  intro x
  rw [← show ((⊤ : Subalgebra R A) : Set A) x ↔ x ∈ (S ⊔ T : Subalgebra R A) by
    rw [hST.sup_eq_top]]
  rw [Subalgebra.mem_toSubmodule] at *
  change x ∈ ((S : Submodule R A) ⊔ (T : Submodule R A)) at ‹x ∈ (S ⊔ T : Subalgebra R A)›
  rw [Submodule.mem_sup] at ‹x ∈ ((S : Submodule R A) ⊔ (T : Submodule R A))›
  rcases ‹x ∈ ((S : Submodule R A) ⊔ (T : Submodule R A))› with ⟨s, hs, t, ht, rfl⟩
  rw [map_add, hS hs, hT ht]
